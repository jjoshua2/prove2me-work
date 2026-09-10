#!/usr/bin/env python3
"""Submit the audited Child-B reduction to the existing balanced core.

The caller must verify that the exact solution file still has the Git blob
hash from the successful pinned Lean CI run. This script never prints API keys
or bearer tokens.
"""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import time
import urllib.parse
import urllib.request
import uuid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "child_b_balanced_evidence"
PROOF = ROOT / "Solutions" / "Sol_Hirsch_polynomial_edge_refinement_via_balanced.lean"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGET_NAME = "Hirsch.polynomial_edge_refinement_of_circuit_walks"
TRANSFER_NAME = "Hirsch.balanced_hpoly_transfer"
BALANCED_NAME = "Hirsch.balanced_polynomial_bound"
PARENT_ID = "33fc334e-e05b-4090-ac49-f83fd94d9305"

EXPLANATION = r"""We reduce the circuit-to-edge refinement claim to the existing balanced polynomial-diameter core.

Assume `Hirsch.balanced_polynomial_bound`: there are constants $C,k$ such that every bounded nonempty $D$-dimensional H-polytope with exactly $2D$ rows has graph diameter at most $C D^k$. We also use the already proved `Hirsch.balanced_hpoly_transfer`, which sends any bounded nonempty $d$-dimensional $n$-row H-polytope to such a balanced polytope of dimension

$$D=d+(n-2d)\le n+d,$$

and transfers every edge-diameter bound back to the original polytope.

Fix the data in the edge-refinement theorem and a length-$L$ circuit walk from vertices $u$ to $v$. If $L=0$, the circuit-walk endpoint equations imply $u=v$, so the constant stationary walk has the required zero budget.

If $L>0$, the circuit intermediates are unnecessary. The endpoint $u$ makes the original polytope nonempty. Apply the balanced transfer, then the balanced polynomial bound, and transfer the resulting graph walk back. Its length is

$$C D^k \le C(n+d)^k \le C(n+d)^k L.$$

The last inequality uses $L\ge1$. Stationary padding extends the transferred edge walk to exactly $C(n+d)^kL$ steps. Thus the same constants $C,k$ satisfy the full circuit-to-edge statement. The irredundancy and strict-feasibility hypotheses are not needed by this reduction.

Consequently the only open mathematical input of this sketch is the pre-existing balanced polynomial-diameter theorem; no new conjectural child is introduced."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0
        self.version = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode("utf-8"),
            headers={"Content-Type": "application/json", "Accept": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))
        self.version = data.get("version")

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not path.startswith("/") or path.startswith("//"):
            raise ValueError("relative API path required")
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode("utf-8") if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={
                "Authorization": "Bearer " + self.token,
                "Content-Type": content_type,
                "Accept": "application/json",
                "User-Agent": "prove2me-child-b-balanced-submit/1",
            },
            method=method,
        )
        with self.opener.open(req, timeout=75) as response:
            return json.load(response)

    def verify(self, theorem_id: str, proof: str, explanation: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        parts: list[str] = []
        for name, value in [
            ("theorem_id", theorem_id),
            ("proof_type", "prove"),
            ("explanation", explanation),
        ]:
            parts.append(
                f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n'
            )
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
            f'Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n'
        )
        return self.request(
            "/verify",
            "".join(parts).encode("utf-8"),
            "POST",
            "multipart/form-data; boundary=" + boundary,
        )


def write(name: str, obj) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def rows(api: API, theorem_name: str):
    query = urllib.parse.urlencode({
        "env": PIN,
        "theorem_name": theorem_name,
        "limit": 20,
        "offset": 0,
    })
    data = api.request("/theorems?" + query)
    return data.get("theorems", [])


def unique(api: API, name: str):
    matches = rows(api, name)
    exact = [x for x in matches if x.get("theorem_name") == name and x.get("mathlib_rev") == PIN]
    if len(exact) != 1:
        raise RuntimeError(f"expected one pinned theorem named {name}, found {len(exact)}")
    return api.request("/theorems/" + exact[0]["theorem_id"])


def safe(api: API, path: str):
    try:
        return api.request(path)
    except Exception as exc:
        return {"error_type": type(exc).__name__, "error": str(exc)[:500], "path": path}


def wait_verdict(api: API, submission_id: str, timeout: int = 900):
    end = time.monotonic() + timeout
    terminal = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
    while True:
        state = api.request("/verify?" + urllib.parse.urlencode({"submission_id": submission_id}))
        write("verify-status.json", state)
        if state.get("status") in terminal:
            return state
        if time.monotonic() >= end:
            return state
        time.sleep(8)


def summary_row(item):
    return {k: item.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev")}


def main() -> int:
    if not PROOF.is_file():
        raise RuntimeError("audited Child-B proof file missing")
    proof = PROOF.read_text()
    if "theorem solution" not in proof:
        raise RuntimeError("proof file does not contain theorem solution")
    if TARGET_NAME in proof:
        raise RuntimeError("proof text unexpectedly mentions/imports its own target theorem")

    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)

    target = unique(api, TARGET_NAME)
    transfer = unique(api, TRANSFER_NAME)
    balanced = unique(api, BALANCED_NAME)
    write("pre-submit-frontier.json", {
        "platform_version": api.version,
        "target": summary_row(target),
        "transfer": summary_row(transfer),
        "balanced": summary_row(balanced),
    })

    if target.get("mathlib_rev") != PIN or transfer.get("mathlib_rev") != PIN or balanced.get("mathlib_rev") != PIN:
        raise RuntimeError("environment mismatch")
    if transfer.get("status") != "Proved":
        raise RuntimeError("balanced transfer is no longer Proved")
    if balanced.get("status") not in {"Open", "Proved"}:
        raise RuntimeError("unexpected balanced core status")

    # If a concurrent solver has already closed Child B, do not resubmit.
    if target.get("status") == "Proved":
        result = {
            "already_proved": target.get("theorem_id"),
            "target": summary_row(target),
            "balanced": summary_row(balanced),
            "platform_version": api.version,
        }
        write("result.json", result)
        print(json.dumps(result, indent=2))
        return 0
    if target.get("status") != "Open":
        raise RuntimeError("unexpected target status: " + repr(target.get("status")))

    queued = api.verify(target["theorem_id"], proof, EXPLANATION)
    write("submitted.json", queued)
    sid = queued["submission_id"]
    verdict = wait_verdict(api, sid)

    target_after = api.request("/theorems/" + target["theorem_id"])
    target_open = safe(api, "/theorems/" + target["theorem_id"] + "/open-leaves")
    target_decomp = safe(api, "/theorems/" + target["theorem_id"] + "/decompositions")
    parent = safe(api, "/theorems/" + PARENT_ID)
    parent_open = safe(api, "/theorems/" + PARENT_ID + "/open-leaves")
    balanced_after = api.request("/theorems/" + balanced["theorem_id"])

    write("target-after.json", target_after)
    write("target-open-leaves.json", target_open)
    write("target-decompositions.json", target_decomp)
    write("parent-after.json", parent)
    write("parent-open-leaves.json", parent_open)
    write("balanced-after.json", balanced_after)

    result = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "submission_id": sid,
        "verdict": verdict.get("status"),
        "target": summary_row(target_after),
        "balanced": summary_row(balanced_after),
        "parent": summary_row(parent) if isinstance(parent, dict) else parent,
        "target_open_leaves": target_open,
        "parent_open_leaves": parent_open,
        "platform_version": api.version,
    }
    write("result.json", result)
    print(json.dumps(result, indent=2))

    if verdict.get("status") not in {"SKETCH_ACCEPTED", "ACCEPTED"}:
        return 2
    if balanced_after.get("status") == "Open":
        leaves = target_open.get("open_leaves", []) if isinstance(target_open, dict) else []
        if not any(x.get("theorem_id") == balanced_after.get("theorem_id") for x in leaves if isinstance(x, dict)):
            raise RuntimeError("accepted sketch did not expose balanced core as an open leaf")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        write("submission-failure.json", {"type": type(exc).__name__, "message": str(exc)[:1000]})
        print(json.dumps({"error": type(exc).__name__, "message": str(exc)[:600]}))
        raise SystemExit(2)
