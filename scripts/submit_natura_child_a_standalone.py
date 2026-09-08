#!/usr/bin/env python3
"""Self-contained Prove2Me submission client for the audited Child-A proof.

The caller must regenerate `child_a_direct_evidence/solution.lean` from the
pinned source commit and verify its SHA-256 against the successful independent
Lean audit before invoking this script. This script itself performs no source
transformation and never prints credentials or bearer tokens.
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
OUT = ROOT / "child_a_direct_evidence"
PROOF = OUT / "solution.lean"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGET_ID = "9b9a6f06-d05d-41ba-980f-04b905e67562"
TARGET_NAME = "Hirsch.cubic_circuit_walk_bound"

EXPLANATION = r"""Constructive proof with explicit constant C=17.

The proof first replaces the bounded H-presentation by an irredundant strictly feasible subpresentation of the same polytope. Boundedness makes the row-evaluation map injective, so slack coordinates identify row-circuit steps and walks with maximal elementary augmentations in a nonnegative affine slice.

For the matrix-free slice, recenter at the target vertex. Every displacement admits an exact conformal decomposition into at most n support-minimal elementary directions. A phase records coordinates that have made permanent progress: target-zero coordinates already at zero and target-positive coordinates already below M v_i, where M=max(2,n). The phase reference is reset after every strict progress event; this support-safe reset prevents a coordinate that became zero from later blocking a positive augmentation.

Within a phase, a potential over the live target-zero coordinates contracts by at least 1-1/M at each maximal norm step. After at most 4 M^2 such steps without an event, it is at most 1/(2 M^2). A support-safe elimination displacement then has a conformal elementary component whose positive maximal augmentation creates a new permanent progress event, while the scalar inequalities preserve all previously trapped coordinates.

Thus each phase uses at most 4 M^2+1 maximal circuit steps and either reaches the target or strictly enlarges a subset of the n coordinates. There are at most n phases, and n(4 M^2+1) <= 17 n^3. Recentring and the slack/row-walk equivalence transfer the route back to the irredundant H-presentation; stationary padding yields the required 17 (m+d)^3 budget."""


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
                "User-Agent": "prove2me-child-a-submit/1",
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


def main() -> int:
    if not PROOF.exists():
        raise RuntimeError("audited flattened proof file is missing")
    proof = PROOF.read_text()
    if "theorem solution" not in proof:
        raise RuntimeError("flattened file does not contain theorem solution")
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api = API(key)
    target = api.request("/theorems/" + TARGET_ID)
    write("live-target.json", {k: target.get(k) for k in
          ("theorem_id", "theorem_name", "status", "mathlib_rev", "formal_statement")})
    if target.get("theorem_name") != TARGET_NAME:
        raise RuntimeError("target theorem name changed")
    if target.get("mathlib_rev") != PIN:
        raise RuntimeError("target Lean environment changed")
    if target.get("status") == "Proved":
        result = {"already_proved": TARGET_ID, "platform_version": api.version}
        write("result.json", result)
        print(json.dumps(result))
        return 0
    if target.get("status") != "Open":
        raise RuntimeError("unexpected target status: " + repr(target.get("status")))

    queued = api.verify(TARGET_ID, proof, EXPLANATION)
    write("submitted.json", queued)
    sid = queued["submission_id"]
    verdict = wait_verdict(api, sid)
    final = api.request("/theorems/" + TARGET_ID)
    result = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "theorem_id": TARGET_ID,
        "submission_id": sid,
        "verdict": verdict.get("status"),
        "theorem_status": final.get("status"),
        "platform_version": api.version,
    }
    write("result.json", result)
    print(json.dumps(result, indent=2))
    return 0 if verdict.get("status") == "ACCEPTED" and final.get("status") == "Proved" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        write("submission-failure.json", {"type": type(exc).__name__, "message": str(exc)[:1000]})
        print(json.dumps({"error": type(exc).__name__, "message": str(exc)[:600]}))
        raise SystemExit(2)
