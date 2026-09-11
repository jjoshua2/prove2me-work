#!/usr/bin/env python3
"""Register, prove, and mission-link the audited normalized two-moment theorem."""
from __future__ import annotations

import datetime
import hashlib
import json
import os
import re
import time
import urllib.parse
import urllib.request
import uuid
from pathlib import Path

BASE = "https://prove2.me/api/v1"
VERSION = "0.10.0"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE = "e9b89ee3f02fbaed5c379e35ef1c824ab3b85186"
SOURCE_RUN = "34605987684"
FRONTIER = "73beca40-31bc-42d5-8350-5ec9ac28bd3e"
MISSION_NAME = "The Polynomial Hirsch Conjecture"
THEOREM_NAME = "Hirsch.normalized_two_moment_slice_diameter_two"
SOLUTION = Path("/tmp/excess-two-public/solution.lean")
SOLUTION_SHA256 = "45e96aecc53c63bfd394ebc11a2ee196b958534cd93fe1f648c281dad8072317"
OUT = Path("excess_two_diameter_publication_receipts")

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch"""

FORMAL = """namespace Hirsch
theorem normalized_two_moment_slice_diameter_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) :
    DiamLE
      {s : EuclideanSpace ℝ (Fin n) |
        (∀ i, 0 ≤ s i) ∧
        (∑ i, s i) = 1 ∧
        (∑ i, t i * s i) = mu} 2 := by sorry
end Hirsch"""

NATURAL = """For arbitrary real moments t_i and target mu, consider the normalized nonnegative slice of the simplex defined by sum_i s_i = 1 and sum_i t_i s_i = mu. Its vertex-edge graph has padded diameter at most two. No distinctness or genericity assumption is made on the moments, so repeated moments, empty slices, singleton slices, and lower-dimensional cases are included."""

EXPLANATION = """Classify every extreme point. A vertex is either unit mass on a coordinate whose moment equals mu, or the unique two-coordinate convex combination supported on one index below mu and one above mu. Equal-moment singletons are mutually adjacent, and each is adjacent to every low/high pair point, by identifying the corresponding coordinate support face exactly with their segment. Two pair vertices sharing a low or high index are adjacent. For arbitrary pair endpoints p_ij and p_kl, use p_il as an intermediate vertex, yielding at most two edges/stays. The chosen intermediate introduces no coordinate that is zero at both endpoints. An explicit Nat-indexed padded walk then proves DiamLE 2."""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.version = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json", "Accept": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data["access_token"]
        self.version = data.get("version")
        if self.version != VERSION:
            raise RuntimeError(f"platform version {self.version!r} differs from reviewed {VERSION!r}")

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not path.startswith("/") or path.startswith("//") or "://" in path:
            raise ValueError("API-relative path required")
        if not self.token:
            self.refresh()
        if data is None:
            body = None
        elif isinstance(data, bytes):
            body = data
        else:
            body = json.dumps(data).encode()
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={
                "Authorization": "Bearer " + self.token,
                "Content-Type": content_type,
                "Accept": "application/json",
            },
            method=method,
        )
        with self.opener.open(req, timeout=120) as response:
            return json.load(response)

    def verify(self, theorem_id: str, proof: str, explanation: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        parts: list[str] = []
        for name, value in [("theorem_id", theorem_id), ("proof_type", "prove"),
                            ("explanation", explanation)]:
            parts.append(
                f"--{boundary}\r\nContent-Disposition: form-data; name=\"{name}\"\r\n\r\n"
                f"{value}\r\n"
            )
        parts.append(
            f"--{boundary}\r\nContent-Disposition: form-data; name=\"file\"; filename=\"solution.lean\"\r\n"
            f"Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n"
        )
        return self.request("/verify", "".join(parts).encode(), "POST",
                            "multipart/form-data; boundary=" + boundary)


def save(path: Path, data) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def norm(text: str | None) -> str:
    return re.sub(r"\s+", "", text or "")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_summary(t: dict) -> dict:
    return {k: t.get(k) for k in ("theorem_id", "theorem_name", "status", "mathlib_rev")}


def poll(api: API, path: str, terminal: set[str], receipt: Path, timeout: int):
    deadline = time.monotonic() + timeout
    while True:
        data = api.request(path)
        save(receipt, data)
        if data.get("status") in terminal:
            return data
        if time.monotonic() > deadline:
            raise TimeoutError(f"platform job still pending: {path}")
        time.sleep(5)


def existing_theorem(api: API):
    q = urllib.parse.urlencode({"env": PIN, "theorem_name": THEOREM_NAME, "limit": 50, "offset": 0})
    rows = api.request("/theorems?" + q).get("theorems", [])
    matches = [r for r in rows if r.get("theorem_name") == THEOREM_NAME]
    if len(matches) > 1:
        raise RuntimeError("ambiguous theorem-name collision")
    return api.request("/theorems/" + matches[0]["theorem_id"]) if matches else None


def register_or_reuse(api: API):
    theorem = existing_theorem(api)
    registration = "REUSED" if theorem else "PUBLISHED"
    if theorem is None:
        payload = {
            "env": PIN,
            "private": False,
            "problems": [{
                "theorem_name": THEOREM_NAME,
                "theorem_title": "Normalized two-moment slices have graph diameter at most two",
                "formal_statement": FORMAL,
                "preamble": PREAMBLE,
                "natural_language_statement": NATURAL,
                "source": (
                    "https://github.com/jjoshua2/prove2me-work/commit/" + SOURCE
                    + " ; standalone Lean/Axiom gate Actions run " + SOURCE_RUN
                ),
                "tags": ["polyhedra", "graph-diameter", "formalization"],
            }],
        }
        save(OUT / "registration-request.json", payload)
        queued = api.request("/submit-problem", payload, "POST")
        save(OUT / "registration-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("registration did not queue exactly one theorem")
        verdict = poll(api, "/publish-jobs/" + queued["jobs"][0]["job_id"],
                       {"PUBLISHED", "FAILED", "ERROR"},
                       OUT / "registration-verdict.json", 900)
        if verdict.get("status") != "PUBLISHED":
            raise RuntimeError("theorem registration failed")
        theorem = api.request("/theorems/" + verdict["theorem_id"])
    save(OUT / "theorem-before-proof.json", theorem)
    if theorem.get("mathlib_rev") != PIN:
        raise RuntimeError("live theorem Mathlib revision mismatch")
    if norm(theorem.get("formal_statement")) != norm(FORMAL):
        raise RuntimeError("live theorem formal statement mismatch")
    return theorem, registration


def prove(api: API, theorem: dict, registration: str) -> dict:
    record = {
        "theorem_name": THEOREM_NAME,
        "theorem_id": theorem["theorem_id"],
        "registration": registration,
        "solution_sha256": SOLUTION_SHA256,
    }
    if theorem.get("status") == "Proved":
        record.update(verdict="ALREADY_PROVED", status="Proved", submission_id=None)
        save(OUT / "result.json", record)
        return record
    if theorem.get("status") != "Open":
        raise RuntimeError("unexpected theorem status: " + str(theorem.get("status")))
    queued = api.verify(theorem["theorem_id"], SOLUTION.read_text(encoding="utf-8"), EXPLANATION)
    save(OUT / "proof-queued.json", queued)
    submission_id = queued["submission_id"]
    verdict = poll(api,
        "/verify?" + urllib.parse.urlencode({"submission_id": submission_id}),
        {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"},
        OUT / "proof-verdict.json", 1200)
    final = api.request("/theorems/" + theorem["theorem_id"])
    save(OUT / "theorem-final.json", final)
    record.update(submission_id=submission_id, verdict=verdict.get("status"), status=final.get("status"))
    save(OUT / "result.json", record)
    if record["verdict"] != "ACCEPTED" or record["status"] != "Proved":
        raise RuntimeError("proof did not receive ACCEPTED and live Proved")
    return record


def find_mission(api: API) -> dict:
    offset = 0
    matches: list[dict] = []
    while True:
        data = api.request("/missions?" + urllib.parse.urlencode({"limit": 100, "offset": offset}))
        rows = data.get("missions", [])
        matches.extend(m for m in rows if m.get("name") == MISSION_NAME)
        offset += len(rows)
        if offset >= int(data.get("total", offset)) or not rows:
            break
    if len(matches) != 1:
        raise RuntimeError(f"expected one exact mission, found {len(matches)}")
    save(OUT / "mission.json", matches[0])
    return matches[0]


def link_mission(api: API, mission: dict, result: dict) -> dict:
    mission_id = mission["id"]
    theorem_id = result["theorem_id"]
    existing = api.request(f"/missions/{mission_id}/comments?limit=100&offset=0")
    for comment in existing.get("comments", []):
        if any(r.get("type") == "theorem" and r.get("id") == theorem_id
               for r in comment.get("references", [])):
            save(OUT / "mission-comment.json", comment)
            return comment
    theorem_link = f"[normalized excess-two diameter theorem](p2m:theorem/{theorem_id})"
    proof_clause = ""
    if result.get("submission_id"):
        proof_clause = f" with its [accepted Lean solution](p2m:solution/{result['submission_id']})"
    body = (
        f"Published {theorem_link}{proof_clause}: every normalized nonnegative two-moment "
        "slice of the simplex has padded graph diameter at most two, with repeated moments "
        "and degenerate slices included. The internal proof also chooses the two-step "
        "intermediate vertex without introducing any coordinate zero at both endpoints. "
        "This closes the normalized excess-two base case, but it does NOT assert that an "
        "arbitrary circuit carrier is such a rank-two slice. The separate slack-normalization/"
        "affine-transport bridge is still needed, and the d≥4 polynomial edge-refinement "
        "frontier remains Open."
    )
    comment = api.request(f"/missions/{mission_id}/comments",
                          {"body_md": body, "tags": ["reference"]}, "POST")
    save(OUT / "mission-comment.json", comment)
    refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
    if ("theorem", theorem_id) not in refs:
        raise RuntimeError("mission comment did not resolve theorem reference")
    if result.get("submission_id") and ("solution", result["submission_id"]) not in refs:
        raise RuntimeError("mission comment did not resolve solution reference")
    return comment


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent")
    if not SOLUTION.is_file() or digest(SOLUTION) != SOLUTION_SHA256:
        raise RuntimeError("frozen standalone proof is absent or has wrong SHA-256")
    api = API(key)
    envs = api.request("/environments")
    save(OUT / "environments.json", envs)
    if not any(e.get("mathlib_rev") == PIN for e in envs.get("environments", [])):
        raise RuntimeError("pinned Mathlib environment unavailable")
    before = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-before.json", theorem_summary(before))
    if before.get("status") != "Open":
        raise RuntimeError("Polynomial-Hirsch edge-refinement frontier is not Open")
    theorem, registration = register_or_reuse(api)
    result = prove(api, theorem, registration)
    mission = find_mission(api)
    comment = link_mission(api, mission, result)
    after = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-after.json", theorem_summary(after))
    if after.get("theorem_id") != before.get("theorem_id") or after.get("status") != "Open":
        raise RuntimeError("Polynomial-Hirsch frontier changed unexpectedly")
    receipt = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "platform_version": api.version,
        "mathlib_rev": PIN,
        "source_commit": SOURCE,
        "source_run": SOURCE_RUN,
        "solution_sha256": SOLUTION_SHA256,
        "result": result,
        "mission_id": mission["id"],
        "mission_name": mission["name"],
        "mission_comment_id": comment["id"],
        "frontier_before": theorem_summary(before),
        "frontier_after": theorem_summary(after),
        "frontier_graph_modified": False,
        "new_conjectural_children": 0,
    }
    save(OUT / "receipt.json", receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
