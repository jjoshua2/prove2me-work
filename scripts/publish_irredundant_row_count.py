#!/usr/bin/env python3
"""Register, prove, and mission-link the audited irredundant row-count theorem.

This is intentionally fail-closed. It pins the reviewed Prove2Me release and
Mathlib revision, collision-checks the theorem name/type, requires the exact
standalone proof hash, checks the Polynomial-Hirsch frontier before and after,
and writes durable JSON receipts without ever persisting credentials.
"""
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
SOURCE = "1ff86eb9c69679c6355c6fa968b6601482b046a1"
SOURCE_RUN = "34559027640"
FRONTIER = "73beca40-31bc-42d5-8350-5ec9ac28bd3e"
MISSION_NAME = "The Polynomial Hirsch Conjecture"
THEOREM_NAME = "Hirsch.irredundant_rows_card_le_any_equivalent_presentation"
SOLUTION = Path("Solutions/Sol_Hirsch_irredundant_rows_card_le_any_equivalent_presentation.lean")
SOLUTION_SHA256 = "33be3fdd17714bc1439b0bef73489c571ae41b14f5b06443c4ab6f85e905af55"
OUT = Path("irredundant_row_count_publication_receipts")

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_circuit_model
open scoped RealInnerProductSpace
open Hirsch"""

FORMAL = """namespace Hirsch
theorem irredundant_rows_card_le_any_equivalent_presentation
    {d n m : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : Fin m → EuclideanSpace ℝ (Fin d)) (β : Fin m → ℝ)
    (hirr : RowPresentationIrredundant a b)
    (hstrict : StrictlyFeasibleRows a b)
    (hP : Hpoly c β = Hpoly a b) : n ≤ m := by sorry
end Hirsch"""

NATURAL = """Let an n-row finite H-presentation be strictly feasible and irredundant, where irredundant means deleting any row strictly enlarges the feasible set. Then every equivalent finite H-presentation has at least n rows. The comparison presentation may use completely different normals and may contain redundant rows, duplicate rows, or zero-normal tautologies. Boundedness is not required."""

EXPLANATION = """For each indispensable source row i, interpolate between a common strictly feasible point and a witness that violates only row i. This produces a feasible point p_i at which row i is tight and every other source row is strict. In any equivalent finite presentation, some nonzero describing row must be tight at p_i: otherwise a sufficiently small displacement in the normal direction of the valid tight source inequality would remain feasible while violating that inequality. Choose one such comparison row f(i). If f(i)=f(k) for i≠k, then that nonzero comparison row is tight at the midpoint of p_i and p_k. But every source row is strict at that midpoint, hence every nonzero valid inequality is strict there, a contradiction. Thus f is injective and n≤m."""


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
            raise RuntimeError(
                f"platform version {self.version!r} differs from reviewed {VERSION!r}"
            )

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
        for name, value in [
            ("theorem_id", theorem_id),
            ("proof_type", "prove"),
            ("explanation", explanation),
        ]:
            parts.append(
                f"--{boundary}\r\n"
                f"Content-Disposition: form-data; name=\"{name}\"\r\n\r\n"
                f"{value}\r\n"
            )
        parts.append(
            f"--{boundary}\r\n"
            "Content-Disposition: form-data; name=\"file\"; filename=\"solution.lean\"\r\n"
            "Content-Type: text/plain\r\n\r\n"
            f"{proof}\r\n--{boundary}--\r\n"
        )
        return self.request(
            "/verify",
            "".join(parts).encode(),
            "POST",
            "multipart/form-data; boundary=" + boundary,
        )


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
    query = urllib.parse.urlencode(
        {"env": PIN, "theorem_name": THEOREM_NAME, "limit": 50, "offset": 0}
    )
    rows = api.request("/theorems?" + query).get("theorems", [])
    matches = [row for row in rows if row.get("theorem_name") == THEOREM_NAME]
    if len(matches) > 1:
        raise RuntimeError(f"ambiguous theorem name collision: {THEOREM_NAME}")
    if not matches:
        return None
    return api.request("/theorems/" + matches[0]["theorem_id"])


def register_or_reuse(api: API):
    theorem = existing_theorem(api)
    registration = "REUSED" if theorem else "PUBLISHED"
    if theorem is None:
        payload = {
            "env": PIN,
            "private": False,
            "problems": [
                {
                    "theorem_name": THEOREM_NAME,
                    "theorem_title": "Irredundant H-presentations are cardinal-minimal under strict feasibility",
                    "formal_statement": FORMAL,
                    "preamble": PREAMBLE,
                    "natural_language_statement": NATURAL,
                    "source": (
                        "https://github.com/jjoshua2/prove2me-work/commit/"
                        + SOURCE
                        + " ; standalone Lean/Axiom gate Actions run "
                        + SOURCE_RUN
                    ),
                    "tags": ["polyhedra", "formalization", "linear-programming"],
                }
            ],
        }
        save(OUT / "registration-request.json", payload)
        queued = api.request("/submit-problem", payload, "POST")
        save(OUT / "registration-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("registration did not queue exactly one theorem")
        job_id = queued["jobs"][0]["job_id"]
        verdict = poll(
            api,
            "/publish-jobs/" + job_id,
            {"PUBLISHED", "FAILED", "ERROR"},
            OUT / "registration-verdict.json",
            900,
        )
        if verdict.get("status") != "PUBLISHED":
            raise RuntimeError("theorem registration failed")
        theorem = api.request("/theorems/" + verdict["theorem_id"])
    save(OUT / "theorem-before-proof.json", theorem)
    if theorem.get("mathlib_rev") != PIN:
        raise RuntimeError("live theorem uses an unexpected Mathlib revision")
    if norm(theorem.get("formal_statement")) != norm(FORMAL):
        raise RuntimeError("live theorem formal statement differs from reviewed statement")
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
    verdict = poll(
        api,
        "/verify?" + urllib.parse.urlencode({"submission_id": submission_id}),
        {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"},
        OUT / "proof-verdict.json",
        1200,
    )
    final = api.request("/theorems/" + theorem["theorem_id"])
    save(OUT / "theorem-final.json", final)
    record.update(
        submission_id=submission_id,
        verdict=verdict.get("status"),
        status=final.get("status"),
    )
    save(OUT / "result.json", record)
    if record["verdict"] != "ACCEPTED" or record["status"] != "Proved":
        raise RuntimeError("proof did not receive ACCEPTED and live Proved")
    return record


def find_mission(api: API) -> dict:
    offset = 0
    matches: list[dict] = []
    while True:
        data = api.request(
            "/missions?" + urllib.parse.urlencode({"limit": 100, "offset": offset})
        )
        rows = data.get("missions", [])
        matches.extend(m for m in rows if m.get("name") == MISSION_NAME)
        offset += len(rows)
        total = int(data.get("total", offset))
        if offset >= total or not rows:
            break
    if len(matches) != 1:
        raise RuntimeError(f"expected one exact mission {MISSION_NAME!r}, found {len(matches)}")
    save(OUT / "mission.json", matches[0])
    return matches[0]


def link_mission(api: API, mission: dict, result: dict) -> dict:
    mission_id = mission["id"]
    theorem_id = result["theorem_id"]
    # Idempotence: if this theorem is already referenced in the mission thread,
    # preserve that comment rather than posting a duplicate on a rerun.
    existing = api.request(f"/missions/{mission_id}/comments?limit=100&offset=0")
    for comment in existing.get("comments", []):
        if any(
            ref.get("type") == "theorem" and ref.get("id") == theorem_id
            for ref in comment.get("references", [])
        ):
            save(OUT / "mission-comment.json", comment)
            return comment

    theorem_link = f"[row-count theorem](p2m:theorem/{theorem_id})"
    if result.get("submission_id"):
        solution_link = f"[accepted Lean solution](p2m:solution/{result['submission_id']})"
        proof_clause = f" with its {solution_link}"
    else:
        proof_clause = ""
    body = (
        "Published a representation-semantics result relevant to the current common-face "
        f"defect/excess program: {theorem_link}{proof_clause}. A strictly feasible, "
        "irredundant finite H-presentation is cardinal-minimal among all equivalent "
        "finite H-presentations, even if the comparison rows use different normals and "
        "contain redundancies or tautologies. This upgrades the least-row count from an "
        "original-subset notion toward a representation-independent row count. It does "
        "not identify an abstract geometric facet API and does not supply an edge-routing "
        "bound; the d≥4 polynomial edge-refinement child remains Open."
    )
    comment = api.request(
        f"/missions/{mission_id}/comments",
        {"body_md": body, "tags": ["reference"]},
        "POST",
    )
    save(OUT / "mission-comment.json", comment)
    refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
    if ("theorem", theorem_id) not in refs:
        raise RuntimeError("mission comment did not resolve the theorem reference")
    if result.get("submission_id") and ("solution", result["submission_id"]) not in refs:
        raise RuntimeError("mission comment did not resolve the solution reference")
    return comment


def main() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent")
    if not SOLUTION.is_file():
        raise RuntimeError("standalone solution file is missing")
    actual_sha = digest(SOLUTION)
    if actual_sha != SOLUTION_SHA256:
        raise RuntimeError(
            f"frozen proof hash mismatch: expected {SOLUTION_SHA256}, got {actual_sha}"
        )

    api = API(key)
    envs = api.request("/environments")
    save(OUT / "environments.json", envs)
    if not any(e.get("mathlib_rev") == PIN for e in envs.get("environments", [])):
        raise RuntimeError("pinned Mathlib environment unavailable")

    frontier_before = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-before.json", theorem_summary(frontier_before))
    if frontier_before.get("status") != "Open":
        raise RuntimeError("expected Polynomial-Hirsch edge-refinement frontier is not Open")

    theorem, registration = register_or_reuse(api)
    result = prove(api, theorem, registration)
    mission = find_mission(api)
    comment = link_mission(api, mission, result)

    frontier_after = api.request("/theorems/" + FRONTIER)
    save(OUT / "frontier-after.json", theorem_summary(frontier_after))
    if (
        frontier_after.get("theorem_id") != frontier_before.get("theorem_id")
        or frontier_after.get("status") != "Open"
    ):
        raise RuntimeError("Polynomial-Hirsch edge-refinement frontier changed unexpectedly")

    summary = {
        "source_commit": SOURCE,
        "source_run": SOURCE_RUN,
        "solution_sha256": SOLUTION_SHA256,
        "platform_version": api.version,
        "mathlib_rev": PIN,
        "result": result,
        "mission_id": mission["id"],
        "mission_name": mission["name"],
        "mission_comment_id": comment.get("id"),
        "frontier_before": theorem_summary(frontier_before),
        "frontier_after": theorem_summary(frontier_after),
        "frontier_graph_modified": False,
        "new_conjectural_children": 0,
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    }
    save(OUT / "summary.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
