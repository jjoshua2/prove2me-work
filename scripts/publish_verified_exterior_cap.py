#!/usr/bin/env python3
"""Publish the already-audited PR #52 exterior-cap proof to Prove2Me.

This script intentionally does *not* run Lean.  It accepts only the immutable
GitHub Actions artifact produced by run 34412248641, validates its audit record
and hashes, then performs the authenticated Prove2Me registration/verification
calls.  It is safe to re-run: an identical existing theorem is reused and a
Proved theorem is not resubmitted.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.parse
import urllib.request
import uuid

BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
LEAN = "leanprover/lean4:v4.30.0"
SOURCE_COMMIT = "5d57b93dc40d0f0917dcc99ce7a80274890c5c54"
SOURCE_RUN = "34412248641"
EXPECTED_SOLUTION_SHA256 = "386d8c27c5c0b4926ee009095ef2e726451aba86ad3ff5140c7bf30a744a592e"
NAME = "Hirsch.simultaneous_clip_diameter_of_exterior_cap"
SHORT_NAME = "simultaneous_clip_diameter_of_exterior_cap"

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
"""

TITLE = "Exterior-cap witness bound for simultaneous clipping"
NATURAL = (
    "Let R be a compact convex parent with a convex exterior-cap region G and a set V of old "
    "vertices. Assume every pair of vertices in V has a padded parent-edge route of length D, "
    "and every extreme point of R is either in V or is a cap vertex in G adjacent to some old "
    "vertex. If one point o in R strictly satisfies every added cut, G lies outside the final "
    "clip, and each final cut face i has intrinsic diameter at most B_i, then the final clipped "
    "polytope has padded graph diameter at most D + 1 + sum_i B_i. The theorem deliberately "
    "assumes the exterior-cap witness/classification; it does not formalize existence of such a "
    "cap for every pointed H-polyhedron."
)
EXPLANATION = (
    "The exterior-cap classification gives a route of length at most D+1 between any two parent "
    "vertices when cap-to-cap motion is allowed inside G: old/old uses the supplied D-step route, "
    "mixed pairs add one cap adjacency, and cap/cap pairs use the convex exterior cap. The radial "
    "clipping construction from the strict common centre maps the exterior portions into final cut "
    "faces. The verified clipping route theorem replaces those portions by final-parent routes, "
    "charging each final cut face at most its supplied intrinsic budget B_i. Hence the final padded "
    "diameter is D + 1 + sum_i B_i."
)
TAGS = ["polyhedra", "hirsch-conjecture", "graph-diameter", "clipping", "path-repair"]


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as r:
            data = json.load(r)
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type},
            method=method,
        )
        with self.opener.open(req, timeout=90) as r:
            return json.load(r)

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
            "".join(parts).encode(),
            "POST",
            "multipart/form-data; boundary=" + boundary,
        )


def norm(text: str | None) -> str:
    return re.sub(r"\s+", "", text or "")


def save(out: Path, name: str, obj) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out / name).write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def locate_packet(root: Path) -> Path:
    candidates: list[Path] = []
    for manifest_path in root.rglob("manifest.json"):
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except Exception:
            continue
        if data.get("proposed_theorem_name") == NAME:
            candidates.append(manifest_path.parent)
    if len(candidates) != 1:
        raise RuntimeError(f"expected exactly one verified exterior-cap packet, found {len(candidates)}")
    return candidates[0]


def validate_packet(packet: Path) -> tuple[dict, dict, str]:
    manifest = json.loads((packet / "manifest.json").read_text(encoding="utf-8"))
    verification = json.loads((packet / "verification.json").read_text(encoding="utf-8"))
    solution = (packet / "solution.lean").read_text(encoding="utf-8")
    digest = hashlib.sha256(solution.encode()).hexdigest()

    checks = {
        "mathlib_rev": manifest.get("mathlib_rev") == PIN,
        "lean_toolchain": manifest.get("lean_toolchain") == LEAN,
        "source_commit": manifest.get("source_commit") == SOURCE_COMMIT,
        "proposed_theorem_name": manifest.get("proposed_theorem_name") == NAME,
        "formal_scope": manifest.get("formal_scope") == "EXTERIOR_CAP_WITNESS_WITH_STRICT_CENTRE_NOT_GENERAL_POINTED_HPOLY",
        "manifest_solution_hash": manifest.get("solution_sha256") == EXPECTED_SOLUTION_SHA256,
        "actual_solution_hash": digest == EXPECTED_SOLUTION_SHA256,
        "verification_source_commit": verification.get("source_commit") == SOURCE_COMMIT,
        "verification_run": str(verification.get("run_id")) == SOURCE_RUN,
        "source_and_standalone_compilation": verification.get("source_and_standalone_compilation") == "PASSED",
        "standard_axiom_audits": verification.get("standard_axiom_audits") == "PASSED",
        "regression_hashes": verification.get("both_exact_regression_hashes") == "MATCHED",
        "not_previously_submitted_by_artifact": verification.get("publication") == "NOT_SUBMITTED",
    }
    failed = [name for name, ok in checks.items() if not ok]
    if failed:
        raise RuntimeError("verified packet validation failed: " + ", ".join(failed))
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", solution, re.M):
        raise RuntimeError("standalone proof contains a forbidden admission/unchecked declaration")
    return manifest, verification, solution


def formal_statement(manifest: dict) -> str:
    theorem_type = manifest["theorem_type"]
    if not theorem_type.startswith("theorem solution"):
        raise RuntimeError("unexpected theorem_type in verified manifest")
    typed = theorem_type.replace("theorem solution", f"theorem {SHORT_NAME}", 1)
    return f"namespace Hirsch\n\n{typed} := by sorry\n\nend Hirsch"


def theorem_rows(api: API):
    q = urllib.parse.urlencode({"env": PIN, "theorem_name": NAME, "limit": 20, "offset": 0})
    return [x for x in api.request("/theorems?" + q).get("theorems", []) if x.get("theorem_name") == NAME]


def wait_publish(api: API, job_id: str, timeout: int = 180):
    end = time.monotonic() + timeout
    while True:
        result = api.request("/publish-jobs/" + job_id)
        if result.get("status") in {"PUBLISHED", "FAILED", "ERROR"}:
            return result
        if time.monotonic() >= end:
            raise TimeoutError(f"publication job {job_id} did not finish within {timeout}s")
        time.sleep(4)


def wait_verdict(api: API, submission_id: str, timeout: int = 480):
    end = time.monotonic() + timeout
    terminal = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
    while True:
        result = api.request("/verify?" + urllib.parse.urlencode({"submission_id": submission_id}))
        if result.get("status") in terminal:
            return result
        if time.monotonic() >= end:
            raise TimeoutError(f"verification {submission_id} did not finish within {timeout}s")
        time.sleep(4)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--artifact-root", type=Path, required=True)
    parser.add_argument("--out", type=Path, default=Path("prove2me_exterior_cap_receipts"))
    args = parser.parse_args()

    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("PROVE2ME_API_KEY unavailable")

    packet = locate_packet(args.artifact_root)
    manifest, verification, solution = validate_packet(packet)
    formal = formal_statement(manifest)
    out = args.out
    summary = {
        "started_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "source_commit": SOURCE_COMMIT,
        "source_run": SOURCE_RUN,
        "solution_sha256": EXPECTED_SOLUTION_SHA256,
        "theorem_name": NAME,
        "artifact_validation": "PASSED",
    }
    save(out, "validated-artifact.json", {"manifest": manifest, "verification": verification})

    api = API(key)
    rows = theorem_rows(api)
    if rows:
        if len(rows) != 1:
            raise RuntimeError(f"theorem-name collision: found {len(rows)} rows")
        theorem = api.request("/theorems/" + rows[0]["theorem_id"])
        if norm(theorem.get("formal_statement")) != norm(formal):
            raise RuntimeError("existing Prove2Me theorem with this name has a different formal statement")
        theorem_id = theorem["theorem_id"]
        summary["registration"] = "REUSED"
    else:
        queued = api.request(
            "/submit-problem",
            {
                "env": PIN,
                "private": False,
                "problems": [
                    {
                        "theorem_name": NAME,
                        "theorem_title": TITLE,
                        "formal_statement": formal,
                        "natural_language_statement": NATURAL,
                        "preamble": PREAMBLE,
                        "source": "Kernel- and standalone-verified theorem from jjoshua2/prove2me-work PR #52, source commit " + SOURCE_COMMIT + ".",
                        "tags": TAGS,
                    }
                ],
            },
            "POST",
        )
        save(out, "problem-queued.json", queued)
        if queued.get("errors") or len(queued.get("jobs", [])) != 1:
            raise RuntimeError("Prove2Me theorem publication did not queue exactly one job")
        job = wait_publish(api, queued["jobs"][0]["job_id"])
        save(out, "problem-job.json", job)
        if job.get("status") != "PUBLISHED":
            raise RuntimeError(f"theorem publication failed: {job.get('status')}")
        theorem_id = job["theorem_id"]
        summary["registration"] = "PUBLISHED"

    summary["theorem_id"] = theorem_id
    theorem = api.request("/theorems/" + theorem_id)
    save(out, "theorem-before-verify.json", theorem)
    if theorem.get("status") == "Proved":
        summary.update(status="Proved", verification="SKIPPED_ALREADY_PROVED")
        save(out, "status.json", summary)
        print(json.dumps(summary, indent=2))
        return 0
    if theorem.get("status") != "Open":
        raise RuntimeError(f"unexpected theorem status before verification: {theorem.get('status')}")

    queued = api.verify(theorem_id, solution, EXPLANATION)
    save(out, "proof-queued.json", queued)
    submission_id = queued.get("submission_id")
    if not submission_id:
        raise RuntimeError("Prove2Me verification response did not include submission_id")
    summary["submission_id"] = submission_id

    verdict = wait_verdict(api, submission_id)
    save(out, "proof-verdict.json", verdict)
    final_theorem = api.request("/theorems/" + theorem_id)
    save(out, "theorem-final.json", final_theorem)
    summary["verdict"] = verdict.get("status")
    summary["status"] = final_theorem.get("status")
    save(out, "status.json", summary)
    print(json.dumps(summary, indent=2))
    if summary["verdict"] != "ACCEPTED" or summary["status"] != "Proved":
        raise RuntimeError(f"Prove2Me did not accept proof: verdict={summary['verdict']} status={summary['status']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        out = Path("prove2me_exterior_cap_receipts")
        save(out, "failure.json", {"error_type": type(exc).__name__, "error": str(exc)[:1000]})
        raise
