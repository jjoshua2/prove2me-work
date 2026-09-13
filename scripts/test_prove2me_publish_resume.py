#!/usr/bin/env python3
"""Focused tests for durable Prove2Me problem-registration retries."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import prove2me_comment_publish as pub


REV = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PROBLEM = {
    "theorem_name": "Demo.pending_registration",
    "formal_statement": "theorem Demo.pending_registration : True := by sorry",
    "env": REV,
}


class FakeAPI:
    def __init__(self, jobs: list[dict], latest: dict | None = None):
        self.jobs = jobs
        self.latest = latest or {}
        self.calls: list[tuple[str, str]] = []
        self.submits = 0

    def request(self, path: str, payload=None, method: str = "GET"):
        self.calls.append((method, path))
        if path.startswith("/theorems?"):
            return {"theorems": [], "total": 0}
        if path.startswith("/publish-jobs?"):
            return {"jobs": self.jobs}
        if path.startswith("/publish-jobs/"):
            return dict(self.latest)
        if path == "/submit-problem" and method == "POST":
            self.submits += 1
            return {"job_id": "new-job"}
        if path == "/theorems/thm-1":
            return {"theorem_id": "thm-1", "status": "Proved"}
        raise AssertionError(f"unexpected API request: {method} {path}")


class PublishJobRecoveryTests(unittest.TestCase):
    def exact_job(self, *, job_id: str = "job-1", status: str = "PENDING") -> dict:
        return {
            "id": job_id,
            "kind": "problem",
            "theorem_name": PROBLEM["theorem_name"],
            "formal_statement": PROBLEM["formal_statement"],
            "env": REV,
            "status": status,
        }

    def test_matching_jobs_require_available_disambiguators_to_agree(self) -> None:
        exact = self.exact_job()
        wrong_statement = {**exact, "id": "wrong-statement", "formal_statement": "theorem X : True := by sorry"}
        wrong_env = {**exact, "id": "wrong-env", "env": "other"}
        name_only = {
            "id": "name-only",
            "theorem_name": PROBLEM["theorem_name"],
            "status": "PENDING",
        }
        api = FakeAPI([wrong_statement, wrong_env, name_only, exact])
        self.assertEqual(pub.matching_publish_jobs(api, PROBLEM, REV), [exact])

    def test_multiple_exact_active_jobs_are_refused(self) -> None:
        api = FakeAPI([self.exact_job(job_id="job-1"), self.exact_job(job_id="job-2")])
        with self.assertRaises(RuntimeError):
            pub.recover_publish_job(api, PROBLEM, REV)

    def test_publish_packet_resumes_existing_job_without_resubmit(self) -> None:
        active = self.exact_job()
        api = FakeAPI([active], latest={"id": "job-1", "status": "PUBLISHED", "theorem_id": "thm-1"})
        with tempfile.TemporaryDirectory() as tmp:
            packet = Path(tmp) / "packet"
            packet.mkdir()
            (packet / "problem.json").write_text(json.dumps(PROBLEM), encoding="utf-8")
            with patch.object(pub, "validate_artifact_packet", return_value={"publishable": True, "mathlib_rev": REV}), \
                 patch.object(pub, "wait_until", return_value={"id": "job-1", "status": "PUBLISHED", "theorem_id": "thm-1"}):
                result = pub.publish_packet(api, packet)
        self.assertEqual(api.submits, 0)
        self.assertEqual(result["registration"], "RESUMED_PUBLISHED")
        self.assertEqual(result["status"], "SKIPPED_ALREADY_PROVED")

    def test_timeout_returns_durable_pending_receipt_without_resubmit(self) -> None:
        active = self.exact_job()
        api = FakeAPI([active], latest=active)
        with tempfile.TemporaryDirectory() as tmp:
            packet = Path(tmp) / "packet"
            packet.mkdir()
            (packet / "problem.json").write_text(json.dumps(PROBLEM), encoding="utf-8")
            with patch.object(pub, "validate_artifact_packet", return_value={"publishable": True, "mathlib_rev": REV}), \
                 patch.object(pub, "wait_until", side_effect=TimeoutError):
                result = pub.publish_packet(api, packet, timeout=1)
        self.assertEqual(api.submits, 0)
        self.assertEqual(result["status"], "PUBLISH_PENDING")
        self.assertEqual(result["publish_job_id"], "job-1")
        self.assertEqual(result["registration"], "RESUMED")


if __name__ == "__main__":
    raise SystemExit(unittest.main())
