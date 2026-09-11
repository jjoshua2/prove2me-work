#!/usr/bin/env python3
"""Recover the exact rank-selected Prove2Me submission interrupted by CI timeout.

This script is deliberately read-only with respect to Prove2Me: it never calls
/verify or /submit-problem.  If the known submission is still pending, poll it;
if it is accepted and the theorem reads back Proved, continue.  Any other
terminal state stops the publication workflow so the generic publisher cannot
blindly create a duplicate submission.
"""
from __future__ import annotations

import hashlib
import json
import os
import urllib.parse
from pathlib import Path

from publish_face_cover_certificates import API, PIN, poll, save

THEOREM_ID = "76cdff62-bb43-4758-a1ed-980ce0ec5230"
SUBMISSION_ID = "c227d208-25c5-48b1-b49b-e94788770bf1"
EXPECTED_SOLUTION_SHA256 = "046c0e776884c926f6eb86210798c582e50e7950e75a8b11493eaa3008badd3f"
TERMINAL = {"ACCEPTED", "SKETCH_ACCEPTED", "CE", "WA", "SORRY", "FAILED", "ERROR"}
OUT = Path("face_cover_publication_receipts/rank_selected_recovery")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    proof = Path("face_cover_publication_packet/rank_selected.lean")
    got = digest(proof)
    if got != EXPECTED_SOLUTION_SHA256:
        raise RuntimeError(
            "rank-selected proof bytes differ from the interrupted audited submission: " + got
        )

    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key:
        raise RuntimeError("repository publication credential is not present")
    api = API(key)

    theorem = api.request("/theorems/" + THEOREM_ID)
    save(OUT, "theorem-before-recovery.json", theorem)
    if theorem.get("mathlib_rev") != PIN:
        raise RuntimeError("rank-selected theorem environment changed")
    if theorem.get("status") == "Proved":
        result = {
            "theorem_id": THEOREM_ID,
            "submission_id": SUBMISSION_ID,
            "solution_sha256": got,
            "verdict": "THEOREM_ALREADY_PROVED",
            "status": "Proved",
            "new_submission": False,
        }
        save(OUT, "result.json", result)
        print(json.dumps(result), flush=True)
        return
    if theorem.get("status") != "Open":
        raise RuntimeError("unexpected rank-selected theorem status: " + str(theorem.get("status")))

    status = api.request(
        "/verify?" + urllib.parse.urlencode({"submission_id": SUBMISSION_ID})
    )
    save(OUT, "submission-first-read.json", status)
    if status.get("theorem_id") != THEOREM_ID:
        raise RuntimeError("known submission points at a different theorem")
    if status.get("status") not in TERMINAL:
        status = poll(
            api,
            "/verify?" + urllib.parse.urlencode({"submission_id": SUBMISSION_ID}),
            TERMINAL,
            OUT,
            "submission-final-read.json",
            900,
        )

    final = api.request("/theorems/" + THEOREM_ID)
    save(OUT, "theorem-after-recovery.json", final)
    result = {
        "theorem_id": THEOREM_ID,
        "submission_id": SUBMISSION_ID,
        "solution_sha256": got,
        "verdict": status.get("status"),
        "status": final.get("status"),
        "new_submission": False,
    }
    save(OUT, "result.json", result)
    print(json.dumps(result), flush=True)
    if result["verdict"] != "ACCEPTED" or result["status"] != "Proved":
        raise RuntimeError(
            "interrupted rank-selected submission is terminal but not ACCEPTED+Proved; refusing duplicate submission"
        )


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        save(OUT, "failure.json", {"type": type(exc).__name__, "message": str(exc)[:500]})
        print(json.dumps({"type": type(exc).__name__, "message": str(exc)[:500]}), flush=True)
        raise SystemExit(2)
