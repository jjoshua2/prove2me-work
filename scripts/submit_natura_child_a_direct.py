#!/usr/bin/env python3
"""Submit the already-flattened, locally audited direct Child-A proof to Prove2Me."""
from __future__ import annotations

import datetime
import json
import os
from pathlib import Path
import sys
import time
import urllib.parse

from publish_natura_helpers import API

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "child_a_direct_evidence"
PROOF = OUT / "solution.lean"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGET_ID = "9b9a6f06-d05d-41ba-980f-04b905e67562"
TARGET_NAME = "Hirsch.cubic_circuit_walk_bound"

EXPLANATION = r"""This is a constructive proof with explicit constant C=17.

The proof first replaces the bounded H-presentation by an irredundant strictly feasible subpresentation of the same polytope. Boundedness makes the row-evaluation map injective, so slack coordinates identify row-circuit steps and walks with maximal elementary augmentations in a nonnegative affine slice.

For the matrix-free slice, the target is recentered as the affine reference. Every displacement admits an exact conformal decomposition into at most n support-minimal elementary directions. A phase records coordinates that have made permanent progress: target-zero coordinates already at zero, and target-positive coordinates already below the threshold M v_i, with M=max(2,n). The reference is reset at every strict progress event; this is the support-safe reset needed to prevent a stale zero coordinate from blocking a later augmentation.

Within a phase, a weighted potential over the live target-zero coordinates contracts by at least a factor 1-1/M after each maximal norm step. After at most 4 M^2 such steps without a progress event, the potential is at most 1/(2 M^2). A support-safe elimination displacement then has a conformal elementary component whose positive maximal augmentation necessarily creates a new progress event, while the checked scalar inequalities preserve all previously trapped coordinates.

Thus each phase uses at most 4 M^2+1 maximal circuit steps and either reaches the target or strictly enlarges a finite subset of n coordinates. There are at most n phases. The arithmetic bound n(4 M^2+1) <= 17 n^3 gives the standard-slice route. Recentring and the slack/row-walk equivalence transfer it back to the irredundant H-presentation, and stationary padding changes 17 m^3 to the required 17 (m+d)^3 budget."""


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
        raise RuntimeError("flattened proof missing; run bundle_natura_child_a_direct.py --check first")
    proof = PROOF.read_text()
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
        write("result.json", {"already_proved": TARGET_ID})
        print(json.dumps({"already_proved": TARGET_ID}))
        return 0
    if target.get("status") != "Open":
        raise RuntimeError("unexpected target status: " + repr(target.get("status")))

    submitted = api.verify(TARGET_ID, proof, EXPLANATION)
    write("submitted.json", submitted)
    sid = submitted["submission_id"]
    verdict = wait_verdict(api, sid)
    final = api.request("/theorems/" + TARGET_ID)
    result = {
        "checked_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "theorem_id": TARGET_ID,
        "submission_id": sid,
        "verdict": verdict.get("status"),
        "theorem_status": final.get("status"),
        "platform_version": getattr(api, "version", None),
    }
    write("result.json", result)
    print(json.dumps(result, indent=2))
    return 0 if verdict.get("status") == "ACCEPTED" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        write("submission-failure.json", {"type": type(exc).__name__, "message": str(exc)[:1200]})
        print(f"ERROR: {exc}", file=sys.stderr)
        raise
