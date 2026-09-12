#!/usr/bin/env python3
"""Prepare, audit-gate, and publish compact extreme-face disjointness.

The exact mathematical source is standalone: Mathlib/Krein--Milman only.
Credentials are read only in publish mode, after the generated proof packet has
compiled and its SHA-256 has been written to the audit receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import types

SOURCE = "fb1594e865b723ea2e6bf63baf46beeba7025027"
SOURCE_PATH = "Solutions/PolynomialClosedExtremeFacesDisjointPublic.lean"
SOURCE_BLOB = "523d3573a6b9be1bf6d81aa92ad0994285254abb"
CLIENT_COMMIT = "1692538ba9f7661ca079a86f2963fb48ac2270d1"
CLIENT_PATH = "scripts/publish_excess_two_diameter_two.py"
CLIENT_BLOB = "7da71d03920b59b688bae7cc8b4f9c15432adc4a"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PACKET = Path("/tmp/closed-extreme-face-disjoint-public")
OUT = Path("closed_face_disjoint_publication_receipts")
NAME = "Hirsch.closed_extreme_faces_disjoint_of_no_shared_parent_extreme"
TITLE = "Closed extreme faces with no shared parent extreme point are disjoint"

BINDERS = """    {d : ℕ}
    (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P)
    (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (hno : ¬ ∃ v : EuclideanSpace ℝ (Fin d),
      v ∈ Set.extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G) :
    Disjoint F G"""

FORMAL = (
    "namespace Hirsch\n"
    "theorem closed_extreme_faces_disjoint_of_no_shared_parent_extreme\n" +
    BINDERS + " := by sorry\nend Hirsch"
)

PREAMBLE = """import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
open scoped RealInnerProductSpace
open Set
"""

NATURAL = (
    "Let P be a compact subset of finite-dimensional Euclidean space, and let F and G be closed "
    "extreme subsets of P. If no extreme point of P belongs to both F and G, then F and G are "
    "disjoint. Equivalently, any nonempty intersection of two closed extreme faces of a compact "
    "parent contains a parent extreme point."
)

EXPLANATION = (
    "Assume F and G intersect. Their intersection is closed, extreme in P, and compact because it "
    "is a closed subset of compact P. Krein--Milman supplies an extreme point of this nonempty "
    "compact intersection. Extreme points of an extreme subset of P are extreme points of P, so "
    "this gives a parent extreme point lying in both F and G, contradicting the hypothesis."
)


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"])


def verify_blob(commit: str, path: str, expected: str) -> bytes:
    blob = run("git", "rev-parse", f"{commit}:{path}")
    if blob != expected:
        raise RuntimeError(f"blob mismatch for {path}: {blob} != {expected}")
    return git_bytes(commit, path)


def expected_packet() -> bytes:
    source = verify_blob(SOURCE, SOURCE_PATH, SOURCE_BLOB)
    text = source.decode("utf-8")
    wrapper = """

theorem solution
{binders} := by
  exact Hirsch.closed_extreme_faces_disjoint_of_no_shared_parent_extreme
    P F G hP hF hG hFc hGc hno

#print axioms solution
""".format(binders=BINDERS)
    return (text.rstrip() + wrapper).encode("utf-8")


def prepare() -> None:
    PACKET.mkdir(parents=True, exist_ok=True)
    proof = expected_packet()
    proof_path = PACKET / "solution.lean"
    proof_path.write_bytes(proof)
    manifest = {
        "source_commit": SOURCE,
        "source_path": SOURCE_PATH,
        "source_blob": SOURCE_BLOB,
        "proof_sha256": sha256(proof),
        "theorem_name": NAME,
        "mathlib_rev": PIN,
        "private_solutions_imports": False,
    }
    (PACKET / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(manifest, sort_keys=True), flush=True)


def load_reviewed_client(proof_hash: str):
    data = verify_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB)
    source = data.decode("utf-8")
    old_title = "Excess-two H-polyhedra have padded diameter at most two"
    if old_title not in source:
        raise RuntimeError("reviewed client title slot not found")
    source = source.replace(old_title, TITLE, 1)
    module = types.ModuleType("reviewed_publish_client")
    module.__file__ = f"{CLIENT_COMMIT}:{CLIENT_PATH}"
    exec(compile(source, module.__file__, "exec"), module.__dict__)
    if getattr(module, "VERSION", None) != "0.10.0":
        raise RuntimeError("reviewed client version changed unexpectedly")
    module.VERSION = "0.10.3"
    module.SOURCE = SOURCE
    module.SOURCE_RUN = os.environ.get("SOURCE_RUN", "34699009349")
    module.THEOREM_NAME = NAME
    module.SOLUTION = str(PACKET / "solution.lean")
    module.SOLUTION_SHA256 = proof_hash
    module.OUT = OUT
    module.PREAMBLE = PREAMBLE
    module.FORMAL = FORMAL
    module.NATURAL = NATURAL
    module.EXPLANATION = EXPLANATION
    return module


def publish() -> None:
    key = os.environ.get("PROVE2ME_API_KEY", "").strip()
    if not key or not key.startswith("p2m_"):
        raise RuntimeError("PROVE2ME_API_KEY repository credential is absent or malformed")

    proof = expected_packet()
    proof_path = PACKET / "solution.lean"
    if not proof_path.exists() or proof_path.read_bytes() != proof:
        raise RuntimeError("prepared standalone proof differs from immutable source packet")
    proof_hash = sha256(proof)
    audit = PACKET / "audit-passed.sha256"
    if not audit.exists() or audit.read_text(encoding="utf-8").strip() != proof_hash:
        raise RuntimeError("standalone proof has not passed the exact-hash audit gate")

    client = load_reviewed_client(proof_hash)
    original_link = client.link_mission

    def link_mission(api, theorem_id: str):
        return original_link(
            api,
            theorem_id,
            "Publication from the current Polynomial Hirsch repair line: compact closed extreme "
            "faces with no shared parent extreme point are disjoint. This is the geometric bridge "
            "used after shortest/chordless region routing: nonadjacent used face labels cannot "
            "intersect, allowing disjoint target-slack row faces to feed the strict-row carrier "
            "resource inequality. This theorem alone is not a diameter bound.",
        )

    client.link_mission = link_mission
    client.main()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=["prepare", "publish"])
    args = parser.parse_args()
    if args.mode == "prepare":
        prepare()
    else:
        publish()


if __name__ == "__main__":
    main()
