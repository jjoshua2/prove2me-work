#!/usr/bin/env python3
"""Build, audit-gate, and publish the public target-tight outer theorem.

The proof source imports only Mathlib and public definition modules. Credentials
are read only in `publish` mode, after the exact generated solution has compiled
and an audit hash has been written by the GitHub Actions gate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import types

SOURCE = "1fa9bd8cfcdbf11068bd435878ce3a23e99cf434"
SOURCE_PATH = "Solutions/PolynomialTargetTightOuterPublic.lean"
SOURCE_BLOB = "a23ef6804dc94f9d7c2d71c3557c235fac0e5101"
CLIENT_COMMIT = "1692538ba9f7661ca079a86f2963fb48ac2270d1"
CLIENT_PATH = "scripts/publish_excess_two_diameter_two.py"
CLIENT_BLOB = "7da71d03920b59b688bae7cc8b4f9c15432adc4a"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PACKET = Path("/tmp/target-tight-outer-public")
OUT = Path("target_tight_outer_publication_receipts")
NAME = "Hirsch.target_tight_outer_unique_vertex_zero_diameter"
TITLE = "A vertex's tight inequalities form a pointed outer with a unique vertex"

BINDERS = """    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    ∃ m : ℕ, m ≤ n ∧ ∃ e : Fin m ↪ Fin n,
      (∀ i, (∃ k, e k = i) ↔ ⟪a i, v⟫ = b i) ∧
      Function.Injective (HirschCircuit.rowMap (fun k => a (e k))) ∧
      Set.extremePoints ℝ (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) = {v} ∧
      Hirsch.DiamLE (Hirsch.Hpoly (fun k => a (e k)) (fun k => b (e k))) 0"""

FORMAL = (
    "namespace Hirsch\n"
    "theorem target_tight_outer_unique_vertex_zero_diameter\n" +
    BINDERS + " := by sorry\nend Hirsch"
)

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_circuit_model
open scoped RealInnerProductSpace
open Set
"""

NATURAL = (
    "Let P={x in R^d : <a_i,x> <= b_i} be any finite H-polyhedron and let v be a vertex of P. "
    "There is a subpresentation consisting exactly of the inequalities tight at v. Its row-evaluation "
    "map is injective, v is its only vertex, and therefore its padded vertex-edge graph diameter is zero. "
    "The relaxed outer is allowed to be unbounded and may contain infinitely many nonvertex points. "
    "No boundedness, irredundancy, or full-dimensionality assumption is made."
)

EXPLANATION = (
    "At a vertex, the normals of all tight inequalities span the ambient direction space: otherwise a "
    "small symmetric perturbation along a nonzero annihilated direction would keep every inequality "
    "feasible, contradicting extremality. Reindex exactly those tight rows. The spanning fact makes their "
    "row map injective and also shows the original target remains extreme in the relaxed outer. If z is any "
    "vertex of the relaxed outer, every retained row that is tight at z is also tight at v; applying the same "
    "spanning argument inside the retained presentation to z-v forces z=v. Thus the relaxed outer has the "
    "singleton vertex set {v}, so every pair of its vertices is identical and its padded graph diameter is "
    "zero. This is a structural outer-reduction theorem, not a claim that restoring the omitted inequalities "
    "has zero cost or that Polynomial Hirsch is solved."
)


def read_blob(commit: str, path: str, expected: str) -> bytes:
    data = subprocess.run(["git", "show", commit + ":" + path],
                          check=True, capture_output=True).stdout
    actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
    if actual != expected:
        raise RuntimeError("immutable source blob mismatch: " + path)
    return data


def expected_packet() -> bytes:
    source = read_blob(SOURCE, SOURCE_PATH, SOURCE_BLOB).decode("utf-8")
    wrapper = (
        "\n\ntheorem solution\n" + BINDERS + " := by\n"
        "  exact Hirsch.target_tight_outer_unique_vertex_zero_diameter a b v hv\n"
        "\n#print axioms solution\n"
    )
    return (source + wrapper).encode("utf-8")


def prepare() -> None:
    data = expected_packet()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / "solution.lean").write_bytes(data)
    manifest = {
        "source_commit": SOURCE,
        "source_path": SOURCE_PATH,
        "source_git_blob": SOURCE_BLOB,
        "mathlib_rev": PIN,
        "standalone_sha256": hashlib.sha256(data).hexdigest(),
        "theorem_name": NAME,
        "external_definitions": [
            "Definitions.Def_Hirsch_model",
            "Definitions.Def_Hirsch_circuit_model",
        ],
        "tracked_theorem_dependencies": [],
        "evidence_level": "generated standalone source; compile/axiom audit required before publish",
    }
    (PACKET / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    expected = expected_packet()
    solution = PACKET / "solution.lean"
    if not solution.is_file() or solution.read_bytes() != expected:
        raise RuntimeError("standalone packet differs from immutable source and wrapper")
    proof_hash = hashlib.sha256(expected).hexdigest()
    audit = PACKET / "audit-passed.sha256"
    if not audit.is_file() or audit.read_text().strip() != proof_hash:
        raise RuntimeError("compile/axiom audit receipt is absent or names another proof")
    if not os.environ.get("PROVE2ME_API_KEY", "").strip():
        raise RuntimeError("PROVE2ME_API_KEY unavailable")

    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode("utf-8")
    old_title = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(old_title) != 1:
        raise RuntimeError("reviewed client title slot changed")
    client = types.ModuleType("reviewed_target_tight_outer_publisher")
    exec(compile(text.replace(old_title, repr(TITLE), 1), CLIENT_PATH, "exec"), client.__dict__)
    client.VERSION = "0.10.1"
    client.SOURCE = SOURCE
    client.SOURCE_RUN = os.environ.get("GITHUB_RUN_ID", "publication-gate")
    client.THEOREM_NAME = NAME
    client.SOLUTION = solution
    client.SOLUTION_SHA256 = proof_hash
    client.OUT = OUT
    client.PREAMBLE = PREAMBLE
    client.FORMAL = FORMAL
    client.NATURAL = NATURAL
    client.EXPLANATION = EXPLANATION

    def link_mission(api, mission, result):
        tid = result["theorem_id"]
        mid = mission["id"]
        body = (
            f"Published [target-tight unique-vertex outer](p2m:theorem/{tid})"
            + (f" with [accepted proof](p2m:solution/{result['submission_id']})"
               if result.get("submission_id") else "")
            + ": every vertex admits a subpresentation consisting exactly of its tight inequalities; "
              "the retained row map is injective and the relaxed outer has that target as its unique "
              "vertex, hence old-vertex graph diameter zero. The outer may be unbounded. This removes "
              "the old-outer vertex cost in the target-anchored batch-deletion strategy, but restoring "
              "the omitted cuts still carries the unresolved edge-routing cost. The d>=4 circuit-to-edge "
              "refinement frontier remains Open."
        )
        comment = api.request(f"/missions/{mid}/comments",
                              {"body_md": body, "tags": ["reference", "strategy"]}, "POST")
        client.save(OUT / "mission-comment.json", comment)
        refs = {(r.get("type"), r.get("id")) for r in comment.get("references", [])}
        if ("theorem", tid) not in refs:
            raise RuntimeError("mission theorem reference was not resolved")
        if result.get("submission_id") and ("solution", result["submission_id"]) not in refs:
            raise RuntimeError("mission proof reference was not resolved")
        return comment

    client.link_mission = link_mission
    client.main()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "publish"])
    args = parser.parse_args()
    prepare() if args.mode == "prepare" else publish()
