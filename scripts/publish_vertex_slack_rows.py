#!/usr/bin/env python3
"""Prepare, audit-gate, and publish the public vertex slack-row bound.

The mathematical source imports only Mathlib and the public Hirsch model.
Credentials are read only in publish mode, after the exact standalone proof has
compiled and the workflow has written a matching audit hash.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import types

SOURCE = "8a14d88e8bb61b11fd41c9fb7b3df8f08b3414ce"
SOURCE_PATH = "Solutions/PolynomialVertexSlackRowsPublic.lean"
SOURCE_BLOB = "6a2c1d9ec1e63e2026f4d0845f955a7e61f6607a"
CLIENT_COMMIT = "1692538ba9f7661ca079a86f2963fb48ac2270d1"
CLIENT_PATH = "scripts/publish_excess_two_diameter_two.py"
CLIENT_BLOB = "7da71d03920b59b688bae7cc8b4f9c15432adc4a"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PACKET = Path("/tmp/vertex-slack-row-bound-public")
OUT = Path("vertex_slack_row_publication_receipts")
NAME = "Hirsch.vertex_strictly_slack_rows_card_le_row_excess"
TITLE = "A vertex has at most row-excess many strictly slack inequalities"

BINDERS = """    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b)) :
    (Finset.univ.filter (fun i => ⟪a i, v⟫ < b i)).card ≤ n - d"""

FORMAL = (
    "namespace Hirsch\n"
    "theorem vertex_strictly_slack_rows_card_le_row_excess\n" +
    BINDERS + " := by sorry\nend Hirsch"
)

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set
"""

NATURAL = (
    "Let P={x in R^d : <a_i,x> <= b_i} be any finite H-polyhedron described by n rows, "
    "and let v be a vertex. Then at most n-d describing inequalities are strictly slack at v. "
    "Equivalently, at least d describing rows are tight at every vertex. No boundedness, "
    "irredundancy, simplicity, or full-dimensionality assumption is required."
)

EXPLANATION = (
    "The proof first gives a direct finite-perturbation argument that the normals of all inequalities "
    "tight at a vertex span the ambient d-dimensional direction space: otherwise a small symmetric "
    "move along a common annihilated direction would keep all inequalities feasible and contradict "
    "extremality. Evaluating against the tight normals is therefore an injective linear map from R^d "
    "to one real coordinate per tight row, so finrank gives at least d tight rows. Feasibility makes "
    "every describing row either tight or strictly slack at v; the two sets partition the n rows. "
    "Subtracting the at-least-d tight rows gives at most n-d strictly slack rows. The theorem is a "
    "sharp counting fact used in target-anchored batch reinsertion; it does not itself supply the "
    "edge-routing budget of the exposed faces or prove Polynomial Hirsch."
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
        "  exact Hirsch.vertex_strictly_slack_rows_card_le_row_excess a b v hv\n"
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
        "external_definitions": ["Definitions.Def_Hirsch_model"],
        "tracked_theorem_dependencies": [],
        "platform_version_expected": "0.10.3",
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
    client = types.ModuleType("reviewed_vertex_slack_row_publisher")
    exec(compile(text.replace(old_title, repr(TITLE), 1), CLIENT_PATH, "exec"), client.__dict__)
    client.VERSION = "0.10.3"
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
            f"Published [vertex slack-row bound](p2m:theorem/{tid})"
            + (f" with [accepted proof](p2m:solution/{result['submission_id']})"
               if result.get("submission_id") else "")
            + ": every vertex of an n-row H-presentation in dimension d has at most n-d strictly "
              "slack inequalities. This is the sharp row-excess cardinality input behind the "
              "target-anchored batch-reinsertion bound. It does not supply the final face-routing "
              "budgets, and the d>=4 circuit-to-edge refinement frontier remains Open."
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
