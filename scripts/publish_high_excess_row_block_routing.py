#!/usr/bin/env python3
"""Publish the high-excess independent-row-block diameter theorem safely.

The local driver contains the exact row-block proof with the universal
small-excess theorem as an explicit premise. The public solution imports only
the already-Proved small-excess theorem and applies that checked driver. The
repository API key is used only after the generated driver compiles and passes
its axiom audit in the owner-only publication workflow.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import types
from pathlib import Path

from publish_affine_diameter_transport import (
    read_blob, CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB,
)

SOURCE = "4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b"
PRODUCT_PATH = "Solutions/PolynomialProductWalk.lean"
PRODUCT_BLOB = "64e5977f9cd5fd9617b67e82f504550236d49b83"
AFFINE_PATH = "Solutions/PolynomialAffineDiameterTransport.lean"
AFFINE_BLOB = "ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1"
ROW_BLOCK_PATH = "Solutions/PolynomialRowBlockRouting.lean"
ROW_BLOCK_BLOB = "f410f77d854bf2853372492965d35561695f885b"
PACKET = Path("/tmp/high-excess-row-block-public")
OUT = Path("high_excess_row_block_publication_receipts")
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
NAME = "Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks"
TITLE = "High-excess H-polyhedra factorized into small-excess row blocks satisfy the row-excess bound"
PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch"""
BINDERS = """    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d)"""
FORMAL = "namespace Hirsch\ntheorem hpoly_diameter_le_excess_of_independent_small_row_blocks\n" + BINDERS + " := by sorry\nend Hirsch"
NATURAL = (
    "Let P be a nonempty bounded H-polyhedron in R^d described by n rows. "
    "Suppose an invertible linear change of coordinates identifies its rows "
    "with a disjoint family of independent blocks: block i uses counts(i) rows "
    "in dims(i) coordinates, every parent row is in exactly one block, and each "
    "block has dims(i) <= counts(i) <= dims(i)+3. Then the padded ordinary "
    "vertex-edge graph diameter of P is at most n-d. There is no bound on total "
    "row excess n-d or on the number of factors. The conclusion follows from "
    "an actual Cartesian-product decomposition, not from a face-cover or an "
    "amortized circuit-count argument."
)
EXPLANATION = """## Exact product structure

The certificate contains a linear equivalence T from the ambient space to the
product of the block coordinate spaces and a row equivalence e which partitions
all n describing inequalities among the blocks. The row identity hypothesis
says that, after applying T, each selected row depends only on its own block.
Consequently the image of the entire feasible H-polyhedron is exactly the
Cartesian product of the factor H-polyhedra; every combination of factor points
is feasible, so there is no compatibility or portal assumption hidden here.

## Graph cost

Nonemptiness and boundedness of the parent imply the same properties for every
factor. Each block has at most three excess rows, so the already-Proved theorem
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` gives factor diameter
`counts(i)-dims(i)`. Cartesian-product edge walks concatenate one factor at a
time, so the product diameter is at most the sum of those factor excesses.
The row and coordinate equivalences force that sum to equal `n-d`. Finally an
affine equivalence preserves extreme points, ordinary edges, and padded graph
diameter exactly, transporting the product walk back to the original parent.

This is a sufficient high-excess routing criterion. It does not assert that
every circuit carrier admits such a factorization, and therefore does not solve
the open d>=4 circuit-to-edge refinement theorem by itself."""

DEPENDENCY_NAME = "Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three"
DEPENDENCY_ID = "12426807-9602-4014-bd5e-c69fb43f4cb6"
DEPENDENCY_FORMAL = """namespace Hirsch

theorem hpoly_diameter_le_excess_of_rows_le_dim_add_three (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + 3) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch"""


def body(path: str, blob: str) -> str:
    text = read_blob(SOURCE, path, blob).decode("utf-8")
    rows = []
    for line in text.splitlines():
        if line.startswith("import "):
            continue
        if line.startswith("#print axioms"):
            continue
        rows.append(line)
    return "\n".join(rows) + "\n"


def source_prefix() -> str:
    return (
        PREAMBLE + "\n\n" +
        body(PRODUCT_PATH, PRODUCT_BLOB) + "\n" +
        body(AFFINE_PATH, AFFINE_BLOB) + "\n" +
        body(ROW_BLOCK_PATH, ROW_BLOCK_BLOB)
    )


def expected_packets() -> tuple[bytes, bytes]:
    prefix = source_prefix()
    hsmall_type = """    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n - d))
"""
    apply_args = """      dims counts a b T e A hrows hbd hne hcount hsmallcount"""
    driver = prefix + "\n\nnamespace Hirsch\n\ntheorem checked_row_block_adapter\n" + hsmall_type + BINDERS + " := by\n  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks hsmall\n" + apply_args + "\n\n#print axioms checked_row_block_adapter\n\nend Hirsch\n"

    dep_import = "import Theorems.Thm_" + DEPENDENCY_NAME.replace(".", "_") + "\n"
    solution = dep_import + prefix + "\n\nnamespace Hirsch\n\ntheorem solution\n" + BINDERS + " := by\n  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks\n    (fun {d n} a b hbd hrows =>\n      Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three d n a b hrows hbd)\n" + apply_args + "\n\n#print axioms solution\n\nend Hirsch\n"
    return driver.encode("utf-8"), solution.encode("utf-8")


def prepare() -> None:
    driver, solution = expected_packets()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / "driver.lean").write_bytes(driver)
    (PACKET / "solution.lean").write_bytes(solution)
    manifest = {
        "source_commit": SOURCE,
        "product_blob": PRODUCT_BLOB,
        "affine_blob": AFFINE_BLOB,
        "row_block_blob": ROW_BLOCK_BLOB,
        "driver_sha256": hashlib.sha256(driver).hexdigest(),
        "solution_sha256": hashlib.sha256(solution).hexdigest(),
        "target": NAME,
        "public_dependency": {DEPENDENCY_NAME: DEPENDENCY_ID},
        "evidence_boundary": "driver is kernel/axiom audited before authentication; unconditional dependency composition is verified by Prove2Me",
    }
    (PACKET / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    driver, solution = expected_packets()
    if (PACKET / "driver.lean").read_bytes() != driver:
        raise RuntimeError("driver packet changed")
    if (PACKET / "solution.lean").read_bytes() != solution:
        raise RuntimeError("solution packet changed")
    audit = PACKET / "driver-audit-passed.sha256"
    driver_hash = hashlib.sha256(driver).hexdigest()
    if not audit.is_file() or audit.read_text().strip() != driver_hash:
        raise RuntimeError("kernel/axiom driver audit is absent or names another proof")

    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode("utf-8")
    old_title = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(old_title) != 1:
        raise RuntimeError("reviewed publication-client title slot changed")
    client = types.ModuleType("reviewed_row_block_publication_client")
    exec(compile(text.replace(old_title, repr(TITLE), 1), CLIENT_PATH, "exec"), client.__dict__)
    client.VERSION = "0.10.1"
    client.SOURCE = SOURCE
    client.SOURCE_RUN = os.environ.get("GITHUB_RUN_ID", "unknown")
    client.THEOREM_NAME = NAME
    client.SOLUTION = PACKET / "solution.lean"
    client.SOLUTION_SHA256 = hashlib.sha256(solution).hexdigest()
    client.OUT = OUT
    client.PREAMBLE = PREAMBLE
    client.FORMAL = FORMAL
    client.NATURAL = NATURAL
    client.EXPLANATION = EXPLANATION

    api = client.API(os.environ.get("PROVE2ME_API_KEY", ""))
    dep = api.request("/theorems/" + DEPENDENCY_ID)
    if (dep.get("theorem_name") != DEPENDENCY_NAME or
            dep.get("status") != "Proved" or
            dep.get("mathlib_rev") != PIN or
            client.norm(dep.get("formal_statement")) != client.norm(DEPENDENCY_FORMAL)):
        raise RuntimeError("small-excess Prove2Me dependency identity/type/status mismatch")
    client.save(OUT / "small-excess-dependency.json", dep)

    def link_mission(api, mission, result):
        mid, tid = mission["id"], result["theorem_id"]
        offset = 0
        while True:
            page = api.request(f"/missions/{mid}/comments?limit=100&offset={offset}")
            comments = page.get("comments", [])
            for comment in comments:
                if any(r.get("type") == "theorem" and r.get("id") == tid
                       for r in comment.get("references", [])):
                    client.save(OUT / "mission-comment.json", comment)
                    return comment
            offset += len(comments)
            if not comments or len(comments) < 100 or offset >= int(page.get("total", offset + 1)):
                break
        body_md = (
            f"Published [high-excess independent-row-block routing](p2m:theorem/{tid})"
            + (f" with [accepted proof](p2m:solution/{result['submission_id']})"
               if result.get("submission_id") else "")
            + ": an actual Cartesian-product certificate now gives ordinary-edge diameter <= n-d even when total row excess is arbitrarily large, provided every independent block has excess <=3. The proof composes the already-Proved small-excess H-polyhedron theorem with exact product-walk and affine-transport arguments. This directly handles the zero-savings cube carriers from the deletion-savings diagnostics after their redundant carrier rows are certified away. It is a sufficient factorization criterion, not a claim that every saturated circuit carrier factors. The d>=4 circuit-to-edge refinement frontier remains Open; the remaining hard case is a genuinely coupled residual block of excess >=4 or a cost-controlled bypass of such a block."
        )
        comment = api.request(f"/missions/{mid}/comments",
                              {"body_md": body_md, "tags": ["reference", "strategy"]}, "POST")
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
