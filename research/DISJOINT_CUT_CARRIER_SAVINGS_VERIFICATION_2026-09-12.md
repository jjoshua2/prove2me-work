# Disjoint cut carrier savings verification

Date: 2026-09-12.

Frozen theorem head: `78cf6257c32fd69f1e82d2112a91066d0e7310c5`.

Hosted verification:
- run `34698381788`
- job `103565698090`
- artifact `10298904568`
- artifact digest `sha256:5f6cd4d0d377435d0304985d0fd03106c92ce32bb548ad4c2225054b34f493e2`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only hosted gate built `Solutions.PolynomialDisjointCutCarrierSavings`, ran the file directly through Lean, and transitive-axiom-audited:
- `HirschCircuitLocalization.row_ne_zero_of_tight_and_strict`
- `HirschCircuitLocalization.closed_extreme_faces_disjoint_of_no_parent_vertex_portal`
- `HirschCircuitLocalization.closed_extreme_faces_disjoint_of_region_nonadj`
- `HirschCircuitLocalization.commonFace_subset_hpolyRowFace_of_tight`
- `HirschCircuitLocalization.row_strict_on_commonFace_of_disjoint_rowFaces`
- `HirschCircuitLocalization.commonFace_minExcess_add_disjoint_rowFaces_le`
- `HirschCircuitLocalization.commonFace_minExcess_add_disjoint_targetSlack_rowFaces_le`

All seven reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the strict checker reports: `Axiom audit passed: 7 required declarations; 7 reports checked; only standard logical axioms.`

## Formal contribution

Two compact closed extreme parent faces with no shared parent extreme vertex are disjoint. Consequently, nonadjacency of two distinct labels in the parent-vertex face-intersection graph forces the underlying faces to be disjoint.

If an actual portal pair is tight on a nonzero row `i`, its whole common carrier lies in row face `i`. Any row face `j` disjoint from row face `i` is therefore strictly slack at every point of that carrier. A finite family of such disjoint row faces can be fed directly into PR #186's verified strict-row savings theorem to obtain

`(M_min - h) + |J| <= n - d`

for the actual portal-pair carrier. In the target-slack specialization, nonzeroness of the current cut row follows automatically from being tight at a portal while strictly slack at the fixed target.

Strategic role: merged shortest-region routing #188 supplies chordless path nonadjacency. This module converts that graph nonadjacency into exactly the carrier-wide strictness hypothesis needed by the quantitative row-savings theorem. The remaining composition is cardinality: count how many used cut labels are nonneighbors of the current cut and map them to disjoint target-slack row faces.

This is a carrier resource theorem, not a global diameter theorem. No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
