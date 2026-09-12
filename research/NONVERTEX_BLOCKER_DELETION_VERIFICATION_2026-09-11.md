# Nonvertex blocker deletion / universal vertex-face verification

Date: 2026-09-11.

Frozen theorem source commit: `a9a0446d6cac42d30d90040e63ef8f761e094fa3`.

Hosted verification:
- run `34672288285`
- job `103495796215`
- artifact `10291346409`
- digest `sha256:a02c7e67e950efa8da8208f0b6143e3423653183e74752743fc9d137848924c1`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialNonvertexBlockerDeletion` and axiom-audited all four public declarations with only the repository-allowed logical axioms `propext`, `Classical.choice`, and `Quot.sound`:

- `HirschCircuitLocalization.vertices_tight_on_unique_nonneutral_row`
- `HirschCircuitLocalization.rowCircuitStep_target_blocker_pointed_delete_or_all_vertices_tight`
- `HirschCircuitLocalization.diamLE_of_all_vertices_in_extreme_face`
- `HirschCircuitLocalization.rowCircuitStep_target_blocker_pointed_delete_or_face_controls_parent`

Formal meaning: for an arbitrary maximal circuit step in an injective finite H-presentation, the destination blocker either admits a pointed one-row deletion or every original parent vertex lies on that blocker supporting face. In the exceptional one-nonneutral-row case any graph budget for that face already controls the whole parent graph, so no deletion-outer cost is needed.

This is a structural/cost dichotomy, not a global recurrence and not a solution of the Open d>=4 circuit-to-edge theorem.
