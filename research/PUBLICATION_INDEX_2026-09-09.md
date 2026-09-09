# Polynomial Hirsch publication index — 2026-09-09

Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This index distinguishes **Prove2Me public theorems**, **GitHub-published verified lemmas**, and **research-only exact certificates**. It does not label conjectural or conditional research as a proved global Polynomial Hirsch result.

## Prove2Me — verified public results

| Theorem | Prove2Me ID | Status | Source work |
|---|---|---|---|
| `Hirsch.target_face_access_of_local_neutral_rank` | `4da3a606-c8d4-4570-a246-afbff569cc7a` | Proved | PR #2 |
| `Hirsch.given_supporting_face_access_of_boundary_residual_rank` | `7eeb1ee6-c837-4814-943c-2d39cf6fc4a7` | Proved | PR #3 |
| `Hirsch.vertex_exposing_redundant_row_extension` | `0fff8924-afe0-4653-8c3c-2f4f5cd815cd` | Proved | PR #3 |
| `Hirsch.given_supporting_face_access_of_boundary_product_factors` | `cf9699ad-34c6-4202-8b4a-10177c844813` | Proved | PR #4 |
| `Hirsch.cut_face_access_of_outer_diameter` | `7d78c1ee-f7f7-439b-99f9-8210bb1b5de6` | Proved | PR #5 |
| `Hirsch.clipped_diameter_le_outer_add_cut_face` | `4b66b5b2-64e6-4da7-b8f3-a443c0c724d3` | Proved | PR #6 |
| `Hirsch.cut_face_access_of_unbounded_outer_diameter` | `12f145c8-ecde-4cdd-97b2-eb9b24d1d778` | Proved | PR #7 |
| `Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one` | `376a6b61-a5a9-4c6f-87c6-4bddc9aa64b1` | Proved | PR #7 |
| `Hirsch.box_slice_diameter_le_dimension` | `76900e5f-9732-427a-b648-9499518dce05` | Proved | PR #8 |
| `Hirsch.cubic_circuit_walk_bound` | `9b9a6f06-d05d-41ba-980f-04b905e67562` | Proved | Natura / Child A |
| `HirschCircuit.rowMap_injective_of_bounded` | `cbc71ccc-9bc3-46c5-b8d4-02beb69791c8` | Proved | Natura helper publication |
| `HirschCircuit.rowCircuitWalk_mono` | `25951473-a407-43c4-a7be-443e35593402` | Proved | Natura helper publication |
| `HirschCircuit.exists_positive_maximal_nonnegative_step` | `ac00e416-0658-485d-9a4a-1cbeac8b26a4` | Proved | Natura helper publication |
| conformal decomposition publication | `05726681-715c-408a-b44c-d73dac856b20` | Proved | PR #25 / submission `9003da2a-48dd-4d30-9e64-a3f4eaf93235` |
| `Hirsch.reentry_splice_through_extreme_face` | `9d1ffa54-5123-4a52-87a2-e482d3c78918` | Proved | PR #27 / publication PR #35 |
| `Hirsch.geodesic_face_disjoint_tail_bound` | `16f7c90c-1721-4cfe-aa86-52c761ff99c1` | Proved | PR #27 / publication PR #35 |
| `Hirsch.geodesic_face_cover_diameter_bound` | `81bb9472-8b70-48dd-b7cc-1921d6a14fe9` | Proved | PR #27 / publication PR #37 |
| `Hirsch.common_face_dimension_tradeoff` | `b56b59cc-fe2a-4d64-979d-595cabec37ca` | Proved | PR #30 / publication PR #36 |
| `Hirsch.common_face_effective_count_le_rows_minus_common` | `be716434-50fa-4b32-a13a-71c3ae2caa4b` | Proved | PR #33 / publication PR #36 |
| `Hirsch.common_face_diameter_of_effective_rows` | `496bd99b-f3dc-465e-9c99-ebca0b1129be` | Proved | PR #28 / publication PR #36 |

Public definition modules:

- `Hirsch_circuit_slack_model` — definition ID `26b46900-d139-4f6c-b2e7-5088faed7b9e`.
- `Hirsch_common_face_geometry` — definition ID `dc9161e6-0dae-4da5-ab82-91b871e2409e`.

Publication/verifier receipts:

- PR #35 / Actions `34301906252`: reentry splice and ordered-tail theorem. Submissions `7ade01da-474c-4a55-8c3a-b60e130746aa` and `3237871f-7670-4489-8e96-340312b9792a`, both `ACCEPTED`.
- PR #37 / Actions `34344699190`: face-incidence diameter theorem. Submission `0127d3e9-87b8-47c4-86dc-04b9f20f6d1e`, `ACCEPTED`; receipt artifact `10101432222`.
- PR #36 / Actions `34343690139`: common-face public definition plus three theorems. Submissions `9a42fa4d-2634-44e6-82ec-9edc9fb19d53`, `49221457-5a3f-4a47-a468-e89c75cc8a94`, and `ec84d0ee-c43c-40a0-90e1-bdb4279d01c2`, all `ACCEPTED`; receipt artifact `10101643730`.

Each publication run rebuilt the reviewed source, generated standalone server proof files with no private `Solutions.*` imports, compiled them independently, and rejected `sorryAx`/nonstandard axioms before any Prove2Me verification call.

## GitHub-published verified work

- PR #27 — extreme-face reentry splice; geodesic face-incidence bound; order-sensitive tail theorem `diam(P) <= B+K`; exact d=5 regression and incidence-only lower certificate. Its three main reusable graph theorems are now Prove2Me `Proved` above.
- PR #28 — effective-row common-face model. Its main balanced-diameter transfer is now Prove2Me `Proved` above.
- PR #29 — sparse-presentation d-step induction and minimal-counterexample obstruction. This remains a conditional diagnostic; the exact d-step conjecture is false globally, so it is intentionally not promoted as a global theorem claim.
- PR #30 — general common-face dimension tradeoff `dim F(u,x) + dim F(v,x) <= d + (n-2d)` and splitter. The main dimension tradeoff is Prove2Me `Proved` above; the broader splitter remains preserved in the verified GitHub source.
- PR #31 — exact rational counterexamples to arbitrary-facet and selectable-good-facet 2-face bridge strategies.
- PR #33 — generic effective-row count bounds. Its main count inequality is Prove2Me `Proved` above.
- PR #34 — authenticated publication-backlog audit and this index.
- PR #35 — standalone publication gate/receipts for reentry and ordered-tail.
- PR #36 — public common-face vocabulary plus standalone publication gate/receipts for the three common-face results.
- PR #37 — standalone publication gate/receipts for the face-incidence diameter theorem.

## Research-only exact certificates

PR #31 publishes the exact rational 4D/infinite-family and 5D counterexamples to the proposed 2-face bridge strategies. These are mathematical/computational certificates, not Lean hull certificates and not Prove2Me theorem claims. They rule out proof strategies, not Polynomial Hirsch itself.

## Intentionally not marked Proved

`Hirsch.polynomial_edge_refinement_of_circuit_walks`, ID `099c6686-560c-48fc-b2c2-18b6a620a06e`, remains **Open**. It contains the essential graph-routing difficulty. A prior sketch reducing it back to `balanced_polynomial_bound` was deprecated because it created a dependency cycle.

## Integration note

Natura proof-development PRs #13–#26 were merged into the Child-A integration chain as they became kernel-green. Their reusable public results are listed above where individually published; the remaining helper lemmas are preserved in the merged Git history even when not useful as standalone platform declarations.
