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

The circuit slack definition `Hirsch_circuit_slack_model` is public as definition ID `26b46900-d139-4f6c-b2e7-5088faed7b9e`.

Authenticated backlog audit: Actions run `34302051513`. It reconfirmed all PR #2–#8 entries above plus Child A as `Proved`.

## New GitHub-published verified work

- PR #27 — extreme-face reentry splice; geodesic face-incidence bound; order-sensitive tail theorem `diam(P) <= B+K`; exact d=5 regression and incidence-only lower certificate.
- PR #28 — effective-row common-face model.
- PR #29 — sparse-presentation d-step induction and minimal-counterexample obstruction. This is a conditional diagnostic; the exact d-step conjecture is false globally.
- PR #30 — general common-face dimension tradeoff `dim F(u,x)+dim F(v,x) <= d+(n-2d)` and splitter.
- PR #31 — exact rational counterexamples to arbitrary-facet and selectable-good-facet 2-face bridge strategies.
- PR #33 — generic effective-row count bounds: common rows vanish after restriction and `effectiveCount <= n-commonRowCount`.
- PR #34 — authenticated publication-backlog audit and this index.

## Prove2Me publication in progress for new generic graph lemmas

The following statements have standalone server proofs gated by a fresh Lean/axiom audit on branch `chatgpt/publish-geodesic-theorems`:

- `Hirsch.reentry_splice_through_extreme_face` — platform theorem ID `9d1ffa54-5123-4a52-87a2-e482d3c78918`; created and awaiting/under verification at the time this index was written.
- `Hirsch.geodesic_face_disjoint_tail_bound` — queued after the reentry theorem in the same serial publisher.

Update this section only from authenticated platform results; do not infer acceptance from local compilation.

## Intentionally not marked Proved

`Hirsch.polynomial_edge_refinement_of_circuit_walks`, ID `099c6686-560c-48fc-b2c2-18b6a620a06e`, remains **Open**. It contains the essential graph-routing difficulty. A prior sketch reducing it back to `balanced_polynomial_bound` was deprecated because it created a dependency cycle.

The exact 2-face bridge counterexamples in PR #31 are research certificates, not Prove2Me theorem submissions. They rule out proposed proof strategies, not Polynomial Hirsch itself.

## Integration note

Natura proof-development PRs #13–#26 were merged into the Child-A integration chain as they became kernel-green. Their reusable public results are listed above where individually published; the remaining helper lemmas are preserved in the merged Git history even when not useful as standalone platform declarations.
