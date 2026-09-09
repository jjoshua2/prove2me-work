# Polynomial Hirsch publication index — 2026-09-09

Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This index distinguishes **Prove2Me public theorems**, **GitHub-verified
results**, and **research-only exact certificates**. It does not label
conditional research or an incomplete Lean assembly as a global Polynomial
Hirsch proof.

For the current mathematical frontier, branch map, and next obligations, read
[`../STATUS.md`](../STATUS.md).

## Current formal frontier

`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains **Open**.

Its sibling `Hirsch.cubic_circuit_walk_bound`
(`9b9a6f06-d05d-41ba-980f-04b905e67562`) is **Proved**. PR #50 adds two
new Proved geometric repair/checkpoint results but does not close edge
refinement.

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
| `HirschCircuit.rowMap_injective_of_bounded` | `cbc71ccc-9bc3-46c5-b8d4-02beb69791c8` | Proved | Natura helper |
| `HirschCircuit.rowCircuitWalk_mono` | `25951473-a407-43c4-a7be-443e35593402` | Proved | Natura helper |
| `HirschCircuit.exists_positive_maximal_nonnegative_step` | `ac00e416-0658-485d-9a4a-1cbeac8b26a4` | Proved | Natura helper |
| conformal decomposition publication | `05726681-715c-408a-b44c-d73dac856b20` | Proved | PR #25 |
| `Hirsch.reentry_splice_through_extreme_face` | `9d1ffa54-5123-4a52-87a2-e482d3c78918` | Proved | PR #27 / #35 |
| `Hirsch.geodesic_face_disjoint_tail_bound` | `16f7c90c-1721-4cfe-aa86-52c761ff99c1` | Proved | PR #27 / #35 |
| `Hirsch.geodesic_face_cover_diameter_bound` | `81bb9472-8b70-48dd-b7cc-1921d6a14fe9` | Proved | PR #27 / #37 |
| `Hirsch.common_face_dimension_tradeoff` | `b56b59cc-fe2a-4d64-979d-595cabec37ca` | Proved | PR #30 / #36 |
| `Hirsch.common_face_effective_count_le_rows_minus_common` | `be716434-50fa-4b32-a13a-71c3ae2caa4b` | Proved | PR #33 / #36 |
| `Hirsch.common_face_diameter_of_effective_rows` | `496bd99b-f3dc-465e-9c99-ebca0b1129be` | Proved | PR #28 / #36 |
| `Hirsch.face_interval_cover_route_bound` | `11592f65-f434-4fad-9c84-f96cf223c3bf` | Proved | PR #39 / #43 |
| `Hirsch.ordered_damage_repair_exact` | `238cbea9-9f9a-454d-93e5-94344960261e` | Proved | PR #40 / #44 |
| `Hirsch.route_of_faces_and_surviving_edges` | `9eed40c7-03ed-4a02-80b4-1f7404ac05ac` | Proved | PR #40 / #44 |
| `Hirsch.extreme_face_cut_route_bound` | `d3a9d907-a9a7-4564-a718-51d1a1a78889` | Proved | PR #41 / #45 |
| `Hirsch.mixed_repair_route_or_cut` | `92dc970d-1e7c-4bbe-b30c-b781d045360b` | Proved | PR #42 / #46 |
| `Hirsch.crossing_cube_endpoint_certificate_insufficient` | `3672334a-7c8c-4a5d-b95d-8629418d3bba` | Proved | PR #41 / #47 |
| `Hirsch.face_interval_cover_route_bound_of_start_containment` | `ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe` | Proved | PR #48 / #49 |
| `Hirsch.face_preserving_vertex_selection` | `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba` | Proved | PR #50 |
| `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment` | `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102` | Proved | PR #50 |

Public definition modules:

- `Hirsch_circuit_slack_model` — `26b46900-d139-4f6c-b2e7-5088faed7b9e`
- `Hirsch_common_face_geometry` — `dc9161e6-0dae-4da5-ab82-91b871e2409e`

## Publication / verifier receipts

- PR #35 / Actions `34301906252`: reentry splice and ordered-tail submissions,
  both `ACCEPTED`.
- PR #37 / Actions `34344699190`: face-incidence diameter theorem,
  `ACCEPTED`.
- PR #36 / Actions `34343690139`: public common-face definition plus three
  theorems, all `ACCEPTED`.
- PR #43 / Actions `34360204346`: `face_interval_cover_route_bound`,
  `ACCEPTED`.
- PR #44 / Actions `34361247630`: exact ordered damage repair and
  face/surviving-edge routing, both `ACCEPTED`.
- PR #45 / Actions `34360502053`: `extreme_face_cut_route_bound`, `ACCEPTED`.
- PR #46 / Actions `34361604218`: `mixed_repair_route_or_cut`, `ACCEPTED`.
- PR #47 / Actions `34363222900`: Boolean-cube endpoint-certificate
  obstruction, `ACCEPTED`.
- PR #49 / Actions `34365609278`: start-containment theorem
  `ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe`, submission
  `6b2c08bc-b2bd-4688-9ab1-019ecf2a98ba`, **ACCEPTED / Proved**.
- PR #50 publication / Actions `34406122009`:
  - `Hirsch.face_preserving_vertex_selection`, theorem
    `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`, submission
    `5c026214-1592-4db8-bc03-be242ced7b18`, **ACCEPTED / Proved**;
  - `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment`,
    theorem `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`, submission
    `6c140ee2-141f-4b4f-baa3-031a31df4f7f`, **ACCEPTED / Proved**;
  - Polynomial Hirsch mission discussion comment
    `dd739cf3-7749-4947-a20a-ba16a17859ef` records the radial construction,
    verification boundary, and remaining global gaps;
  - receipt artifact `10125766656`.

Publication workflows rebuild reviewed source, flatten private proof dependencies
where needed, independently compile/axiom-audit standalone server proofs, and
reject `sorryAx` / nonstandard proof axioms before authenticated submission.

## GitHub-verified work that is not a global proof

- PR #27 — reentry splice, geodesic face-incidence and ordered-tail work.
- PR #28 / #33 — effective-row common-face model and count bounds.
- PR #29 — sparse-presentation d-step induction / minimal-counterexample
  diagnostic; conditional only.
- PR #30 — general common-face dimension tradeoff and splitter.
- PR #31 — exact rational counterexamples to proposed 2-face bridge strategies.
- PR #38 — ordered projective-damage amortization / surviving-step repair.
- PR #39–#42 — crossing repair, exact cut certificates, and route-or-cut
  framework.
- PR #48 — derives portals from start containment and proves the stronger
  active-containment corollary. The general start-containment theorem is public
  via #49.
- PR #50 — seven face-preserving checkpoint/routing declarations plus nine
  radial-clipping algebra declarations are kernel-verified. Two checkpoint
  results are public above. The stronger feasible active-containment theorem
  and the nine radial components remain recorded here as verified source unless
  separately published later.

## PR #50 radial construction — not yet a Prove2Me theorem

PR #50 gives a written mathematical proof and exact certificate constructor for
simultaneous monotone clipping with a strictly feasible common centre. For a
supplied length-`L` **outer edge/stay walk** and final cut-face diameter budgets
`B_i`, the construction gives a final-parent repair route of length

`L + sum_i B_i`.

The fixed radial map partitions each old edge at crossings of affine normalized
violations. Every cell maps either into a final cut face or a clipped old edge;
shared feasible breakpoint images become vertex portals via the now-public
face-preserving selector.

**Formal boundary:** the complete clipping theorem has not yet been assembled
as one end-to-end Lean declaration. Remaining formal steps are finite
breakpoint/face-cover extraction and the clipped-old-edge diameter-one
assembly. Therefore it is intentionally **not** listed above as Prove2Me
Proved.

Exact PR #50 regressions include the genuine moving-facet intersection-loss
sweep and a maximal-circuit hexagon obstruction. They are falsification and
construction certificates, not Lean hull theorems.

## Research-only exact certificates / dead ends

- PR #31's 4D/5D Dantzig examples refute arbitrary/selectable 2-face bridge
  strategies, not Polynomial Hirsch.
- PRs #39/#42 show chronological overlap alone does not create a geometric
  portal; the Boolean-cube abstract obstruction is separately public/Proved.
- PR #50's moving-facet sweep shows even persistent historical face labels can
  lose their intersection in the final parent; use final-parent supports.
- PR #11's Q28 scalar-coupling program found finite amplification but also
  established linear upper bounds for the independent scalar-fiber class.

## Intentionally not marked Proved

`Hirsch.polynomial_edge_refinement_of_circuit_walks`, ID
`099c6686-560c-48fc-b2c2-18b6a620a06e`, remains **Open**.

The complete radial simultaneous-clipping `L + sum B_i` theorem is also not
marked Proved for the formalization reason above.

The sharp next questions are: finish that Lean assembly; derive the required
outer-edge/clipping representation from the global projective/Pachner/circuit
construction; and obtain polynomial control of `sum_i B_i`. See `STATUS.md`
before creating new children.
