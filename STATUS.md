# Current Prove2Me Polynomial Hirsch frontier

Date: 2026-09-09. Repo: `jjoshua2/prove2me-work`.

This is the durable handoff for agents. `main` is a conservative integration
baseline; newest proof development can live on the PR branches below. Follow
this file and the logical dependency graph, not merely commit time or whichever
theorem files happen to be present on `main`.

## Executive status

Polynomial Hirsch is **not solved**.

The current formal Prove2Me research bottleneck remains:

**`Hirsch.polynomial_edge_refinement_of_circuit_walks`**
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) — **Open**.

It asks for constants `C,k` such that every length-`L` row-circuit walk between
vertices of a bounded, irredundant, strictly feasible `n`-row `d`-polytope can
be replaced by an ordinary edge/stay walk of length
`C * (n+d)^k * L`. The replacement need not visit nonvertex circuit
intermediates.

An authenticated platform audit on 2026-09-09 confirmed this theorem Open in
the pinned environment. Do not create a cyclic sketch back to
`balanced_polynomial_bound`; that attempted dependency was deprecated.

## Closed work that must not be redone

### Linear Hirsch / Santos

The complete Santos counterexample chain is Prove2Me **Proved**, including:

- `Hirsch.q28_*` through `q28_polar_no_length_five_walk`
- `Hirsch.five_spindle_length_six`
- `Hirsch.spindle_normalize`, `spindle_one_step_axis`,
  `spindle_one_step_from_apex_facet`, `spindle_one_step`,
  `strong_dstep_spindle`
- `Hirsch.santos_counterexample`

`Solutions/Axis*.lean` and closed PR #1 are historical scratch, not blockers.

### Original polynomial reduction and circuit Child A

The old reduction remains conceptually:

```text
polynomial_hirsch_conjecture
  -> balanced_polynomial_bound
  -> polynomial_target_face_access
  -> polynomial_access_to_given_supporting_face
```

PR #9 gives an exact compiled split of the last prescribed-face leaf:

```text
polynomial_access_to_given_supporting_face
  -> cubic_circuit_walk_bound                         Proved
  +  polynomial_edge_refinement_of_circuit_walks     Open
```

`Hirsch.cubic_circuit_walk_bound`
(`9b9a6f06-d05d-41ba-980f-04b905e67562`) is Prove2Me **Proved**. The
completed Natura development includes a concrete `17*n^3` standard circuit
bound and no `sorryAx` in the finished proof chain. Do not redo Child A absent
a discovered defect.

Known obstruction to overstrengthening Child B: an exact irredundant polygon
family has a single maximal circuit step whose endpoints have graph distance
`n/2` already in dimension two. Constant or dimension-only refinement overhead
is false; polynomial row-dependent overhead is not ruled out.

Also Proved and reusable from the older reduction scaffolding:

- `Hirsch.balanced_hpoly_transfer`
- `Hirsch.diameter_bound_of_target_face_access`
- `Hirsch.nonzero_supporting_row_of_distinct_extremes`
- `Hirsch.vertex_tight_rows_span`
- Kalai–Kleitman / Larman / Todd bounds as background (their growth is not a
  fixed polynomial `(n+d)^k`)

## Major Prove2Me-Proved supporting toolkit

### Supporting-face / cut access

- `Hirsch.target_face_access_of_local_neutral_rank`
- `Hirsch.given_supporting_face_access_of_boundary_residual_rank`
- `Hirsch.vertex_exposing_redundant_row_extension`
- `Hirsch.given_supporting_face_access_of_boundary_product_factors`
- `Hirsch.cut_face_access_of_outer_diameter`
- `Hirsch.clipped_diameter_le_outer_add_cut_face`
- `Hirsch.cut_face_access_of_unbounded_outer_diameter`
- `Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one`
- `Hirsch.box_slice_diameter_le_dimension`

### Geodesic / common-face structure

- `Hirsch.reentry_splice_through_extreme_face`
- `Hirsch.geodesic_face_disjoint_tail_bound`
- `Hirsch.geodesic_face_cover_diameter_bound`
- `Hirsch.common_face_dimension_tradeoff`
- `Hirsch.common_face_effective_count_le_rows_minus_common`
- `Hirsch.common_face_diameter_of_effective_rows`

Useful verified branch results include

`dim F(u,x) + dim F(v,x) <= d + (n - 2*d)`

for separated endpoints, plus effective-row deletion/counting for common-face
coordinates. The condition `effectiveCount <= 2*faceDim` is **not automatic**;
never silently treat a lower-dimensional face as balanced.

### Damage / repair routing through PR #49

Public results include:

- `Hirsch.face_interval_cover_route_bound`
  (`11592f65-f434-4fad-9c84-f96cf223c3bf`)
- `Hirsch.ordered_damage_repair_exact`
  (`238cbea9-9f9a-454d-93e5-94344960261e`)
- `Hirsch.route_of_faces_and_surviving_edges`
  (`9eed40c7-03ed-4a02-80b4-1f7404ac05ac`)
- `Hirsch.extreme_face_cut_route_bound`
  (`d3a9d907-a9a7-4564-a718-51d1a1a78889`)
- `Hirsch.mixed_repair_route_or_cut`
  (`92dc970d-1e7c-4bbe-b30c-b781d045360b`)
- `Hirsch.crossing_cube_endpoint_certificate_insufficient`
  (`3672334a-7c8c-4a5d-b95d-8629418d3bba`)
- `Hirsch.face_interval_cover_route_bound_of_start_containment`
  (`ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe`), PR #49,
  submission `6b2c08bc-b2bd-4688-9ab1-019ecf2a98ba`, **Proved**

Ordered repair has exact accounting

`L - removedLength + replacementCost`.

For crossing/unordered repair, time overlap alone is not a geometric
intersection: genuine shared final-parent points/vertices or an equivalent
connected repair certificate are required.

## Latest advance: PR #50 geometric checkpoint rounding / radial final-face repair

PR #50 (`chatgpt/face-preserving-checkpoints`) is stacked on PR #48. Its core
source was independently verified at commit
`7cea19e9abdd16607bbfdaf5919f4a1433b6d416`, Actions `34403714961`: all
**16 new declarations** compiled, **39 axiom reports** contained only
`propext`, `Classical.choice`, and `Quot.sound`, and the exact geometric
regression output reproduced byte-for-byte.

### Two PR #50 results are now public and Proved

Authenticated publication run `34406122009` independently rebuilt/audited the
public wrappers and flattened standalone proofs before submitting them.

1. `Hirsch.face_preserving_vertex_selection`
   - theorem `c8ebefd3-d31a-4d33-b1f8-6298669cc3ba`
   - submission `5c026214-1592-4db8-bc03-be242ced7b18`
   - **ACCEPTED / Proved**

   For a compact parent polytope `P` and an arbitrary (not necessarily finite)
   family of closed extreme faces `F_i`, there is one selector `r` mapping every
   feasible point to a parent vertex, fixing existing parent vertices, and
   preserving every relevant face membership simultaneously:

   `x ∈ F_i -> r(x) ∈ F_i`.

   No continuity or adjacency preservation is asserted. This means a feasible
   shared point of fixed-parent faces is already enough to obtain a vertex
   portal.

2. `Hirsch.face_interval_cover_route_bound_of_feasible_start_containment`
   - theorem `6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102`
   - submission `6c140ee2-141f-4b4f-baa3-031a31df4f7f`
   - **ACCEPTED / Proved**

   The PR #48 start-containment routing bound therefore extends to nonvertex
   marked checkpoints. Only the two global route endpoints must initially be
   parent vertices; simultaneous rounding preserves all needed closed-face
   incidences and the same total face budget.

The same authenticated run posted Polynomial Hirsch mission discussion comment
`dd739cf3-7749-4947-a20a-ba16a17859ef` summarizing the radial construction,
its exact verification boundary, and the remaining global gaps. Receipt
artifact: `10125766656`.

### PR #50 radial construction: strong progress, but not yet a public theorem

For simultaneous monotone clipping

```text
P = Q ∩ ⋂_i {a_i(x) <= b_i}
```

with compact final `P`, convex polyhedral `Q`, and one centre `o ∈ Q` strictly
satisfying every added cut, PR #50 develops the fixed radial map

```text
mu(x)  = max(1, max_i (a_i(x)-a_i(o))/(b_i-a_i(o)))
rho(x) = o + (x-o)/mu(x).
```

Given a supplied length-`L` **outer edge/stay walk** whose endpoints survive in
both `Q` and `P`, and final cut-face intrinsic diameter bounds `B_i`, the written
mathematical construction and exact certificate builder give

`repaired route length <= L + sum_i B_i`.

Along each old edge, normalized violations are affine. Partitioning at their
crossings produces cells mapping either into a **final cut face** or into a
clipped old edge; consecutive pieces share an actual feasible point in the
one fixed final parent, and the newly Proved selector turns those into vertex
portals. This charges at most the final cut faces plus the old clipped edges,
not every historical deformation event.

Nine radial/algebraic declarations are Lean-verified, including feasibility,
active final-face membership, finite radial-scale existence, and affine
dominance on a cell.

**Do not mark the complete `L + sum B_i` simultaneous-clipping theorem Proved
or register it as such yet.** The end-to-end Lean assembly is still missing:

- finite breakpoint / face-cover extraction;
- the clipped-old-edge diameter-one assembly.

The ordinary proof and exact tests are strong research evidence, not a
substitute for the missing final Lean theorem.

### Genuine moving-facet falsifier / representation lesson

PR #50 also gives an exact actual polytope sweep

`P_t = [0,1]^3 ∩ {3x+2y+z <= t}`

from `t=11/2` to `t=9/2`. The stationary facets `x=1` and `y=1` intersect
before the sweep but are disjoint afterward although both remain genuine
facets. The old shortest path through `(1,1,0)` loses its middle checkpoint.
Thus preserving historical support labels does not preserve final-parent
connectivity. Adding the final moving facet and applying the radial
construction repairs the route. This is a falsifier for a representation
lemma, not a Hirsch counterexample.

## What remains genuinely hard after PR #50

PR #50 sharpens rather than closes the frontier.

For a fixed-parent feasible trace, the **nonvertex portal problem is solved**:
feasible shared points can be rounded to parent vertices without losing any
closed-face incidences.

For simultaneous monotone clipping, there is now a concrete fixed-final-parent
representation with polynomial **support count**. The hard obligations are:

1. **Finish the end-to-end Lean clipping theorem** from the already verified
   radial/checkpoint pieces (finite breakpoint extraction + clipped-edge
   diameter-one assembly).
2. **Applicability:** derive the needed outer-edge / monotone-clipping model
   from the desired global projective/Pachner/circuit construction. A general
   circuit step is not an old edge.
3. **Polynomial cost:** prove polynomial control of `sum_i B_i`. A polynomial
   number of final faces does not imply polynomial total diameter cost.

Do not use the whole parent polytope as a repair face for a circuit segment;
that simply inserts the unknown target diameter into the assumed budget. PR
#50 includes an irredundant hexagon regression with one maximal circuit step,
edge distance three, and no proper face containing the segment.

A productive next decomposition should keep **representation/applicability**
and **face-cost control** separate, and should avoid any child that merely
restates Polynomial Hirsch or depends cyclically on an ancestor.

## Dead ends / regression tests

Before substantial Lean investment, test new geometric statements against:

- PR #31 exact 4D/5D Dantzig counterexamples to arbitrary/selectable 2-face
  bridge strategies;
- cycle/polygon and Proved Boolean-cube counterexamples to treating
  chronological overlap as a portal;
- PR #50's genuine moving-facet intersection-loss sweep;
- PR #27's exact 5D example where incidence-only charging gives 9 while the
  order-sensitive bound gives the sharp value 5;
- PR #50's hexagon maximal-circuit carrier obstruction;
- PR #11's Q28 work, which found finite amplification but proves linear upper
  bounds for the independent scalar-fiber construction class.

## Branch / PR map

- PR #9 `chatgpt/circuit-leaf-split` — exact circuit split; Child B Open
- PRs #13–#26 — completed Natura Child-A proof development
- PR #11 `chatgpt/counterexample-couplings` — Q28/counterexample falsification
- PR #27 `chatgpt/face-reentry-splice` — geodesic/face-routing foundation
- PR #28 / #33 — effective-row common-face work
- PR #30 — common-face dimension tradeoff / splitter
- PR #31 — exact 2-face-bridge counterexamples
- PR #34 `chatgpt/publish-backlog-audit` — publication audit/index
- PR #38 `chatgpt/projective-damage-blocks` — damage-repair foundation
- PR #39–#42 — crossing repair / cut certificates / route-or-cut machinery
- PRs #43–#47 — publication gates for repair results
- PR #48 `chatgpt/interval-start-portals` — start/active containment
- PR #49 — public start-containment theorem
- PR #50 `chatgpt/face-preserving-checkpoints` — feasible checkpoint rounding,
  radial final-face construction, moving-facet falsifier; two completed
  checkpoint results now Prove2Me Proved

Recent no-op or publication-only commits do not imply newer mathematics. Follow
the dependency graph, source verification receipts, and this file.

## Publication truth / environment

A local `lake build`, exact finite certificate, or GitHub Actions compile is
not a Prove2Me theorem verdict. Call a theorem Proved only after authenticated
`/verify` returns `ACCEPTED` or an authenticated read confirms live status.

Current mission environment:

- Lean `v4.30.0`
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- platform version observed by authenticated audit: `0.9.8`

Credentials stay outside Git. GitHub Actions uses repository secret
`PROVE2ME_API_KEY` for authenticated audit/publication workflows.
