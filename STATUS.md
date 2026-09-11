# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-10 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Live authenticated platform observed: Prove2Me **0.10.0**.
Lean environment: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed provenance belongs in the dated files under `research/`; do not infer verification status from branch names or old notes.

## Executive status

**Polynomial Hirsch is not solved.** The sole formal Open bottleneck remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- live status **Open** after the latest 0.10.0 publication transaction
- parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`) is a sketch: `d ≤ 3` is the Proved Klee child and `d ≥ 4` is the Open child above
- target: replace any length-`L` row-circuit walk between vertices of a bounded, irredundant, strictly feasible `n`-row `d`-polytope (`d ≥ 4`) by an edge/stay walk of length at most `C*(n+d)^k*L` for absolute constants `C,k`.

The replacement need not visit the circuit walk's nonvertex checkpoints. Do not create a cyclic child through `balanced_polynomial_bound`, and do not promote a one-step reformulation as a smaller theorem unless the parent implication is genuinely stronger and compiles without a dependency cycle.

## Closed foundations not to redo

- The Santos / linear-Hirsch counterexample chain is Prove2Me **Proved**, including `spindle_one_step_axis`, `strong_dstep_spindle`, and `santos_counterexample`.
- `Hirsch.cubic_circuit_walk_bound` (`9b9a6f06-d05d-41ba-980f-04b905e67562`) is **Proved** and the recovered source gives an explicit `17*n^3` circuit-walk bound.
- Common-face normalization is kernel-checked: a common face can be represented by a bounded, irredundant, strictly feasible row model with both endpoint coordinates extreme.
- The same common-face model can carry the recovered explicit cubic row-circuit walk and the ambient excess/neutral-rank-defect certificate. Circuit-walk existence is therefore not the remaining bottleneck; circuit-to-edge refinement is.

## Latest Prove2Me 0.10.0 results

### `Hirsch.maximal_row_circuit_step_common_face_bound`

- theorem ID `bfea4b5b-106a-4e52-8297-b8138ca0a294`
- submission ID `6fa5d295-7b3e-4463-a823-b9933a67ed70`
- verdict **ACCEPTED** / live status **Proved**
- standalone SHA-256 `ad1bcdc39d8a8f3dd0993b1af9262647ba27f87b3abf5f9a17b9345993b6cd12`

For a maximal row-circuit step `x → y` in an `n`-row presentation in dimension `d`, if the same H-polyhedron has any reference extreme vertex,

```text
commonFaceDim(x,y) + d ≤ n + commonFaceDim(x,x).
```

Neither `x` nor `y` is assumed to be a vertex. Maximality gives a destination-tight blocking row and a strict drop from the step carrier to the destination self-carrier. The internal progress form is

```text
commonFaceDim(y,y) + d + 1 ≤ n + commonFaceDim(x,x).
```

### `Hirsch.row_circuit_step_swap_iff_tight_blockers`

- theorem ID `bd9710b8-067a-4ce6-8ab9-1f6f763133b7`
- submission ID `641acc00-19d4-41ba-93b3-8893e7e94c0b`
- verdict **ACCEPTED** / live status **Proved**
- standalone SHA-256 `49103bd1d83928d2c28b903ed79ec2b098ca9fd55eaf5af491bd128071de2e5e`

For maximal row-circuit steps `x → y → z`, set `w = x + (z-y)`. The reordered pair `x → w → z` consists of maximal row-circuit steps **iff** `w` is feasible and each reordered segment has a nonzero row that is tight at its destination and increases strictly along that segment. The two row supports may overlap. This formalizes the full tight-blocker characterization; it is not merely finite-test evidence anymore.

Verification/publication receipt: `research/CIRCUIT_STEP_PUBLICATION_RECEIPT_2026-09-10.md`. Frozen publication source `2ef303016d5edbed0bb339fc7341b4f019ada400`; source/standalone gate `34553646058`; successful authenticated 0.10.0 publication run `34555207789`, receipt artifact `10182563828`.

## Other recent public / Proved structural results

### Sharp vertex-to-vertex circuit localization

`Hirsch.row_circuit_common_face_dimension_bound`
- theorem `f0e79793-711b-4ada-b276-b4eab1fd0fe8`
- for vertex endpoints with row-circuit displacement:
  `2 * commonFaceDim(u,v) + d ≤ n + 1`.

`Hirsch.balanced_row_circuit_vertices_share_tight_row`
- theorem `73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454`
- when `n=2d` and `d≥2`, a vertex row-circuit pair shares a nonzero tight describing row.

### Circuit neutral rank / row-presentation defect

- `Hirsch.row_circuit_common_face_neutral_rank` — `2caa4fd8-0241-4671-b675-531d935970b9`
- `Hirsch.row_circuit_common_face_selected_row_defect_budget` — `3a03179f-7d55-45e7-89bb-a8a13020f396`
- `Hirsch.row_circuit_common_face_subpresentation_excess_defect` — `6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11`

Internally, `PolynomialCommonFaceMinimalSubpresentation.lean` proves the least equivalent original-row presentation count `M_min` satisfies a matching excess/defect charge. Keep this explicitly a **row-presentation** theorem; equality with an abstract geometric facet count is not formalized and is not needed for the current dynamic routing experiments.

### Carrier-to-edge recognition

`Hirsch.row_circuit_step_adj_of_common_face_dim_le_one` is public **Proved**. Internally the active-neutral defect of a nonstationary displacement is exactly `commonFaceDim - 1`; zero defect therefore recognizes the one-dimensional carrier case in which a maximal circuit step leaving a vertex is already an edge.

### Rank-sensitive face covers

All four are public **Proved**:

- `Hirsch.weighted_geodesic_face_cover_diameter_bound` — theorem `7815b37c-dab5-42b8-a1ed-fbb08d1eab5b`
- `Hirsch.tight_rows_outside_subspace_cardinality_bound` — `27bd88d2-6943-4ca3-abbd-170264c17b98`
- `Hirsch.weighted_cover_improvement_requires_smaller_child` — `599aaead-0333-4d91-8bc5-d7e3e8b9831a`
- `Hirsch.rank_selected_row_face_diameter_bound` — `76cdff62-bb43-4758-a1ed-980ce0ec5230`

These prove useful incidence/rank certificates **and** the recursive-averaging barrier: a polynomial gain cannot come solely from averaging children that themselves cost essentially their vertex count. A genuinely cheaper geometric child/routing bound is still required.

### Clipping / repair toolkit

`Hirsch.simultaneous_clipping_diameter_of_compact_outer` (`75d26f37-e0bd-4d73-9128-688fe7d5a80c`) and `Hirsch.simultaneous_clip_diameter_of_exterior_cap` are Proved. They are conditional on intrinsic cut-face budgets and therefore do not themselves close edge refinement.

## What the newest step results change

The earlier nonvertex localization bound contained both source- and target-checkpoint face dimensions. Maximality now removes the target term from the **step-carrier** bound. This is a real global-routing resource: every maximal circuit step exposes a new destination blocker and its destination self-face is strictly smaller than the step carrier.

However, neither of the following follows automatically:

1. self-face dimension is monotone along an arbitrary multi-step circuit walk;
2. locally legal swaps can be ordered so that total common-carrier graph cost is polynomial.

The exact coupled-family / polygon regressions remain mandatory: commuting directions can still have large carriers in every order, so “more swaps are legal” is not itself a proof of polynomial edge refinement.

## Active work — do not duplicate

As of this update, active unmerged work is already exploring the **excess-two moment-slice / portal** direction:

- PR #78 `Formalize excess-two moment-slice portal geometry`
- PR #79 verification child for its support-face theorem.

Treat these as active research, not established results until their gates finish. Before starting another portal/moment-slice proof, inspect those PRs and reuse or supersede them explicitly.

The next global direction after that work is to combine the new maximal-step progress inequality with whole-walk accounting: identify a potential/rank budget or compatible portal selection whose total cost is polynomial across all circuit steps, rather than bounding each carrier independently by an unknown graph diameter.

## Verification discipline

Evidence levels are distinct:

1. exact Python/regression checks = finite computational evidence;
2. Lean build + axiom audit = kernel/source evidence;
3. independently flattened `solution.lean` + Prove2Me **ACCEPTED / Proved** = public platform evidence.

Only level 3 establishes public `Proved`. Publication/audit credentials remain outside Git in repository secret `PROVE2ME_API_KEY` and are sent only to `https://prove2.me/api/v1` with redirects disabled.

The permanent publication audit is being updated for **0.10.0** and must continue to require the `d≥4` theorem above to remain exactly Open. The public workspace documentation was still advertising 0.9.9 when the server upgrade was first observed, so live authenticated version checks remain mandatory.

## Mandatory counterexample regressions

Before large new routing claims, test against at least:

- maximal-circuit carrier hexagon / polygon examples;
- coupled commuting-direction ordering obstruction;
- exact 4D/5D Dantzig 2-face-bridge examples;
- crossing polygon/cycle and Boolean-cube repair obstructions;
- moving-facet intersection-loss sweep;
- 5D incidence-vs-order cost example;
- balanced cyclic-polar cost barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions.

Do not infer graph-distance control merely from small support count, small common-face dimension, low defect, temporal overlap, or ambient circuit status.
