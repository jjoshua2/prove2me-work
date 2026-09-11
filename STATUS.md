# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-10 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Live authenticated platform observed: Prove2Me **0.10.0**.
Lean environment: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed provenance belongs in the
dated files under `research/`; do not infer verification status from branch
names or old notes.

## Executive status

**Polynomial Hirsch is not solved.** The sole formal Open bottleneck remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
- authenticated status **Open** after the latest 0.10.0 publication transaction
- parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`) is a sketch: `d ≤ 3` is the Proved
  Klee child and `d ≥ 4` is the Open child above
- target: replace any length-`L` row-circuit walk between vertices of a bounded,
  irredundant, strictly feasible `n`-row `d`-polytope (`d ≥ 4`) by an edge/stay
  walk of length at most `C*(n+d)^k*L` for absolute constants `C,k`.

The replacement need not visit the circuit walk's nonvertex checkpoints. Do not
create a cyclic child through `balanced_polynomial_bound`, and do not promote a
one-step reformulation as a smaller theorem unless the parent implication is
genuinely stronger and compiles without a dependency cycle.

## Closed foundations not to redo

- The Santos / linear-Hirsch counterexample chain is Prove2Me **Proved**,
  including `spindle_one_step_axis`, `strong_dstep_spindle`, and
  `santos_counterexample`.
- `Hirsch.cubic_circuit_walk_bound`
  (`9b9a6f06-d05d-41ba-980f-04b905e67562`) is **Proved** and the recovered
  source gives an explicit `17*n^3` circuit-walk bound.
- Common-face normalization is kernel-checked: a common face can be represented
  by a bounded, irredundant, strictly feasible row model with both endpoint
  coordinates extreme.
- The same common-face model can carry the recovered explicit cubic row-circuit
  walk and the ambient excess/neutral-rank-defect certificate. Circuit-walk
  existence is therefore not the remaining bottleneck; circuit-to-edge
  refinement is.

## Latest public / Prove2Me-Proved structural results

### Irredundant row-count invariance

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`

- theorem ID `8538150b-8afe-47ad-94b0-d72189b80264`
- submission ID `9194432c-54e2-4e6a-9aaf-d7c27fb9934e`
- verdict **ACCEPTED** / live status **Proved**
- standalone SHA-256
  `33be3fdd17714bc1439b0bef73489c571ae41b14f5b06443c4ab6f85e905af55`

A strictly feasible irredundant `n`-row finite H-presentation is globally
cardinality-minimal: every equivalent finite H-presentation has at least `n`
rows, even if it uses different normals and contains redundant rows, duplicate
rows, or zero-normal tautologies. Boundedness is not required.

Internally, the kernel-checked adapters prove that the existing common-face
`M_min` (least equivalent original-row subpresentation count) equals the row
count of **any** equivalent strictly feasible irredundant coordinate
presentation. This makes the row count presentation-independent in the relevant
full-dimensional coordinate setting. It still does **not** define or count an
abstract geometric facet type.

Receipt:
`research/IRREDUNDANT_ROW_COUNT_PUBLICATION_RECEIPT_2026-09-10.md`.
Source/standalone gate `34559027640`; publication run `34559453698`; receipt
artifact `10183894675`; mission comment
`33f2c225-aae0-458b-8c98-8575c4e453c5`.

### Maximal circuit-step progress and exact swapping

`Hirsch.maximal_row_circuit_step_common_face_bound`

- theorem ID `bfea4b5b-106a-4e52-8297-b8138ca0a294`
- submission ID `6fa5d295-7b3e-4463-a823-b9933a67ed70`
- **ACCEPTED / Proved**

For a maximal row-circuit step `x → y` in an `n`-row presentation in dimension
`d`, if the same H-polyhedron has a reference extreme vertex,

```text
commonFaceDim(x,y) + d ≤ n + commonFaceDim(x,x)
```

and internally the destination self-carrier satisfies the strict progress form

```text
commonFaceDim(y,y) + d + 1 ≤ n + commonFaceDim(x,x).
```

`Hirsch.row_circuit_step_swap_iff_tight_blockers`

- theorem ID `bd9710b8-067a-4ce6-8ab9-1f6f763133b7`
- submission ID `641acc00-19d4-41ba-93b3-8893e7e94c0b`
- **ACCEPTED / Proved**

For maximal steps `x → y → z`, writing `w = x + (z-y)`, the reordered pair
`x → w → z` consists of maximal circuit steps iff `w` is feasible and each
reordered segment has a destination-tight blocker increasing along that
segment. This is an exact characterization, but legal local swaps do not by
themselves give a polynomial global ordering.

Receipt: `research/CIRCUIT_STEP_PUBLICATION_RECEIPT_2026-09-10.md`.

## Other public / Proved toolkit

### Sharp circuit localization and row-presentation defect

- `Hirsch.row_circuit_common_face_dimension_bound`
  (`f0e79793-711b-4ada-b276-b4eab1fd0fe8`): for vertex endpoints with a
  row-circuit displacement,
  `2 * commonFaceDim(u,v) + d ≤ n + 1`.
- `Hirsch.balanced_row_circuit_vertices_share_tight_row`
  (`73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454`): when `n=2d`, `d≥2`, a vertex
  row-circuit pair shares a nonzero tight describing row.
- `Hirsch.row_circuit_common_face_neutral_rank`
  (`2caa4fd8-0241-4671-b675-531d935970b9`).
- `Hirsch.row_circuit_common_face_selected_row_defect_budget`
  (`3a03179f-7d55-45e7-89bb-a8a13020f396`).
- `Hirsch.row_circuit_common_face_subpresentation_excess_defect`
  (`6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11`).

The minimum-presentation excess/defect theorem is kernel-checked internally.
The new row-count invariance result removes dependence on the particular
strictly feasible irredundant coordinate presentation, but it does not make
circuit status or neutral rank invariant under arbitrary row deletion.

### Carrier-to-edge recognition

`Hirsch.row_circuit_step_adj_of_common_face_dim_le_one` is public **Proved**.
Zero active-neutral defect recognizes the one-dimensional carrier case in which
a maximal circuit step leaving a vertex is already an edge.

### Rank-sensitive face covers

All four are public **Proved**:

- `Hirsch.weighted_geodesic_face_cover_diameter_bound`
- `Hirsch.tight_rows_outside_subspace_cardinality_bound`
- `Hirsch.weighted_cover_improvement_requires_smaller_child`
- `Hirsch.rank_selected_row_face_diameter_bound`

They provide incidence/rank certificates and formalize the recursive-averaging
barrier: polynomial improvement cannot come only from averaging children that
cost essentially their own vertex count. A genuinely cheaper geometric child
or routing bound is still required.

### Clipping / repair toolkit

`Hirsch.simultaneous_clipping_diameter_of_compact_outer` and
`Hirsch.simultaneous_clip_diameter_of_exterior_cap` are public **Proved**.
They remain conditional on intrinsic cut-face budgets and therefore do not
close edge refinement.

## New kernel-verified excess-two portal geometry — not separately published

PRs #81 and #82 are merged. The normalized excess-two moment-slice development
is kernel-checked through shared-index adjacency and pair-to-pair routing.
Receipt: `research/EXCESS_TWO_SHARED_ADJACENCY_VERIFICATION_2026-09-10.md`.

Verified declarations include:

- `HirschExcessTwo.momentSlice_convex`
- exact three-index support-carrier segment descriptions
- `HirschExcessTwo.pairPoint_adj_shared_low`
- `HirschExcessTwo.pairPoint_adj_shared_high`
- `HirschExcessTwo.pairPoint_two_step_route`.

For low/high pair vertices, sharing a low or high index gives an actual edge,
and arbitrary pair vertices have the canonical padded route

```text
pair(i,j) → pair(i,l) → pair(k,l).
```

Thus the **pair-vertex subgraph** has padded diameter at most two. This is
kernel/source evidence, not a separate Prove2Me publication. It does not yet
classify every extreme point of the normalized moment slice, so it is not yet a
full diameter-two theorem for the whole slice.

## Highest-value next work

1. Complete the normalized excess-two slice: prove every extreme point is
   either an equal-moment singleton or a low/high pair point; then prove the
   singleton-to-pair / singleton-to-singleton adjacency cases and conclude full
   padded graph diameter at most two.
2. Only after the full excess-two slice theorem is established, isolate the
   exact hypotheses under which a common circuit carrier reduces to that model.
   Do not silently assume arbitrary carriers are moment slices.
3. Combine maximal-step progress, presentation-independent row count, and
   portal geometry with **whole-walk accounting**. The missing global argument
   must bound total edge-routing cost across all circuit steps, not merely each
   carrier independently.
4. Investigate potentials that mix self-face dimension, row excess, neutral
   defect, destination blockers, and compatible portal reuse. The newest
   theorems give several real resources, but none is yet known to decrease in a
   way that pays all graph-routing cost.
5. Keep `polynomial_edge_refinement_of_circuit_walks_dim_ge_four` as the sole
   Open child. Create a new decomposition only if every child is demonstrably
   smaller and the parent implication compiles without an ancestor cycle.

## Verification discipline

Evidence levels remain distinct:

1. exact Python/regression checks = finite computational evidence;
2. Lean build + axiom audit = kernel/source evidence;
3. independently audited `solution.lean` + Prove2Me **ACCEPTED / Proved** =
   public platform evidence.

Only level 3 establishes public `Proved`. Publication/audit credentials remain
outside Git in repository secret `PROVE2ME_API_KEY` and are sent only to
`https://prove2.me/api/v1` with redirects disabled.

The authenticated row-count publication transaction checked the `d≥4` frontier
before and after and found it exactly **Open**, with no graph modification and
no new conjectural children.

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

Do not infer graph-distance control merely from small support count, small
common-face dimension, low defect, temporal overlap, ambient circuit status, or
presentation-minimality by itself.
