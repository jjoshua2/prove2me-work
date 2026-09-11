# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 17:57 UTC. Repo: `jjoshua2/prove2me-work`.
Main synchronized through `ed4218bf02f2b43dcef400ecad10ea1804fca96c` at this snapshot.
Platform: Prove2Me 0.10.1. Lean: v4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed provenance belongs in the
2026-09-11 receipts under `research/`; the current research map is
`research/SMARTER_AGENT_HANDOFF_2026-09-11.md`.

## Executive status

**Polynomial Hirsch is not solved.** The root
`Hirsch.polynomial_hirsch_conjecture`
(`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`) was authenticated Open in the mission
sync. The high-dimensional circuit-to-edge frontier
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) was authenticated Open immediately
before and after the latest common-carrier publication. The general refinement
`099c6686-560c-48fc-b2c2-18b6a620a06e`, common-face h>=6 leaf
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, and ridge-visible access
`5f309362-bbda-4dea-806f-20b4e2712a2d` also remain research frontiers unless a
newer authenticated receipt says otherwise.

All six curated historical mission milestones are Proved.

## Fresh public Prove2Me results

### Small ambient row excess

`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
(theorem `12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted submission
`59736803-0e9d-40bb-875d-7ca66b9ccd45`) is live **Proved**:

```text
bounded P = Hpoly a b, n <= d+3  ==>  DiamLE P (n-d).
```

This includes redundant rows, zero normals, empty/lower-dimensional feasible
sets, and needs no irredundancy or strict feasibility.

### Arbitrary-checkpoint common carrier at ambient excess <=2

`Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
(theorem `ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted submission
`b9d5af5b-51d3-48dd-b008-a365a18b053e`) is live **Proved**.
For a bounded n-row parent with n<=d+2, any feasible checkpoint `u`, and
arbitrary `v`, the intrinsic common carrier has padded vertex-edge diameter at
most two. The second checkpoint need not be feasible or a vertex.

Receipt:
`research/EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## GitHub routing plumbing now complete through local intrinsic excess two

`Solutions/PolynomialExcessTwoWholeWalkRouting.lean` is merged and proves that
for a bounded parent with global n<=d+2, any feasible length-L checkpoint
sequence with parent-vertex endpoints has a parent edge/stay route of length
`2*L`. Interior checkpoints may be nonvertices. Verification: frozen source
`2935f42d255029dcbc337c953dbb364d71ef1c94`, run `34629152760`, job
`103361465979`.

More importantly, `Solutions/PolynomialIntrinsicExcessTwoWholeWalkRouting.lean`
is now merged on main by PR #105. Frozen source
`dc6fea94d21e8cb62db0a1cd066b21696a88f4b9` passed run `34629982502`, job
`103364150810`; the audit checked 123 transitive reports and the three required
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

It removes the global low-excess hypothesis: for an arbitrary bounded parent,
if **each selected consecutive carrier** satisfies

```text
M_i := commonFaceMinSubpresentationCount(...) <= h_i + 2,
h_i := commonFaceDim(...),
```

then the full feasible checkpoint sequence refines to a parent edge/stay route
of length `2*L`. A uniform-carrier `RowCircuitWalk` corollary is also checked.

Receipt:
`research/INTRINSIC_EXCESS_TWO_WHOLE_WALK_VERIFICATION_2026-09-11.md`.

## Intrinsic excess three is also kernel-verified; do not duplicate it

PR #106 / frozen source `6552ca5edf585354b043e53d2e15218f59b9d688`
passed run `34630058450`, job `103364397358`. The audit checked 123 transitive
reports and only standard logical axioms for:

```text
commonFace_diamLE_three_of_subpresentation_at_most
commonFace_diamLE_three_of_minCount_le_dim_add_three
feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three
```

Thus an arbitrary-parent carrier with minimum equivalent row-presentation
excess at most three has intrinsic diameter at most three, and a feasible
length-L checkpoint sequence whose every consecutive carrier satisfies that
condition has a parent edge/stay route of length `3*L`.

At this snapshot PR #106 is still a verification branch (its second commit only
records the verification receipt); search current main/PR state before doing
integration work. Durable receipt on that branch:
`research/CARRIER_EXCESS_THREE_ROUTING_VERIFICATION_2026-09-11.md`.

## Other settled infrastructure; do not redo it

- The minimum-row adapter is done: `M_min <= h+2` gives carrier diameter <=2.
- `route_of_feasible_commonFace_carrier_budgets` turns arbitrary per-step
  intrinsic carrier budgets into a parent route with the summed budget.
- Nonvertex checkpoint localization is already kernel-verified: commit
  `cd9507f1dc08bfea234e9963707fc68de2d1356f`, run `34550443602`, job
  `103112037411`; 28 required declarations, standard logical axioms only.
- A cubic circuit walk already exists via `standardCircuitWalk_cubic` /
  `standard_cubic_circuit_bound` with padded budget `17*n^3`. Circuit-walk
  construction is not the current bottleneck.

## True research bottleneck

Let `M_i` be the minimum equivalent row-presentation count of the i-th common
carrier and `h_i` its intrinsic dimension. The checked/public plumbing now
handles carriers with `M_i-h_i <= 3` at constant cost. The useful frontier is
therefore **not another low-excess routing wrapper**. It is to control or
amortize the carriers with intrinsic excess `M_i-h_i > 3` along a polynomially
short circuit walk.

Most promising structural target:

1. Extend `rowCircuit_commonFace_minSubpresentation_excess_defect` from a
   **vertex source** to nonvertex circuit checkpoints, with explicit correction
   terms for source/target self-face nullities.
2. Combine that with an ordered/monotone resource so expensive carriers cannot
   recur too often: blocker progress, rank growth, persistent carrier/face
   intervals, distinct-carrier charging, or a phase-reset invariant.
3. Feed the resulting per-carrier/interval costs into the already checked
   carrier/face routing machinery.

The verified nonvertex localization inequality is a useful template:

```text
2*h_i + d <= n + selfDim(source_i) + selfDim(target_i) + 1
```

for the row-circuit specialization with a reference parent vertex. Do not
assume self-face dimension itself is monotone.

## Important negative lesson

Do not try to finish the proof from the scalar resource `excess + neutral-rank
defect` alone. `research/OptimalCircuitDefectCompletion.md` contains
kernel-checked row-presentation specializations plus strong exact finite
diagnostics showing that defect can be traded against excess while protected
graph distances survive. Its full genuine-facet completion theorems are not all
Lean/Prove2Me proved, so respect that evidence boundary, but the examples make
pure scalar-defect induction a poor bet.

A successful global argument likely needs **order/persistence**: actual
portals, blocker order, carrier intervals, selected low-excess children, or
another finite monotone event set.

## Do not waste a stronger agent on these false shortcuts

Do not assume arbitrary circuit carriers have excess <=2 or <=3. Do not infer
small graph diameter solely from small support, low carrier dimension, low
active defect, temporal overlap, ambient circuit status, or presentation
minimality. Do not create an ancestor-equivalent/cyclic Open theorem merely to
rename the missing global argument. Do not pay a full facet diameter at every
dimension recursively: that makes the exponent dimension-dependent.

Before a new broad routing claim, rerun the repository's recorded obstruction
families: maximal-circuit carrier polygons/hexagons; commuting-direction order
obstructions; 4D/5D Dantzig two-face bridges; crossing-cycle and Boolean-cube
repair examples; moving-facet intersection loss; 5D incidence-vs-order cost;
balanced cyclic-polar barriers; deformed cubes/single-step universality; and
Q28 scalar-fiber constructions.

## Verification discipline

Distinguish exact finite regressions, Lean kernel/axiom evidence, and Prove2Me
ACCEPTED/live Proved. A local theorem with an explicit premise matching a public
Proved theorem is not itself an unconditional platform publication. Recover an
existing registration/submission after a canceled monitor before retrying.
Credentials stay outside Git in `PROVE2ME_API_KEY`.
