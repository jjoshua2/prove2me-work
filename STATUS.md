# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 17:49 UTC. Repo: `jjoshua2/prove2me-work`.
Main synchronized through `e5f552c5dbe24825a995338016fe3ca3b79d4e6b`.
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
sets, and needs no irredundancy or strict feasibility. In particular n<=d+2
gives diameter <=2.

### Arbitrary-checkpoint common carrier at ambient excess <=2

`Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
(theorem `ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted submission
`b9d5af5b-51d3-48dd-b008-a365a18b053e`) is live **Proved**.
For a bounded n-row parent with n<=d+2, any feasible checkpoint `u`, and
arbitrary `v`, the intrinsic common carrier has padded vertex-edge diameter at
most two. The second checkpoint need not be feasible or a vertex.

Receipt:
`research/EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## Fresh kernel-verified GitHub result: whole-walk composition

`Solutions/PolynomialExcessTwoWholeWalkRouting.lean` is merged on main.
Frozen source `2935f42d255029dcbc337c953dbb364d71ef1c94` passed Actions run
`34629152760`, job `103361465979`. The build checked 120 transitive axiom
reports; the three required declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

For a bounded parent with n<=d+2, **any feasible length-L checkpoint sequence**
whose endpoints are parent vertices can be replaced by a parent edge/stay
route of length `2*L`. Interior checkpoints need not be vertices and the input
sequence need not be a circuit walk. A `RowCircuitWalk` corollary follows.

This is structurally useful but is not a new global Polynomial Hirsch bound:
when the *whole parent* already has excess <=2, the direct small-excess theorem
is stronger. Its value is that the nonvertex-checkpoint routing composition is
now checked and can be reused once low excess is established locally per
carrier.

Receipt:
`research/EXCESS_TWO_WHOLE_WALK_ROUTING_VERIFICATION_2026-09-11.md`.

## The minimum-row adapter is DONE; do not redo it

`Solutions/PolynomialCommonFaceSmallExcessDiameter.lean` already proves

```text
commonFaceMinSubpresentationCount(a,b,u,v) <= commonFaceDim(a,b,u,v)+2
  ==> DiamLE (commonFace a b u v) 2
```

for bounded parent polytopes with vertex endpoints, using the public small-
excess theorem as an explicit premise.

`Solutions/PolynomialCommonFaceExcessTwoCarrier.lean` strengthens the useful
set-level interface: **any** common carrier admitting an equivalent coordinate
subpresentation with at most `h+2` rows has intrinsic diameter <=2. It also
proves ambient n<=d+2 supplies such a presentation for every feasible source
checkpoint.

So the old handoff item “connect the minimum common-face row count” is closed.

## Immediate useful next theorem

Remove the *global* `n<=d+2` assumption from the whole-walk theorem and replace
it by a **per-step intrinsic carrier** assumption. A natural target is:

```text
for every i < L,
  commonFaceMinSubpresentationCount(a,b,w_i,w_{i+1})
    <= commonFaceDim(a,b,w_i,w_{i+1}) + 2
```

(or the equivalent `HasSubpresentationAtMost` witness) implies a parent
edge/stay route of length `2*L`.

This should be a short composition of
`commonFace_diamLE_two_of_subpresentation_at_most` with
`route_of_feasible_commonFace_carrier_budgets`. Search for concurrent work
before adding it. It is the right reusable interface even though it does not
by itself prove that general circuit carriers satisfy the premise.

## True research bottleneck after that wrapper

Let `M_i` be the minimum equivalent row-presentation count of the i-th common
carrier and `h_i` its intrinsic dimension. The general problem is to control
or amortize carriers with large intrinsic excess `M_i-h_i`.

Useful existing ingredients:

- `rowCircuit_commonFace_minSubpresentation_excess_defect`: at a **vertex
  source**, intrinsic presentation excess plus neutral-rank defect is bounded by
  ambient row excess `n-d`;
- `rowCircuitStep_exists_target_blocking_row`: every maximal circuit step gains
  a genuine target blocking row;
- checkpoint localization bounds carrier dimension for nonvertex endpoints in
  terms of source/target self-face nullities;
- exact two-step blocker/swap certificates;
- `route_of_feasible_commonFace_carrier_budgets` and the face/interval routing
  machinery can charge a finite family of carriers rather than being tied to
  the original nonvertex checkpoints;
- rank-sensitive face-cover tools give progress only when their selected child
  faces already have genuinely improved diameter bounds.

The most valuable structural lemma is likely a **nonvertex-checkpoint analogue
of the minimum-subpresentation excess/defect budget**, with explicit correction
terms for source/target self-face dimensions. Then seek a phase/potential
argument showing expensive carriers, correction terms, or resets cannot recur
too often. Do not assume self-face dimension itself is monotone.

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
