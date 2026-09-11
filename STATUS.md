# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 17:59 UTC. Repo: `jjoshua2/prove2me-work`.
Main includes verified intrinsic-excess-two and intrinsic-excess-three routing.
Platform: Prove2Me 0.10.1. Lean: v4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

Detailed continuation map:
`research/SMARTER_AGENT_HANDOFF_2026-09-11.md`.

## Public Prove2Me state

**Polynomial Hirsch is not solved.** Latest authenticated synchronization plus
the later carrier publication give:

- `Hirsch.polynomial_hirsch_conjecture`
  (`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`): Open;
- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`): Open;
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`): Open;
- `Hirsch.common_face_diameter_of_dim_ge_six`
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`): Open;
- `Hirsch.polynomial_access_to_ridge_visible_vertex`
  (`5f309362-bbda-4dea-806f-20b4e2712a2d`): Open.

All six curated historical mission milestones are Proved.

Important public low-excess results:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
   `59736803-0e9d-40bb-875d-7ca66b9ccd45`): every bounded n-row H-polyhedron
   with `n<=d+3` has `DiamLE P (n-d)`.
2. `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
   (`ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
   `b9d5af5b-51d3-48dd-b008-a365a18b053e`): in a bounded parent with
   `n<=d+2`, any common carrier based at a feasible checkpoint has intrinsic
   diameter <=2; the other checkpoint may be arbitrary.

The accepted carrier publication re-read the d>=4 frontier Open and made no
conjectural graph mutation. Receipt:
`research/EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## GitHub state: low-excess routing plumbing is DONE through intrinsic excess 3

### Intrinsic excess <=2

PR #105 is merged. `Solutions/PolynomialIntrinsicExcessTwoWholeWalkRouting.lean`
was verified from frozen source `dc6fea94d21e8cb62db0a1cd066b21696a88f4b9`,
run `34629982502`, job `103364150810`; 123 transitive axiom reports, only
`propext`, `Classical.choice`, `Quot.sound`.

For an arbitrary bounded parent, if each selected consecutive carrier satisfies

```text
M_i := commonFaceMinSubpresentationCount(...) <= h_i + 2,
h_i := commonFaceDim(...),
```

then any feasible length-L checkpoint sequence with parent-vertex endpoints has
a parent edge/stay route of length `2*L`. Intermediate checkpoints may be
nonvertices. Receipt:
`research/INTRINSIC_EXCESS_TWO_WHOLE_WALK_VERIFICATION_2026-09-11.md`.

### Intrinsic excess <=3

The verified reduction is also merged on main at commit
`0b9a329d34b5e288a3e1ee11b4ee898ab0d536a9`.
`Solutions/PolynomialCarrierExcessThreeRouting.lean` was verified from frozen
source `6552ca5edf585354b043e53d2e15218f59b9d688`, run `34630058450`, job
`103364397358`; again 123 reports and only standard logical axioms.

It proves:

```text
M_i <= h_i + 3  ==> intrinsic carrier diameter <= 3,
```

with no checkpoint-vertex requirement, and if every consecutive carrier of a
feasible length-L checkpoint sequence satisfies that condition, the parent has
an edge/stay route of length `3*L`. The ambient parent may have arbitrary row
excess. Receipt:
`research/CARRIER_EXCESS_THREE_ROUTING_VERIFICATION_2026-09-11.md`.

## Other settled infrastructure; do not redo it

- `commonFaceMinSubpresentationCount` and an effective minimum witness exist.
- At a **vertex source** and row-circuit displacement,
  `rowCircuit_commonFace_minSubpresentation_excess_defect` gives
  `(M_min-h)+neutralDefect <= n-d`.
- `route_of_feasible_commonFace_carrier_budgets` composes arbitrary intrinsic
  per-step carrier budgets into a parent graph route.
- Nonvertex checkpoint localization is already kernel-verified: commit
  `cd9507f1dc08bfea234e9963707fc68de2d1356f`, run `34550443602`, job
  `103112037411`; 28 required declarations, standard logical axioms only.
- A cubic circuit walk already exists: `standardCircuitWalk_cubic` /
  `standard_cubic_circuit_bound`, padded budget `17*n^3`. Circuit-walk
  construction is not the current bottleneck.

## True research bottleneck

For a circuit-walk carrier let

```text
h_i = commonFaceDim(...)
M_i = commonFaceMinSubpresentationCount(...)
e_i = M_i - h_i.
```

The checked routing portal now handles every `e_i<=3` carrier at constant cost.
The useful frontier is to control or amortize **`e_i>3`** carriers.

Highest-value structural target: extend the minimum-subpresentation
excess/defect inequality from a vertex source to **nonvertex checkpoints**, with
explicit source/target self-face-nullity corrections. The already verified
checkpoint localization gives the row-circuit template

```text
2*h_i + d <= n + selfDim(source_i) + selfDim(target_i) + 1.
```

Then seek an ordered/persistent amortization invariant showing expensive
carriers cannot recur too often: blocker/rank progress, persistent carrier or
face intervals, distinct-carrier charging, or a phase-reset resource. Do not
assume self-face dimension itself is monotone.

## Negative lesson

Do not expect the scalar resource `excess + neutral-rank defect` alone to force
short graph routes. `research/OptimalCircuitDefectCompletion.md` contains
kernel-checked row-presentation specializations plus exact finite diagnostics in
which defect/excess trade while protected graph distances survive. Its full
genuine-facet completion theorems are not all Lean/Prove2Me proved; keep that
evidence boundary explicit.

Likewise do not infer cheap routing solely from small support, low carrier
dimension, low active defect, temporal overlap, circuit status, or presentation
minimality. Test new global claims against the recorded carrier polygons,
Dantzig bridges, crossing/cube repairs, moving-facet failures, cyclic-polar
barriers, deformed cubes, Q28 scalar-fiber examples, and optimal-defect
completion models.

## Verification discipline

Keep finite evidence, Lean kernel/axiom evidence, and Prove2Me ACCEPTED/live
Proved distinct. Avoid cyclic theorem-graph decompositions and duplicate
registrations/submissions. Credentials stay outside Git in `PROVE2ME_API_KEY`.
