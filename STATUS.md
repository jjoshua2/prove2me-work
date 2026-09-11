# Current Prove2Me Polynomial Hirsch frontier

Source continuation updated 2026-09-11 after PR #122.
Repository: `jjoshua2/prove2me-work`.
Lean: v4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first: the old immediate target is finished

The exact reference-free nonvertex minimum-subpresentation theorem was completed
in PR #111. Do not repeat the old next-theorem plan in
`research/NONVERTEX_MIN_SUBPRESENTATION_EXCESS_PLAN_2026-09-11.md` or the older
sections of `research/SMARTER_AGENT_HANDOFF_2026-09-11.md`.

The new continuation note is
`research/CIRCUIT_DELETION_SAVINGS_VERIFICATION_2026-09-11.md`. It records a
sharper universal one-carrier identity, its equality criterion, executed local
Lean verification, and two explicit geometric barriers to naive amortization.

This update distinguishes source progress from platform status. No fresh
authenticated Prove2Me read or submission was made by the deletion-savings
continuation; the public-state receipts below retain their own observation
times. Concurrent publication PRs must be checked independently before claiming
additional platform acceptance.

## Completed source layer: exact nonvertex excess/defect

`Solutions/PolynomialCircuitCheckpointMinSubpresentationDefectBounded.lean`
contains

```text
rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded.
```

For a bounded parent, feasible source x, and ambient row circuit y-x, a minimum
effective common-carrier presentation exists with

```text
(M_min-h) + selectedNeutralDefect <= n-d.
```

No source/target extremality, auxiliary reference vertex, or self-face-nullity
corrections are needed. Frozen source `2d0794c46940cf7be3221c3ce02a117becb7ba4f`
passed run `34632388202`, job `103372091147`. Receipt:
`research/REFERENCE_FREE_CHECKPOINT_DEFECT_VERIFICATION_2026-09-11.md`.

The supporting bounded neutral-rank result from PR #108 is also complete:
neutral kernel is the circuit line; restricted to commonDirection its rank is
exactly h-1. Receipt:
`research/NONVERTEX_BOUNDED_NEUTRAL_RANK_VERIFICATION_2026-09-11.md`.

## New source layer: exact deletion savings, merged PR #122

Merge commit `29910957b47a015937cfd79ffad6d3b5adadcac7`; proof source commit
`d359432b967f77646482d579cf60094fe447e718`.

`Solutions/PolynomialCircuitDeletionSavings.lean` proves four declarations.
For selected effective rows F with h<=|F|, let e=|F|-h and delta be their
restricted neutral-rank defect. Let kappa count surplus disappearing rows,
s count discarded nonneutral effective rows, and tau count neutral deletions
beyond actual independent rank loss. Then

```text
e + delta + kappa + s + tau = n-d,
e + delta + s <= n-d.
```

The old bound e+delta=n-d is saturated if and only if all three savings vanish.
For minimum equivalent presentations, existing witness lemmas give |F|=M_min.
Neither endpoint needs to be a vertex; only source feasibility is assumed.

Verification was LOCAL, using a source-faithful focused-import standalone of
17 modules under the pinned environment, with global autoImplicit=false.
All four transitive axiom reports contain only propext, Classical.choice, and
Quot.sound. A full lake build/separate original-module gate was not completed;
the receipt explains the offline-cache and memory limitations and provides the
reproducible successful standalone command and hashes. No hosted proof workflow
was added. This package is not claimed Prove2Me ACCEPTED/Proved.

Exact rational regressions passed 768 selected-row checks, including 192
minimum cube-carrier cases, four negative controls, and 354 genuine-facet
witnesses. The same JSON data was reproduced on rerun.

## Two barriers now made explicit

1. **High excess need not force savings.** A family with D=2k-1 dimensions and
   N=4k-2=2D genuine facets has a k-cube carrier for a maximal ambient circuit
   diagonal. Its minimum presentation has e=k, delta=k-1, and
   kappa=s=tau=0. Exactly balanced genuine-facet examples were checked for
   k=4,...,12. These examples are easy to route, but invalidate automatic
   savings/progress from high carrier excess.
2. **Static savings do not telescope.** In a corner-truncated cube, a
   linear-length simple Gray-code walk has distinct vertices and carriers, yet
   the same genuine facet supplies s_i=1 repeatedly. The tested walks have
   sum_i s_i>n-d. Distinct-carrier deduplication is therefore not proof that
   these credits are consumed globally.

The universal algebraic identity is Lean-checked. The geometric families have
ordinary explanations and exact finite evidence, not Lean formalizations.
Their constructors and reports are in the new continuation package.

## Existing graph-routing interfaces: reuse, do not repackage

The generic `route_of_feasible_commonFace_carrier_budgets` composes intrinsic
carrier graph budgets into a parent edge/stay route. Face-preserving checkpoint
and interval-routing machinery already handles nonvertex checkpoints.

The low-excess interfaces are complete through excess 3:

- intrinsic M_i<=h_i+2 gives a 2L route (PR #105);
- intrinsic M_i<=h_i+3 gives a 3L route (PR #106);
- `PolynomialCarrierSmallExcessBudgetRouting.lean` preserves exact additive
  certified budgets R_i<=3, with total cost sum_i R_i (PR #107).

Later minimum-excess wrappers reuse the same geometry. Do not spend the next
strong-agent iteration on another low-excess-to-route composition.

## Corrected hard target: actual ordinary-edge cost

The existing circuit construction already gives a walk of length 17*n^3.
Merely proving that the number of expensive carriers is polynomial is therefore
insufficient: their own graph costs remain unbounded by that counting argument.

The missing target is a polynomial bound on TOTAL ORDINARY-EDGE COST, or a
cost-controlled bypass/replacement of hard blocks. A useful recurrence must
quantify both the decrease and its branching/routing cost.

The equality criterion identifies the structure of saturated carriers. Study
whether an actual route-dependent invariant can exploit it: a permanently
consumed row/rank event, a geometric inexpensive bypass, or a persistent face
interval with independently bounded intrinsic cost. Do not assume positive
accounting slack decreases graph distance, self-face dimension is monotone, or
a repeatedly discarded row is a new global resource.

The earlier `research/OptimalCircuitDefectCompletion.md` remains relevant:
its row-presentation specializations are checked, but its full genuine-facet
completion theorems are not all Lean/Prove2Me proved. Keep that boundary.

## Public Prove2Me observations retained from authenticated receipts

The last cited authenticated mission synchronization and carrier publication
reported these Open states; this source update does not claim to refresh them:

- root `58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`;
- general circuit-to-edge refinement `099c6686-560c-48fc-b2c2-18b6a620a06e`;
- d>=4 refinement `73beca40-31bc-42d5-8350-5ec9ac28bd3e`;
- common-face dimension>=6 `87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`;
- ridge-visible access `5f309362-bbda-4dea-806f-20b4e2712a2d`.

All six curated historical milestones were Proved in that sync. See
`research/PROVE2ME_HIRSCH_SYNC_2026-09-11.md`.

Relevant accepted public inputs include:

- `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`, theorem
  `12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
  `59736803-0e9d-40bb-875d-7ca66b9ccd45`: bounded n<=d+3 implies
  DiamLE P (n-d), without irredundancy/strict feasibility.
- `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`, theorem
  `ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
  `b9d5af5b-51d3-48dd-b008-a365a18b053e`: bounded ambient excess<=2 gives
  intrinsic common-carrier diameter<=2 for a feasible source checkpoint.

See the corresponding publication receipts and any newer accepted receipts
before submitting. Source/kernel verification is not platform acceptance.
Avoid duplicate submissions and cyclic/conjectural graph decompositions.
Credentials stay outside Git in `PROVE2ME_API_KEY`.
