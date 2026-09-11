# Smarter-agent handoff: Polynomial Hirsch useful frontier — 2026-09-11

Use this as the starting point for the next strong agent. It incorporates the
latest authenticated Prove2Me synchronization and the intrinsic-excess-two and
intrinsic-excess-three routing results now merged on GitHub.

Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Repo: `jjoshua2/prove2me-work`.

## 1. Live Prove2Me boundary

The conjecture remains unsolved. Latest authenticated status:

- root `Hirsch.polynomial_hirsch_conjecture`
  (`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`): Open;
- general circuit-to-edge refinement
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`): Open;
- d>=4 circuit-to-edge refinement
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`): Open;
- common-face dimension>=6 leaf
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`): Open;
- ridge-visible access
  (`5f309362-bbda-4dea-806f-20b4e2712a2d`): Open.

All six curated historical mission milestones are Proved. The durable board
receipt is `research/PROVE2ME_HIRSCH_SYNC_2026-09-11.md`.

Two public low-excess facts are especially important:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
   `59736803-0e9d-40bb-875d-7ca66b9ccd45`): a bounded n-row H-polyhedron with
   `n<=d+3` has `DiamLE P (n-d)`; no irredundancy/strict-feasibility hypothesis.
2. `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
   (`ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
   `b9d5af5b-51d3-48dd-b008-a365a18b053e`): in a bounded parent with
   `n<=d+2`, any common carrier based at a feasible checkpoint has intrinsic
   diameter<=2; the other checkpoint may be arbitrary.

The second publication posted mission comment
`b3feca04-21d1-481a-989f-76638bb21122`, re-read the d>=4 frontier Open after
acceptance, and made no conjectural graph mutation. Receipt:
`research/EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

Do not create another Prove2Me child merely to restate the still-missing global
edge-refinement argument.

## 2. What is already solved in the repository

### Minimum intrinsic row presentation

`Solutions/PolynomialCommonFaceMinimalSubpresentation.lean` defines
`commonFaceMinSubpresentationCount` (`M_min`) and an effective minimum equivalent
presentation. At a **vertex source** and row-circuit displacement,

```text
(M_min - h) + ((h-1) - selectedNeutralRank) <= n-d,
```

where `h = commonFaceDim`. This is
`rowCircuit_commonFace_minSubpresentation_excess_defect`.

### Generic carrier/face routing

`Solutions/PolynomialCircuitCarrierRouting.lean` has
`route_of_feasible_commonFace_carrier_budgets`: intrinsic carrier budgets
`B_i` for a feasible checkpoint sequence compose to a parent edge/stay route of
cost `sum B_i`.

`PolynomialFacePreservingCheckpoints.lean` plus interval-routing modules allow
one to route using selected faces/carriers over intervals, so a useful global
proof need not pay one carrier occurrence at a time.

### Nonvertex checkpoint localization

Already kernel-verified; do not spend an iteration re-establishing its status.
Receipt `research/CircuitCheckpointVerificationReceipt.md`: commit
`cd9507f1dc08bfea234e9963707fc68de2d1356f`, run `34550443602`, job
`103112037411`; 28 required declarations and only standard logical axioms.

One row-circuit specialization is

```text
2 * commonFaceDim(x,y) + d
  <= n + commonFaceDim(x,x) + commonFaceDim(y,y) + 1.
```

This is the key warning that nonvertex endpoints introduce self-face-nullity
corrections.

### Polynomial circuit walk already exists

`CircuitPhaseProgress/Potential/Route` culminate in
`standardCircuitWalk_cubic` / `standard_cubic_circuit_bound` with padded budget
`17*n^3`. Circuit-walk construction is therefore not the present bottleneck.
The useful analogy is its proof architecture: finite monotone events,
quantitative within-phase progress, and bounded resets.

## 3. Local low-excess edge-refinement portal is now complete through excess 3

### `M_i-h_i <= 2`: merged

PR #105 merged `Solutions/PolynomialIntrinsicExcessTwoWholeWalkRouting.lean`.
Frozen source `dc6fea94d21e8cb62db0a1cd066b21696a88f4b9`, run `34629982502`, job
`103364150810`; 8,514 build jobs succeeded and the axiom checker inspected 123
transitive reports, only `propext`, `Classical.choice`, `Quot.sound`.

For an arbitrary bounded parent, if each selected consecutive carrier has

```text
M_i <= h_i + 2,
```

then a feasible length-L checkpoint sequence with parent-vertex endpoints has a
parent edge/stay route of length `2L`. Intermediate checkpoints may be
nonvertices. There is also a uniform-carrier RowCircuitWalk corollary.

Receipt:
`research/INTRINSIC_EXCESS_TWO_WHOLE_WALK_VERIFICATION_2026-09-11.md`.

### `M_i-h_i <= 3`: merged

Commit `0b9a329d34b5e288a3e1ee11b4ee898ab0d536a9` merged
`Solutions/PolynomialCarrierExcessThreeRouting.lean` plus its receipt. Frozen
source `6552ca5edf585354b043e53d2e15218f59b9d688`, run `34630058450`, job
`103364397358`; 123 transitive reports, only standard logical axioms.

Checked statements:

```text
commonFace_diamLE_three_of_subpresentation_at_most
commonFace_diamLE_three_of_minCount_le_dim_add_three
feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three
```

Thus an arbitrary-parent carrier with minimum equivalent row-presentation excess
<=3 has intrinsic graph diameter<=3, without checkpoint-vertex hypotheses; if
every consecutive carrier of a feasible length-L checkpoint sequence satisfies
that condition, the parent route costs `3L`.

Receipt:
`research/CARRIER_EXCESS_THREE_ROUTING_VERIFICATION_2026-09-11.md`.

**Do not assign the next agent another low-excess-to-2L/3L routing wrapper.**
That plumbing is finished.

## 4. The real problem is now high intrinsic excess

For circuit-walk checkpoint pair `(x_i,x_{i+1})`, write

```text
h_i = commonFaceDim(a,b,x_i,x_{i+1})
M_i = commonFaceMinSubpresentationCount(a,b,x_i,x_{i+1})
e_i = M_i - h_i.
```

The checked portal handles every `e_i<=3` carrier at O(1) graph cost. The useful
frontier is to prove a polynomially amortizable bound for the carriers or
intervals with **`e_i>3`**.

### Highest-value missing structural lemma

Extend the vertex-source minimum-subpresentation excess/defect theorem to
**nonvertex circuit checkpoints**. Derive the correction terms rather than
assuming them. A schematic target is

```text
local presentation excess + local neutral defect
  <= ambient excess + explicit source/target nullity corrections.
```

The verified checkpoint inequality above strongly suggests self-face dimensions
must appear, but it does not by itself prove this schematic formula.

This is the cleanest next way to connect the actual cubic RowCircuitWalk to the
now-complete low-excess carrier portal.

## 5. Do not rely on a scalar excess+defect induction alone

Read `research/OptimalCircuitDefectCompletion.md` first. The row-presentation
specializations are kernel checked; public Prove2Me results include neutral-rank,
selected-row defect budget, and subpresentation excess/defect theorems. The note
also has extensive exact finite completion diagnostics showing one can trade
circuit-rank defect against excess while preserving protected graph distances.

The full genuine-facet completion Theorems 1-4 in that note are **not all
Lean-verified or Prove2Me-Proved**. Preserve that evidence boundary. But the
models are strong evidence that a scalar decrease in `e+defect` does not force a
strict graph-distance improvement.

A successful proof probably needs **order or persistence** in addition to the
scalar budget.

## 6. Best research directions

### Blocker/rank phases

`PolynomialCircuitStepProgress.lean` gives a genuine target blocking row for
every maximal circuit step and strict containment of the target self-carrier in
the step carrier. `PolynomialCircuitStepBlockerCharacterization.lean` gives an
exact swap certificate for consecutive maximal steps.

Try to prove that an expensive `e_i>3` step forces one of a bounded set of
monotone events: new independent blocker rank, permanently retained tight row,
safe reorder/cancellation, or a reset charged to a finite rank/tight-set
resource. Do not assume self-face dimension is monotone.

### Persistent carrier/face intervals

The face-preserving checkpoint and interval-routing machinery makes the
following target attractive:

> cover the cubic circuit walk by polynomially many intervals, each carried by
> a face/section that is either intrinsic-excess<=3 or causes certified rank /
> blocker progress.

This can be much easier than proving every individual carrier cheap, and it
allows repeated/persistent carriers to be paid once per interval rather than
once per step.

### Rank-sensitive low-excess children

`PolynomialRankSensitiveFaceCover.lean` can force normal-rank growth when a row
is selected outside a saturated face-row span. Averaging alone is not enough;
it only helps if selected children really have a better diameter bound. The new
`e<=3` portal gives an actual cheap-child class. Look for a theorem saying that
rank-increasing children eventually enter that class, or failures consume a
finite rank resource.

### Reuse the old phase architecture conceptually

The successful circuit-walk construction already shows how to combine a finite
progress set with a quantitative potential inside phases. Build a new phase
object for **ordinary-edge refinement cost**, with events tied to blockers,
carrier row-span rank, or persistent low-excess sections. Do not simply reuse
the old slack potential: it controls circuit-walk length, not graph distance.

## 7. Suggested next-agent queue

1. Anti-duplication search of current main/open PRs.
2. Derive the nonvertex minimum-presentation excess/defect formula using the
   existing effective-row/minimum-subpresentation API.
3. Before substantial Lean work, falsify candidate correction formulas and
   potentials on the existing exact obstruction and optimal-defect-completion
   families.
4. If the formula survives, seek either:
   - a bound on the number of `e_i>3` phases/events; or
   - an interval/distinct-carrier cover that pays expensive carriers only
     polynomially many times.
5. Compose that result with the already-checked carrier/face routing and the
   existing `17*n^3` circuit walk.

A theorem proving that **many carriers**, or long persistent blocks, have
`e_i<=3` is already useful; it need not make every step cheap.

## 8. Regression/counterexample discipline

Test broad claims against at least the recorded:

- maximal-circuit carrier polygons/hexagons;
- commuting-direction ordering obstructions;
- 4D/5D Dantzig two-face bridges;
- crossing-cycle and Boolean-cube repair examples;
- moving-facet intersection loss;
- 5D incidence-vs-order cost;
- balanced cyclic-polar barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions;
- optimal-defect-completion finite models.

Small support, low carrier dimension, low active defect, temporal overlap,
circuit status, or presentation minimality alone do not imply a short ordinary
graph route.

## 9. Evidence/publication rules

Keep distinct:

1. exact finite evidence;
2. Lean kernel/axiom-gate evidence;
3. Prove2Me ACCEPTED / authenticated live Proved.

Do not create ancestor-equivalent Open children to rename the global gap. For
public compositions, use tracked Prove2Me imports or keep already-public facts
as explicit local premises; do not hide theorem stubs in a claimed axiom-clean
proof. Recover an existing theorem/submission after a canceled monitor before
retrying. Credentials remain outside Git in `PROVE2ME_API_KEY`.

## Bottom line

The project already has a polynomial circuit walk and now has constant-cost
ordinary-edge refinement for every carrier whose intrinsic minimum-presentation
excess is at most three, even with arbitrary ambient parent excess and nonvertex
checkpoints.

The strongest next agent should work on the **amortized high-excess layer**:
understand `M_i-h_i>3` at nonvertex checkpoints and prove that blocker/rank or
carrier/face persistence prevents those expensive carriers from recurring too
often.
