# Smarter-agent handoff: Polynomial Hirsch useful frontier — 2026-09-11

This is the research handoff for the next strong agent. It reconciles the
current GitHub development with the latest authenticated Prove2Me receipts and
tries to keep the next iteration away from already-settled plumbing.

Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Repo: `jjoshua2/prove2me-work`.

## 1. Live Prove2Me state

Polynomial Hirsch is still Open. The latest authenticated board synchronization
and the later common-carrier publication transaction agree on the important
frontier:

- root `Hirsch.polynomial_hirsch_conjecture`
  (`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`): Open;
- general circuit-to-edge refinement
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`): Open;
- d>=4 circuit-to-edge refinement
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`): Open;
- common-face h>=6 leaf
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`): Open;
- ridge-visible access
  (`5f309362-bbda-4dea-806f-20b4e2712a2d`): Open.

All six curated historical mission milestones were authenticated Proved.
`research/PROVE2ME_HIRSCH_SYNC_2026-09-11.md` is the durable board-sync receipt.

Two public Prove2Me results now supply the low-excess portal:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
   `59736803-0e9d-40bb-875d-7ca66b9ccd45`): every bounded n-row H-polyhedron
   with `n <= d+3` has `DiamLE P (n-d)`. Redundant/zero rows and degenerate sets
   are allowed.
2. `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
   (`ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
   `b9d5af5b-51d3-48dd-b008-a365a18b053e`): in a bounded parent with
   `n<=d+2`, every common carrier based at a feasible checkpoint has intrinsic
   diameter <=2; the other checkpoint may be arbitrary.

The second publication posted mission reference comment
`b3feca04-21d1-481a-989f-76638bb21122` and re-read the d>=4 frontier Open after
acceptance. No duplicate/cyclic Open theorem was created. See
`EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## 2. Settled GitHub infrastructure — do not redo it

### Intrinsic minimum presentation count

`Solutions/PolynomialCommonFaceMinimalSubpresentation.lean` defines the least
number `M_min` of original common-face coordinate inequalities needed for an
equivalent presentation and produces an effective minimum witness.

At a **vertex source** and row-circuit displacement it proves

```text
(M_min - h) + ((h - 1) - selectedNeutralRank) <= n - d,
```

where `h = commonFaceDim`. This is
`rowCircuit_commonFace_minSubpresentation_excess_defect`.

### Low-excess carrier diameter

`Solutions/PolynomialCommonFaceSmallExcessDiameter.lean` and
`Solutions/PolynomialCommonFaceExcessTwoCarrier.lean` establish the checked
transport from an equivalent low-row coordinate presentation to intrinsic
common-carrier graph diameter. In particular, arbitrary checkpoints need not be
vertices for the set-level adapter
`commonFace_diamLE_two_of_subpresentation_at_most`.

### Arbitrary carrier-budget routing

`Solutions/PolynomialCircuitCarrierRouting.lean` contains
`route_of_feasible_commonFace_carrier_budgets`: if consecutive carriers of a
feasible checkpoint sequence have intrinsic budgets `B_i`, parent-vertex
endpoints can be connected by a parent edge/stay route with total cost
`sum_i B_i`. This module has now compiled in multiple later verification gates;
its old candidate-only comment is stale.

The surrounding face/interval routing machinery can also charge a selected
family of faces/carriers, including interval covers, rather than forcing one
payment per original circuit step.

### Nonvertex checkpoint localization

This package is already kernel-verified. Do not recompile it merely to establish
its status. `research/CircuitCheckpointVerificationReceipt.md` records commit
`cd9507f1dc08bfea234e9963707fc68de2d1356f`, run `34550443602`, job
`103112037411`, artifact `10180667590`: 28 required declarations, 28 fresh axiom
reports, only `propext`, `Classical.choice`, `Quot.sound`.

Its row-circuit specialization gives, with the reference-parent assumptions in
that file,

```text
2 * commonFaceDim(x,y) + d
  <= n + commonFaceDim(x,x) + commonFaceDim(y,y) + 1.
```

The source/target self-face nullities are the important nonvertex correction
terms.

### Cubic circuit-walk existence

`Solutions/CircuitPhaseProgress.lean`, `CircuitPhasePotential.lean`, and
`CircuitPhaseRoute.lean` already implement a successful finite-phase/potential
architecture and culminate in `standardCircuitWalk_cubic` /
`standard_cubic_circuit_bound`, with padded budget `17*n^3`.

That solves the circuit-walk **existence** side. It does not solve ordinary-edge
refinement. Do not spend a stronger agent improving that cubic constant unless
it unlocks a new graph-routing invariant.

## 3. Newly checked local-carrier routing — the easy wrapper is DONE

### Intrinsic excess <=2: merged on main

PR #105 merged `Solutions/PolynomialIntrinsicExcessTwoWholeWalkRouting.lean`.
Frozen source `dc6fea94d21e8cb62db0a1cd066b21696a88f4b9`; run `34629982502`, job
`103364150810`; all 8,514 build jobs succeeded. The axiom checker inspected 123
transitive reports; the three required declarations use only standard logical
axioms.

Checked statements include:

```text
commonFace_has_subpresentation_dim_add_two_of_minCount_le
feasible_sequence_edge_route_two_mul_of_minCounts
rowCircuitWalk_edge_route_two_mul_of_uniform_minCount
```

Crucially the parent may have **arbitrary ambient row excess**. If every selected
consecutive carrier has `M_i <= h_i+2`, a feasible length-L checkpoint sequence
with vertex endpoints has a parent edge/stay route of length `2L`.

Receipt:
`research/INTRINSIC_EXCESS_TWO_WHOLE_WALK_VERIFICATION_2026-09-11.md`.

### Intrinsic excess <=3: kernel-verified branch

PR #106 frozen source `6552ca5edf585354b043e53d2e15218f59b9d688`
passed run `34630058450`, job `103364397358`; again the targeted build succeeded
and the axiom checker inspected 123 transitive reports with only standard
logical axioms for:

```text
commonFace_diamLE_three_of_subpresentation_at_most
commonFace_diamLE_three_of_minCount_le_dim_add_three
feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three
```

So if every consecutive carrier has `M_i <= h_i+3`, the parent route costs at
most `3L`, still with arbitrary ambient row excess and nonvertex intermediate
checkpoints. The second PR commit only records the verification receipt; at the
time of this snapshot PR #106 had not yet been cleanly integrated to main.
Search current PR/main state before doing integration work.

Receipt on the branch:
`research/CARRIER_EXCESS_THREE_ROUTING_VERIFICATION_2026-09-11.md`.

**Therefore do not assign a strong agent another “local excess two/three implies
2L/3L” wrapper. That work is already checked.**

## 4. Actual mathematical bottleneck

For circuit-walk checkpoint pair `(x_i,x_{i+1})`, define

```text
h_i = commonFaceDim(a,b,x_i,x_{i+1})
M_i = commonFaceMinSubpresentationCount(a,b,x_i,x_{i+1})
e_i = M_i - h_i.
```

The existing portal handles `e_i <= 3` at constant graph cost. General
Polynomial Hirsch requires a polynomially amortizable treatment of the steps or
intervals with **`e_i > 3`**.

The most useful next structural result is a **nonvertex analogue of the minimum
subpresentation excess/defect budget**. The vertex-source theorem says

```text
presentation_excess + selected_neutral_defect <= ambient_excess.
```

For nonvertex checkpoints, derive the exact correction terms from active/common
row sets and self-face nullities rather than guessing them. A desired schematic
form is

```text
local presentation excess + local neutral defect
  <= ambient excess + explicit checkpoint-nullity corrections.
```

The verified checkpoint-localization inequality above is evidence for what kind
of corrections must appear. Do not assume this schematic inequality is true
until it has been derived/tested.

## 5. Why a scalar excess/defect bound is probably insufficient

Read `research/OptimalCircuitDefectCompletion.md` before attempting a pure
`B = excess + defect` induction. The row-presentation specializations are
kernel checked and three public defect/excess statements are Prove2Me Proved.
The note also contains extensive exact finite completion diagnostics showing
that circuit-rank defect can be traded against presentation excess while
protected graph distances survive.

The full genuine-facet completion Theorems 1-4 in that note are **not all
Lean-verified or Prove2Me-Proved**; preserve that evidence boundary. But the
finite models are strong counterexample generators and make “the scalar drops,
therefore graph routing gets cheaper” a poor strategy by itself.

A plausible proof needs an **ordered/persistent resource** in addition to the
scalar budget.

## 6. Best directions after the nonvertex excess formula

### A. Blocker/rank phases

`PolynomialCircuitStepProgress.lean` proves every maximal circuit step gains a
genuine target blocking row and that the target self-carrier is a strict
subspace of the step carrier. `PolynomialCircuitStepBlockerCharacterization`
gives an exact certificate for when consecutive maximal steps may be swapped.

Search for a phase invariant in which expensive (`e_i>3`) steps force one of:

- a new independent blocker/normal rank;
- a permanently trapped tight row;
- a safe reordering that moves the step next to a cancellation/cheap carrier;
- or a reset whose count is bounded by a finite rank/tight-row resource.

Do not assume `commonFaceDim(x_i,x_i)` is monotone; it is not currently known to
be.

### B. Distinct-carrier or interval charging

`PolynomialFacePreservingCheckpoints.lean` and interval routing let one replace
nonvertex checkpoints by parent vertices while preserving membership in chosen
closed extreme faces and route an interval through a selected face once.

A potentially better target than per-step cheapness is:

> cover a polynomially long circuit walk by polynomially many intervals whose
> selected carrier/section faces either have `e<=3` or make certified rank/tight
> progress.

This avoids paying repeatedly for the same persistent expensive carrier.

### C. Rank-sensitive low-excess children

`PolynomialRankSensitiveFaceCover.lean` has the right algebra for selecting rows
outside a saturated face-row span and forcing rank growth. Pure averaging does
not help unless the selected child faces have better diameter bounds. The new
`e<=3` carrier portal supplies an actual “better child” class; the missing
lemma is to show that enough rank-increasing children/sections enter that class,
or that failures consume a finite rank resource.

### D. Reuse the old phase architecture, not its literal potential

The existing circuit-walk proof demonstrates a useful design pattern:
finite monotone event set + quantitative contraction within a phase + reset
only after strict progress. Try to build the analogous object for **edge
refinement cost**, perhaps with events defined by new blockers, carrier-row-span
rank, or persistent low-excess sections. The current slack potential itself
controls circuit-walk construction, not graph distance.

## 7. Concrete queue for the next strong agent

1. Search main/open PRs first. PR #105 is already merged; PR #106 has a passed
   source gate and may be integrated concurrently.
2. Derive/test the nonvertex minimum-presentation excess/defect formula. Reuse
   the existing effective-row/minimum-subpresentation API; do not invent a new
   facet-count formalism unless unavoidable.
3. Falsify candidate correction formulas and scalar potentials on the recorded
   exact obstruction/completion families before large Lean work.
4. If the nonvertex formula survives, look for a phase theorem bounding the
   number of `e_i>3` events, or an interval-cover theorem charging each expensive
   carrier/section only polynomially many times.
5. Only then connect the result to `route_of_feasible_commonFace_carrier_budgets`
   / interval face routing and the existing `17*n^3` circuit walk.

A useful intermediate theorem is one that proves **many** or **long persistent
blocks** of carriers have `e<=3`; it need not prove every carrier cheap. That is
already enough to interact with interval covers and rank-progress phases.

## 8. Counterexample discipline

Before trusting a broad local-to-global claim, rerun the repository's known
failure modes:

- maximal-circuit carrier polygons/hexagons;
- commuting-direction ordering obstructions;
- exact 4D/5D Dantzig two-face bridges;
- crossing-cycle and Boolean-cube repair obstructions;
- moving-facet intersection loss;
- 5D incidence-vs-order cost;
- balanced cyclic-polar barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions;
- the optimal-defect-completion finite models.

Known non-implications: small support count, low carrier dimension, low active
defect, temporal overlap, circuit status, and presentation minimality do not by
themselves imply a short ordinary graph route.

## 9. Publication/collaboration discipline

Keep three evidence levels separate:

1. exact finite/regression evidence;
2. Lean kernel + axiom-gate evidence;
3. Prove2Me ACCEPTED / authenticated live Proved.

Do not register cyclic/ancestor-equivalent Open children merely to rename the
missing global theorem. For compositions using an already-public theorem, keep
it as an explicit premise in local audits or use tracked Prove2Me imports; do
not claim a theorem stub is an unconditional kernel proof. After a canceled
publication monitor, recover the existing theorem/submission before retrying.
`PROVE2ME_API_KEY` stays outside Git.

## Bottom line

The project has now crossed two plumbing milestones:

- a polynomially short circuit walk already exists;
- carriers with intrinsic minimum-presentation excess <=3 can already be turned
  into constant-cost ordinary-edge routing, including through nonvertex
  checkpoints in arbitrary-excess parents.

The useful frontier is therefore an **amortized high-intrinsic-excess theorem**.
The strongest agent should focus on how `M_i-h_i>3` can occur along the cubic
circuit walk, what nonvertex correction terms govern it, and which ordered or
persistent resource prevents those expensive carriers from recurring too often.
