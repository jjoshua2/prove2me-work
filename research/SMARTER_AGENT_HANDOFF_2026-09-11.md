# Smarter-agent handoff: Polynomial Hirsch useful frontier — 2026-09-11

This note is a research handoff, not a claim that the Polynomial Hirsch
Conjecture is solved. It reconciles the current GitHub state with the latest
authenticated Prove2Me receipts and identifies work that still changes the
frontier rather than repackaging already-settled lemmas.

Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Repo: `jjoshua2/prove2me-work`.

## 1. Live/public state to take as fixed

The mission root remains Open in the latest authenticated mission sync:

- `Hirsch.polynomial_hirsch_conjecture`
  (`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`).

The central d>=4 circuit-to-edge theorem also remained Open immediately before
and after the newest carrier publication:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`).

Other named Open frontiers from the synchronized board are the general
circuit-to-edge theorem `099c6686-560c-48fc-b2c2-18b6a620a06e`, the h>=6
common-face leaf `87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`, and ridge-visible
access `5f309362-bbda-4dea-806f-20b4e2712a2d`.

All six curated historical mission milestones are Proved.

Two public Prove2Me results now matter especially for the current route:

1. `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
   (`12426807-9602-4014-bd5e-c69fb43f4cb6`, accepted proof
   `59736803-0e9d-40bb-875d-7ca66b9ccd45`): every bounded n-row H-polyhedron
   with `n <= d+3` satisfies `DiamLE P (n-d)`.
2. `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
   (`ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
   `b9d5af5b-51d3-48dd-b008-a365a18b053e`): in a bounded parent with
   `n <= d+2`, every common carrier based at a feasible checkpoint has
   intrinsic diameter at most two; the other checkpoint may be arbitrary.

The latter was authenticated live Proved in the publication transaction. The
first submission was WA only because the generated declaration was namespaced;
the corrected root-level `solution` reused the same theorem ID and was
accepted. See
`EXCESS_TWO_COMMON_CARRIER_PUBLICATION_RECEIPT_2026-09-11.md`.

## 2. What GitHub has already completed — do not redo it

### A. Minimum common-face row count -> diameter two

`Solutions/PolynomialCommonFaceSmallExcessDiameter.lean` contains
`commonFace_diamLE_two_of_minCount_le_dim_add_two`.

For bounded parent H-polytopes and parent-vertex endpoints it proves

```text
commonFaceMinSubpresentationCount a b u v <= commonFaceDim a b u v + 2
  -> DiamLE (commonFace a b u v) 2.
```

This uses the small-excess H-polyhedron theorem as an explicit logical premise,
so the local kernel evidence does not pretend a local public-theorem stub is an
unconditional proof.

### B. Arbitrary-checkpoint low-excess carrier interface

`Solutions/PolynomialCommonFaceExcessTwoCarrier.lean` is stronger for future
composition. Its key declarations are:

```text
commonFace_diamLE_two_of_subpresentation_at_most
commonFace_has_subpresentation_dim_add_two_of_rows_le_dim_add_two
commonFace_diamLE_two_of_rows_le_dim_add_two
```

The first theorem is the important interface: if the common carrier's
coordinate H-polyhedron admits *some equivalent subpresentation* with at most
`h+2` rows, where `h = commonFaceDim`, then the carrier has intrinsic diameter
<=2. It is set-level and does not require endpoint vertices.

The second says global parent excess <=2 supplies such a subpresentation for
any feasible source checkpoint. The third combines them.

### C. Whole-walk routing through nonvertex checkpoints

`Solutions/PolynomialExcessTwoWholeWalkRouting.lean` is merged and
kernel-audited. Frozen source `2935f42d255029dcbc337c953dbb364d71ef1c94`,
Actions run `34629152760`, job `103361465979`: build successful, 120 transitive
axiom reports checked, required declarations standard logical axioms only.

It proves:

```text
feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two
rowCircuitWalk_edge_route_two_mul_of_rows_le_dim_add_two
```

Thus, when the parent itself has `n<=d+2`, any feasible sequence of length L
with parent-vertex endpoints has an ordinary parent edge/stay route of length
`2L`. Interior checkpoints may be nonvertices. Circuit structure is not needed
for this composition.

This is not globally strong — the direct low-excess theorem already bounds the
whole parent — but it verifies the exact nonvertex-checkpoint composition we
need once low excess is established *locally*.

### D. Generic carrier-budget router

`Solutions/PolynomialCircuitCarrierRouting.lean` was formerly labelled
candidate-only, but the whole-walk verification build compiled it successfully.
The important theorem is

```text
route_of_feasible_commonFace_carrier_budgets
```

which takes arbitrary per-step intrinsic carrier budgets `B : Fin L -> Nat`
and returns a parent edge/stay route with cost `sum_i B_i`.

Its source comment also notes a potentially important optimization: the
underlying face-cover theorem can index **distinct carriers** rather than
occurrences, so repeated carriers need not automatically be paid repeatedly.

### E. Nonvertex checkpoint localization is already verified

Do not trust the stale “candidate, not yet compiled” header in
`Solutions/PolynomialCircuitCheckpointLocalization.lean`. The checkpoint
package was kernel-verified at commit
`cd9507f1dc08bfea234e9963707fc68de2d1356f`, Actions run `34550443602`, job
`103112037411`, artifact `10180667590`. Exactly 28 requested declarations
produced 28 fresh axiom reports and all used only `propext`, `Classical.choice`,
and `Quot.sound`; see `research/CircuitCheckpointVerificationReceipt.md`.

The package includes nonvertex checkpoint localization with explicit
source/target nullities and all-neutral direction defect, its row-circuit
specialization, conditional routing by intrinsic carrier budgets, and a
separated-support commutation result.

### F. A cubic circuit walk already exists; circuit-walk construction is not the bottleneck

`Solutions/CircuitPhaseRoute.lean` proves a complete standard-slice phase
argument culminating in

```text
standardCircuitWalk_cubic
standard_cubic_circuit_bound
```

with a padded circuit-walk budget `17*n^3`. The phase machinery uses a finite
progress set and a contracting potential, with at most n strict phase-progress
events. This is useful context, but it solves the **circuit-walk existence**
side, not ordinary graph edge refinement. Do not spend a stronger agent merely
improving the constant/exponent here unless a new edge-refinement connection is
identified.

## 3. First thing a new strong agent should formalize

Search current main/active PRs first. If absent, prove the per-carrier version
of the whole-walk theorem. Do not keep the global `n<=d+2` hypothesis.

A useful target shape is:

```text
theorem feasible_sequence_edge_route_two_mul_of_local_low_excess
    (hsmall : SmallExcessHpolyBound)
    (a : Fin n -> EuclideanSpace R (Fin d)) (b : Fin n -> R)
    (hbd : IsBounded (Hpoly a b))
    (w : Nat -> EuclideanSpace R (Fin d)) (L : Nat)
    (hfeas : forall k <= L, w k in Hpoly a b)
    (h0 : w 0 in extremePoints R (Hpoly a b))
    (hL : w L in extremePoints R (Hpoly a b))
    (hlocal : forall i : Fin L,
      HirschCommonFace.HasSubpresentationAtMost
        (commonFaceA a b (w i) (w (i+1)))
        (commonFaceB a b (w i) (w (i+1)))
        (commonFaceDim a b (w i) (w (i+1)) + 2)) :
    Route (Adj (Hpoly a b)) (2*L) (w 0) (w L)
```

Exact namespaces/types should follow existing files rather than this prose
sketch. A variant taking
`commonFaceMinSubpresentationCount <= commonFaceDim + 2` is also useful where
the minimum count is available.

Proof idea should be almost mechanical:

1. compactness from bounded finite Hpoly;
2. set `B i = 2`;
3. discharge each carrier budget with
   `commonFace_diamLE_two_of_subpresentation_at_most`;
4. apply `route_of_feasible_commonFace_carrier_budgets`;
5. simplify the finite sum to `2*L`.

Why this matters: it creates the exact interface a global proof can feed. The
parent can have arbitrarily large row excess; only selected carriers need be
cheap. It also isolates the true missing mathematics from already-solved
routing plumbing.

This wrapper is deliberately the low-risk first task. The smarter agent should
then spend most of its effort on the next section, not on proliferating more
low-excess corollaries.

## 4. The real problem: control local intrinsic excess along a circuit walk

For a carrier between checkpoints x,y define informally

```text
h = commonFaceDim a b x y
M = commonFaceMinSubpresentationCount a b x y
e = M - h
```

The new low-excess portal handles `e <= 2`. General Polynomial Hirsch now needs
one of the following, or a combination:

- show enough carriers have small e;
- show large-e carriers can be bypassed/reordered;
- show large-e carriers are few under a monotone resource;
- or give a polynomial diameter bound as a function of e that can be summed or
  amortized without a dimension-dependent exponent.

### Strong existing vertex-source inequality

`Solutions/PolynomialCommonFaceMinimalSubpresentation.lean` proves
`rowCircuit_commonFace_minSubpresentation_excess_defect`. At a **vertex source**
and for a circuit displacement, after choosing a minimum effective equivalent
presentation, it gives the exact budget

```text
(M - h) + ((h - 1) - selected_neutral_rank) <= n - d.
```

This is already much better than a loose row-count argument: intrinsic
presentation excess and neutral-rank loss spend the same ambient excess budget.
But general RowCircuitWalk intermediates are not vertices, so it cannot simply
be applied to every step.

### Most promising missing structural lemma

Extend that minimum-subpresentation excess/defect inequality to **nonvertex
checkpoints**. The correction terms should be explicit rather than hidden.

The already-verified `PolynomialCircuitCheckpointLocalization.lean` gives the
right warning/template. For a row circuit when a reference parent vertex exists
it proves

```text
2 * commonFaceDim(x,y) + d
  <= n + commonFaceDim(x,x) + commonFaceDim(y,y) + 1.
```

Source/target self-face nullities are precisely the penalties created by losing
endpoint vertexhood.

A high-value theorem would be a rigorously derived analogue such as

```text
local_intrinsic_excess + local_neutral_defect
  <= ambient_excess + explicit checkpoint-nullity corrections,
```

with the smallest correct corrections. Do **not** assume the exact displayed
shape before deriving it.

If successful, it would connect the minimum-presentation machinery directly to
nonvertex circuit walks and make the `e<=2` portal usable inside high-excess
parents.

### Negative lesson: `excess + defect` alone is not enough

Read `research/OptimalCircuitDefectCompletion.md` before proposing a pure
`B = excess + defect` induction. The repo has kernel-checked row-presentation
specializations and extensive exact finite evidence for a stronger geometric
completion picture. The full genuine-facet completion theorems in that note are
**not all Lean-verified or Prove2Me-Proved**, so do not cite them as theorems.
But they are a serious diagnostic: one can construct/test extensions that
preserve protected graph distances while trading circuit-rank defect exactly
against excess. The note's conclusion is that the resource inequality by itself
need not force strict graph-routing progress.

Therefore a successful induction probably needs an additional ordered resource:
actual portals, blocker order, persistent face intervals, selected low-excess
children, or another geometric certificate — not just a scalar defect budget.

## 5. Potential/amortization ingredients already available

### Maximal-step blocker progress

`Solutions/PolynomialCircuitStepProgress.lean` proves every maximal circuit
step reaches a genuinely new target-tight row increasing along the displacement.
It also proves the target self-carrier is a strict subspace of the step carrier,
and

```text
commonFaceDim(x,y) + d <= n + commonFaceDim(x,x)
commonFaceDim(y,y) + d + 1 <= n + commonFaceDim(x,x).
```

These are useful inequalities, but **self-face dimension is not known to be
monotone along the walk**. Do not build an argument that silently assumes it.

### Exact swap certificate

`Solutions/PolynomialCircuitStepBlockerCharacterization.lean` characterizes
when two already-maximal circuit steps can be swapped. The swapped midpoint
must be feasible and both swapped segments must acquire suitable tight
increasing blockers. This is concrete enough for a phase/reordering theorem,
but there is no blanket commutation theorem.

A plausible research direction is to identify classes of consecutive steps
whose blockers make them safely reorderable, group those steps into phases,
and charge a rank/tight-set increase once per phase.

### Face-preserving checkpoint routing

`Solutions/PolynomialFacePreservingCheckpoints.lean` can round feasible
nonvertex checkpoints to parent vertices while preserving membership in all
chosen closed extreme faces. It has ordinary face-cover and interval-cover
variants. This means a global argument need not literally turn each circuit
checkpoint into a vertex one-by-one; it can cover a sequence by a smaller set
of useful carrier/section faces and pay their budgets.

This suggests studying **persistence intervals** of a carrier or equality
section. If one cheap face contains a long interval of checkpoints, route that
interval once rather than paying every circuit step.

### Rank-sensitive face covers

`Solutions/PolynomialRankSensitiveFaceCover.lean` defines saturated
`faceRowSpan`; selecting a row outside it strictly increases normal rank. Its
averaging theorem discounts rows already in the span.

This is only useful when selected children have genuinely better diameter
bounds. Pure averaging/vertex-counting cannot create a Polynomial Hirsch bound
by itself. The low-excess carrier theorem provides one possible source of
better child bounds; the missing task is to prove enough rank-increasing
children/sections land in such a regime.

### Reuse the old phase machinery conceptually, but do not confuse its target

`CircuitPhaseProgress/Potential/Route` already demonstrate a successful pattern:
identify a finite monotone event set, use a quantitative potential inside a
phase, and permit resets only after a strict event. That is a useful **proof
architecture** for edge-refinement accounting. Its current potential controls
circuit-walk construction in slack space, not graph distance, so it cannot be
reused verbatim as the missing edge theorem.

## 6. Concrete experiment/formalization queue

Priority order for a strong agent:

1. **Anti-duplication check.** Search main and open PRs for the local
   per-carrier whole-walk wrapper.
2. **Formalize that wrapper** if absent. It should be short and gives the
   project a stable target interface.
3. **Do not re-prove checkpoint localization.** Read
   `CircuitCheckpointVerificationReceipt.md`; reuse its verified nonvertex
   inequalities. Re-gate only if changing that source.
4. **Attempt nonvertex minimum-presentation excess/defect.** Reuse the selected
   effective-row machinery rather than inventing a facet API. Start by deriving
   the exact correction terms symbolically from row-set inclusions/nullities.
5. **Falsify first.** Test any proposed scalar potential or correction formula
   on the exact obstruction families and the optimal-defect-completion finite
   models before investing in Lean.
6. **Look for an amortized theorem**, not a per-step universal cheapness claim:
   bound the number of high-e phases, charge distinct/reused carriers once, or
   prove high-e steps force growth in a finite-rank/tight-row/portal resource.
7. **Try an interval version** if per-step accounting is too expensive: prove a
   low-excess or rank-controlled face persists across a maximal block of
   checkpoints, then apply the interval face-cover router once for that block.
8. Only after a genuine new bound exists, connect it to the already checked
   carrier-budget router and the existing cubic circuit-walk theorem. Do not
   spend cycles reconstructing the 17*n^3 circuit walk.

## 7. Counterexample discipline

Before trusting a broad local-to-global claim, test the repository's known
failure modes:

- maximal-circuit carrier polygons/hexagons;
- commuting-direction ordering obstructions;
- exact 4D/5D Dantzig two-face bridges;
- crossing polygon/cycle and Boolean-cube repair obstructions;
- moving-facet intersection loss;
- 5D incidence-vs-order cost;
- balanced cyclic-polar barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions.

Known non-implications: small support count, low carrier dimension, low active
defect, temporal overlap, circuit status, and presentation minimality do not by
themselves imply a short ordinary graph route.

## 8. Publication / collaboration rules

- Keep finite regression evidence, Lean kernel evidence, and Prove2Me
  ACCEPTED/live-Proved status separate.
- Do not register a new Open child that merely restates an existing ancestor or
  the missing global argument.
- For a composition through public Proved theorems, keep explicit logical
  premises in the local audit or use Prove2Me tracked imports; do not call a
  local theorem stub an unconditional axiom-clean proof.
- On Actions cancellation, recover the existing theorem/submission status
  before retrying; do not duplicate registrations or submissions.
- `PROVE2ME_API_KEY` stays outside Git.
- The current main handoff is `STATUS.md`; dated receipts are stronger evidence
  for exact theorem IDs, hashes, run IDs, and acceptance records.

## 9. Bottom line

The project no longer lacks (a) a polynomially short circuit walk, or (b) a way
to turn cheap common carriers into an ordinary edge route through nonvertex
checkpoints. Those two plumbing problems are settled enough to build on.

The live mathematical bottleneck is **why a general polynomially short circuit
walk can be covered by carriers/sections whose intrinsic graph costs have a
polynomially amortizable total**.

A stronger agent should spend its intelligence on that accounting problem —
especially the nonvertex extension of intrinsic presentation-excess/defect and
phase/distinct-carrier/interval amortization — rather than proving another
variant of the already-settled ambient-excess-two case or another circuit-walk
existence theorem.
