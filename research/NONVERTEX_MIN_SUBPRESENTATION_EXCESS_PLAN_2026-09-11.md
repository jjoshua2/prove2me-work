# Next strong-agent target: exact nonvertex minimum-subpresentation excess/defect

Date: 2026-09-11. Repo: `jjoshua2/prove2me-work`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This note is a proof plan, not a claim that the final theorem below is already
verified. It records a dependency audit performed after the bounded nonvertex
neutral-rank result merged. The audit suggests the existing vertex-source
minimum-subpresentation excess/defect theorem may generalize to a merely
feasible source in a bounded parent **with the same right-hand side `n-d` and no
self-face correction terms**.

## 1. New verified ingredient

PR #108 merged `Solutions/PolynomialCircuitBoundedNeutralRank.lean`.
Frozen source `1922d706523c5253bbe32079e6e6ab71444b3538` passed Actions run
`34630740596`, job `103366669600`; all 8,488 build jobs succeeded. The axiom
audit checked 20 transitive reports and the four required declarations use only
`propext`, `Classical.choice`, and `Quot.sound`:

```text
rows_ge_dimension_of_bounded
rowCircuit_neutral_kernel_eq_span_of_bounded
rowCircuit_neutral_rank_eq_dim_sub_one_of_bounded
rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
```

For a bounded parent, feasible source `u`, and ambient row circuit `v-u`, the
ambient neutral rows restricted to the common-direction space have rank exactly

```text
commonFaceDim(a,b,u,v) - 1.
```

No source-vertex or target-vertex hypothesis is needed. Durable receipt:
`research/NONVERTEX_BOUNDED_NEUTRAL_RANK_VERIFICATION_2026-09-11.md`.

## 2. Existing target and where vertexhood is actually used

The current theorem

```text
rowCircuit_commonFace_minSubpresentation_excess_defect
```

in `Solutions/PolynomialCommonFaceMinimalSubpresentation.lean` assumes

```text
hu : u ∈ extremePoints ℝ (Hpoly a b)
```

and concludes, for a minimum equivalent effective coordinate presentation with
`M = commonFaceMinSubpresentationCount a b u v`, an exact budget of the form

```text
(M - h) + selectedNeutralDefect <= n - d,
h = commonFaceDim a b u v.
```

A source audit shows the vertex hypothesis enters through two layers.

### Use A — neutral rank / ambient row count

`rowCircuit_selectedEffectiveRows_defect_budget` currently calls the older
vertex-based theorem
`rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one`, and
the final excess rearrangement obtains `d<=n` from
`rows_ge_dimension_of_vertex`.

**This layer is now removable.** PR #108 supplies exact bounded/feasible
replacements for both facts.

The rest of the selected-row defect proof is set/rank/cardinality accounting:

- `F ⊆ effectiveRowsOnSubspace`;
- deletion loses at most the number of deleted neutral rows;
- `commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim`;
- finite-set subtraction/cardinality arithmetic.

None of those steps intrinsically needs `u` to be a vertex.

### Use B — proving a minimum effective presentation really has at least `h` rows

`commonFace_minSubpresentation_effective_witness` currently obtains

```text
0 ∈ extremePoints ℝ (common-face coordinate Hpoly)
```

from `commonFace_coord_zero_extreme ... hu`, then uses
`commonFace_subpresentation_effectiveRows_card_ge_dim` to derive `h<=M`.

But two observations make ambient vertexhood look unnecessary here.

1. **Deleting zero-normal selected rows needs only zero feasibility, not zero
   extremality.** `effective_subpresentation_preserves_hpoly` assumes only

   ```text
   0 ∈ Hpoly A B.
   ```

   For a merely feasible source `hu : u ∈ Hpoly a b`, this should follow
   directly from `commonFace_u_mem a b u v hu` and
   `mem_commonFace_coord_iff a b u v 0`, because `commonFacePoint ... 0 = u`.

2. **The lower bound `h<=M` can come from boundedness instead of a coordinate
   vertex.** `commonFace_coord_bounded a b u v hbd` says the full coordinate
   H-polyhedron is bounded whenever the parent is bounded. An equivalent
   minimum M-row subpresentation is therefore bounded too, and zero feasibility
   makes it nonempty. Applying the newly verified
   `rows_ge_dimension_of_bounded` to that M-row H-polyhedron in ambient
   dimension `h` should give exactly `h<=M`.

So the old vertex-based `commonFace_subpresentation_effectiveRows_card_ge_dim`
need not be generalized in place; the minimum-presentation theorem can bypass
it with boundedness.

## 3. Strong candidate theorem

Try the strongest clean statement first rather than adding nullity correction
terms prematurely:

```text
theorem rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded
    (a : Fin n -> EuclideanSpace ℝ (Fin d)) (b : Fin n -> ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (v-u)) :
    let M := commonFaceMinSubpresentationCount a b u v
    ∃ e : Fin M ↪ Fin n,
      <same equivalent-presentation witness> ∧
      let F := <same effective selected-row set>
      F.card = M ∧
      (M - commonFaceDim a b u v) +
        ((commonFaceDim a b u v - 1) -
          <same selected neutral rank>)
        <= n-d
```

Exact syntax should copy the existing theorem. The point is only the changed
hypotheses: bounded parent + feasible source instead of source extreme point.

If this theorem fails, isolate the exact failed implication before weakening it
to a self-face-corrected version. The current dependency audit gives a concrete
reason to expect the exact theorem to work.

## 4. Suggested Lean decomposition

Keep each step independently auditable.

### A. Zero coordinate is feasible from source feasibility

Prove a tiny helper, or inline it:

```text
commonFace_coord_zero_mem_of_feasible
  (hu : u ∈ Hpoly a b) :
  0 ∈ Hpoly (commonFaceA a b u v) (commonFaceB a b u v).
```

Proof: `mem_commonFace_coord_iff` + `commonFace_u_mem`; simplify
`commonFacePoint ... 0`.

### B. Effective minimum witness under boundedness/feasibility

Generalize or add a sibling of
`commonFace_minSubpresentation_effective_witness` with hypotheses

```text
hbd : IsBounded (Hpoly a b)
hu  : u ∈ Hpoly a b
```

and the same useful output `F.card=M ∧ h<=M`.

For `F.card=M`, reuse the current minimality argument verbatim after replacing
the old extreme-point-derived `hzero` by helper A.

For `h<=M`:

1. take the exact minimum M-row witness from
   `commonFaceMinSubpresentation_spec`;
2. transfer boundedness from the full coordinate model via
   `commonFace_coord_bounded` and the presentation equality;
3. transfer zero feasibility via the same equality;
4. instantiate `rows_ge_dimension_of_bounded` with ambient dimension
   `h=commonFaceDim` and row count M.

This avoids proving any new vertex/extreme-point geometry.

### C. Bounded/feasible selected-row defect budget

Add a sibling of `rowCircuit_selectedEffectiveRows_defect_budget` replacing

```text
hu : u ∈ extremePoints ...
```

by `hbd` and `hu : u ∈ Hpoly ...`.

The only substantive replacement should be the `hfull` proof: use

```text
rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
```

from PR #108. The deletion/rank/cardinality remainder should stay unchanged.

### D. Bounded/feasible excess form

Generalize `rowCircuit_selectedEffectiveRows_excess_defect` similarly. Obtain
`d<=n` from `rows_ge_dimension_of_bounded a b hbd u hu`, then reuse `omega`.

### E. Minimum-presentation theorem

Combine B + D exactly as the current vertex theorem does.

Gate the final theorem and all new helpers with `#print axioms`; require only
`propext`, `Classical.choice`, `Quot.sound`.

## 5. Why this is strategically better than the earlier nullity-correction plan

The already-verified nonvertex checkpoint localization bound

```text
2*h + d <= n + selfDim(u) + selfDim(v) + 1
```

is useful for dimension localization, but it does **not** imply that the
minimum-presentation excess/defect theorem itself needs self-face corrections.
That earlier expectation came from losing vertex-based rank arguments. PR #108
shows the decisive circuit neutral rank is still exactly `h-1` under boundedness
and source feasibility.

If the exact theorem above verifies, every step of a feasible row-circuit walk
inherits the same local resource inequality previously available only from a
vertex source:

```text
e_i + defect_i <= n-d,
where e_i = M_i-h_i.
```

That still does **not** solve Polynomial Hirsch: ambient excess `n-d` can be
large, and `research/OptimalCircuitDefectCompletion.md` gives strong evidence
that this scalar resource alone cannot force short graph distance. But it would
remove a major semantic mismatch between the actual nonvertex circuit walk and
the intrinsic carrier accounting.

## 6. What to do after the exact nonvertex theorem

The low-excess graph-routing side is already stronger than a uniform 3L bound.
`Solutions/PolynomialCarrierSmallExcessBudgetRouting.lean` is merged: if step i
has an explicit equivalent carrier presentation with row excess `R_i<=3`, its
intrinsic graph cost is at most exactly `R_i`, and total parent route cost is
`sum_i R_i`.

So after the nonvertex resource theorem, concentrate on **amortization of steps
with `e_i>3`**, not more low-excess wrappers. Most promising forms remain:

- a blocker/rank phase theorem showing expensive steps force finitely many
  monotone events;
- a persistent face/carrier interval cover that pays a repeated expensive
  carrier once per long block;
- a rank-sensitive child/section theorem forcing enough selected pieces into
  the `e<=3` cheap class;
- a combined potential with an ordered/persistent component, not just scalar
  `e+defect`.

Reuse `CircuitPhaseProgress/Potential/Route` as a proof-architecture example,
not as the literal graph-distance potential.

## 7. Coordination / anti-duplication

At the time of this note:

- PR #108 has merged, so do not redo bounded nonvertex neutral rank;
- variable `R_i<=3` additive routing has also merged, so do not redo that
  accounting wrapper;
- PR #109 is public-composition/packaging work around the small-carrier-excess
  theorem, not the high-value structural frontier.

Search current main/open PRs again before starting. Keep Prove2Me publication
status separate from local kernel verification; the general d>=4 edge-refinement
and root Polynomial Hirsch theorems remain Open in the latest authenticated
receipts.
