# Verified geodesic face bounds and the incidence-only barrier

## Verification and scope

The Lean proof chain at commit `9b8821229b6d9ccb8377f3bb7fee9a79449b67f5`
passed GitHub Actions run `34299235277`, job `102302419114`:

https://github.com/jjoshua2/prove2me-work/actions/runs/34299235277

The runner compiled `Solutions.PolynomialGeodesicFaceTail`, including its
face-cover and reentry-splice dependencies. The audit required ten declarations
and checked eleven axiom reports; every reported axiom was one of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorryAx` was present. The environment
was Lean 4.30.0 with Mathlib pinned to
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The same run reproduced the exact integer hull and exhaustive shortest-path
regression below. The general theorems are Lean-checked; the concrete
five-dimensional hull/graph application is an exact Python certificate,
not a Lean formalization of that hull. This work does not close the global
Polynomial Hirsch theorem and makes no claim of a new Prove2Me submission.

The branch extends `chatgpt/balanced-core-audit` at
`0eebf5d4ab2e8a8733ec45f72140fdbff38647e6`. No global diameter theorem is
imported into the new proof chain. The quantitative geometric assumptions
are explicit in the statements.

## 1. A shortest path has a bounded visit span in each face

Let `w[0],...,w[L]` be a shortest graph path in a parent set `P`. Let `F` be
an extreme face with intrinsic graph diameter at most `B`. If `w[s]` and
`w[t]` lie in `F`, with `s <= t`, then

```
t - s <= B.
```

Indeed, the proved reentry splice replaces the entire intervening subpath
by a face path. The replacement has length `s + B + (L-t)`. Minimality of
`L` gives the inequality. Therefore the path has at most `B+1` vertices in
`F`, even when it leaves and re-enters `F` between visits.

This does not assert that shortest paths stay inside a face, or that a
simultaneously non-revisiting path exists for all faces. Those stronger
properties are not needed.

Lean declarations in `Solutions/PolynomialGeodesicFaceCover.lean`:

- `HirschFaceSplice.shortest_face_visit_span_le`
- `HirschFaceSplice.shortest_face_visit_card_le`

## 2. An incidence-only face-cover bound

For a finite family of extreme faces `F_i`, suppose each has diameter budget
`B_i` and every parent vertex lies in at least `q > 0` of them. Double-counting
incidences between faces and shortest-path vertices gives

```
q * (L+1) <= sum_i (B_i+1).
```

Graph connectivity supplies a shortest path without assuming any numerical
parent diameter bound. Hence

```
diam(P) <= floor(sum_i (B_i+1) / q) - 1.
```

The Lean expression uses natural-number division and truncated subtraction,
including empty and zero-length boundary cases.

Lean declarations:

- `HirschFaceSplice.shortest_face_cover_budget`
- `HirschFaceSplice.diamLE_of_face_cover`

This is a reusable bound, but optimizing its face weights alone can lose
substantial information about the order of visits.

## 3. A stronger order-sensitive tail bound

Suppose every selected face has diameter at most `B`. For each starting
vertex `u`, let `T(u)` contain every parent vertex that shares no selected
face with `u`, and suppose `|T(u)| <= K`.

Then

```
diam(P) <= B + K.
```

To prove this, consider a shortest path from `u`. Any vertex at index `j>B`
can share no selected face with `u`: otherwise applying the visit-span bound
at indices `0,j` would give `j<=B`. Thus every vertex after index `B` belongs
to `T(u)`. A shortest path never repeats a vertex, so that tail has at most
`K` vertices. Its length is exactly `L-B` when `L>B`.

Unlike the incidence bound, this uses the ordering of all visits relative
to the start. The selected face family need not be finite. The finite set
`T(u)` is an explicit hypothesis; its existence with a small bound is not
silently assumed.

Lean declarations in `Solutions/PolynomialGeodesicFaceTail.lean`:

- `HirschFaceSplice.shortest_no_repeat_of_le`
- `HirschFaceSplice.shortest_face_disjoint_tail_budget`
- `HirschFaceSplice.diamLE_of_disjoint_face_tail_bound`

## 4. Exact comparison on the five-dimensional bridge counterexample

The input coordinates come from
`research/SelectableTwoFaceBridgeCounterexampleD5.md` at commit
`4b09066a5e7a68e664790d56f4e11d24cf9475ee`. The new regression embeds those
coordinates and the expected hull facets, so it does not need that branch
or an external data download to run.

The polar is a simple five-dimensional polytope with ten facets, forty
vertices, and one hundred edges. The exact regression establishes:

| Quantity | Value |
|---|---:|
| Actual graph diameter | 5 |
| Intrinsic diameter of every facet | 4 |
| Facets through each vertex | 5 |
| Sum of facet diameter plus one | 50 |
| Incidence-only upper bound | 9 |
| Maximum number of vertices sharing no facet with a fixed vertex | 1 |
| Ordered-tail upper bound | 5 |

The bound `B+K=4+1=5` is therefore sharp here. It does not need the false
claim that a selected low-ridge facet must admit a two-face bridge to the
target. The regression also rechecks that bridge failure in both
orientations for the designated Dantzig pair.

### The gap cannot be repaired merely by optimizing fractional face weights

There are 290 nonempty proper faces. Give each face `F` cost
`diam(F)+1`, using its exact intrinsic diameter. A fractional cover assigns
nonnegative weights to faces so that each vertex has total covering weight
at least one. Its incidence-only path bound is total cost minus one.

An exact dual certificate proves that the minimum possible cost is **10**,
so the best resulting diameter bound remains **9**, even when all proper
faces and arbitrary nonnegative fractional weights are allowed.

Primal vertices are labelled by their five tight-row indices. Assign unit
dual weight to the following ten vertices and zero to the others:

```
01239 01279 01345 02468 04678
12567 13459 23789 35678 45689
```

For every one of the 290 proper faces, the exact checker verifies

```
number of selected vertices in F <= diam(F)+1.
```

Consequently any fractional cover has cost at least ten by double-counting
these selected vertices. Conversely, weight `1/5` on each of the ten facets
covers every vertex and has cost `10*(1/5)*5=10`. Lower and upper bounds
match exactly. This certificate uses no floating-point linear-programming
result at verification time.

This is a limitation of this specific incidence-only bound, not a lower
bound of nine on the actual graph diameter and not a limitation of every
possible face-based argument.

### Exhaustive checks

`scripts/test_geodesic_face_cover.py` uses Python's standard library only.
It checks all 252 candidate hull facets by 1,260 integer determinants with
fraction-free elimination and exact-division assertions. It reconstructs
the complete graph and all proper-face graphs, then checks all 2,209
shortest paths for unordered endpoint pairs, including zero-length paths.
There are 22,090 facet-visit checks. No shortest paths are sampled or
truncated. The tail assertions are also checked on every enumerated path.

## 5. What remains for a polynomial result

The ordered-tail theorem is a verified implication, not a proof that every
instance has polynomially small `B+K`. We still need a suitable family of
faces whose intrinsic diameter budgets and face-disjoint vertex classes
are quantitatively controlled, or a stronger amortized argument replacing
the uniform `B` maximum.

One cannot close that gap by treating a lower-dimensional facet as an
exactly balanced instance: a facet of a `(d,2d)` presentation may retain
`2d-1` inequalities in dimension `d-1`, which is one more than
`2(d-1)`. A complete recursion must track both dimension and retained
inequality count, including redundancy, instead of assuming balance is
preserved.

The concrete lesson from the exact example is narrower and useful:
incidence totals alone lose information that the order-sensitive tail
argument retains. Further work should exploit that ordering while proving,
rather than assuming, the remaining budget bounds.

## 6. Other repairs completed in this continuation

The effective-row branch now passes at commit
`33a41277ac556413177c7a3be093fd94f55fa572`, run `34298577481`.
Its previous failure was a single-line grep rejecting a valid line-wrapped
axiom report, not a mathematical error. The replacement audit parses
complete reports, rejects nonstandard axioms and `sorryAx`, and requires
all requested declarations to be present.

The sparse-face induction branch now passes at commit
`36272885e05b99c07992531d7e9990680c626d31`, run `34298688055`.
The source-neighbor lemma incorrectly applied an equality as a function
after negation normalization. The proof now uses that equality directly;
its workflow also uses the robust axiom-report audit. These are conditional
d-step and obstruction results, not a global polynomial bound.

## Reproduce from the verified repository commit

In a separate worktree of this repository:

```sh
git worktree add --detach ../prove2me-face-verified 9b8821229b6d9ccb8377f3bb7fee9a79449b67f5
cd ../prove2me-face-verified
python3 scripts/test_geodesic_face_cover.py
~/.elan/bin/lake exe cache get
set -o pipefail
~/.elan/bin/lake build Solutions.PolynomialGeodesicFaceTail 2>&1 | tee face-geodesic.log
python3 scripts/check_lean_axiom_log.py face-geodesic.log \
  HirschFaceSplice.splice_reentry_through_extreme_face \
  HirschFaceSplice.splice_reentry_no_growth \
  HirschFaceSplice.splice_reentry_cost_at_most_face_diameter \
  HirschFaceSplice.shortest_face_visit_span_le \
  HirschFaceSplice.shortest_face_visit_card_le \
  HirschFaceSplice.shortest_face_cover_budget \
  HirschFaceSplice.diamLE_of_face_cover \
  HirschFaceSplice.shortest_no_repeat_of_le \
  HirschFaceSplice.shortest_face_disjoint_tail_budget \
  HirschFaceSplice.diamLE_of_disjoint_face_tail_bound
```

The later commit adding this note changes documentation only; the proof and
regression commit above is the one actually verified by the cited run.
