# Exact selected-support accounting after #200

## Status and provenance

Base: `f3fd2f098f62db10a83b8282be6be6611a82a44a`, the merge of #200.
Lean candidate: `Solutions/PolynomialExactSelectedSupport.lean`.
This file and its transitive axiom printouts have **not been Lean-compiled**.
No new theorem or discussion has been submitted to Prove2Me in this continuation.
Do not mark the candidate proved, publish it, or merge it before the local gate.

The existing verified ingredients are #189's disjoint-row saving, #190's
chordless support counting, #193's carrier tradeoff, and #200's actual deferred
clipping certificate. The new argument preserves their exact selected path and
portal pairs; it does not introduce a whole-face route assumption or a new open
child. It is a distinct follow-up to #199/#200, not another maximal-support
assembly.

## The stronger pointwise inequality

Write `e = n-d`, let `S` be the actual selected cut labels, and let `r = |S|`.
For `i in S`, let `deg_S(i)` count its neighbors **in S** in the parent-vertex
region intersection graph. Let `delta_i` be the minimum-presentation excess of
the common carrier of the actual entry/exit pair charged on cut i.

Then

```
delta_i + r <= e + 1 + deg_S(i).                 (1)
```

Proof under the same bounded-parent, injective row-label, closed extreme-face,
and tight nonzero current-row hypotheses as #193: the blocked selected labels
are exactly i and its selected neighbors. There are exactly `1 + deg_S(i)` of
them because a simple graph has no loop. The other `r-1-deg_S(i)` selected row
faces are disjoint from face i, by the compact face-portal theorem. Their rows
are therefore strict on the whole common carrier. The already established
strict-row saving gives

```
delta_i + (r-1-deg_S(i)) <= e.
```

The nonneighbor/blocked partition gives (1), without truncated subtraction.
Chordlessness is not needed for (1) itself. It is used afterward to ensure
`deg_S(i) <= 2` and that the selected graph is a disjoint union of paths.

The previous `delta_i + (r-3) <= e` throws away whether the actual cut has zero,
one, or two selected neighbors. Non-cut neighboring labels must not be charged
as selected neighbors.

## New routable support regimes

Put `g = e-r`. If every actually selected cut satisfies

```
g + deg_S(i) <= 2,                              (2)
```

then (1) gives `delta_i <= 3`. The existing small-excess theorem supplies an
ordinary parent-edge route at exact cost delta_i. The SAME certificate's
callback assembles these routes at cost

```
D + sum_i delta_i <= D + 3r.
```

The Lean candidate includes this end-to-end certificate theorem with
`SmallExcessHpolyBound` explicit, so it does not import a local target placeholder.
It returns both the exact additive route and the safe bound on its sum.
For target-cone certificates D is 1.

Condition (2) includes three cases, not just maximal support:

| Used support | Additional selected-graph condition | Consequence |
|---|---|---|
| r=e | degree at most two, automatic on the chosen chordless path | recovers maximal support |
| r=e-1 | degree at most one: isolated cuts and two-cut components | all calls have excess at most three |
| r=e-2 | degree zero: all selected cuts are isolated | all calls have excess at most three |

Thus at deficit one an unresolved excess-at-least-four carrier MUST be an
internal vertex of a run of at least three consecutive selected cuts; its
excess is at most four. At deficit two, an isolated selected cut is always easy.
These are necessary conditions for an unresolved call, not evidence that any
such call has large actual distance.

## Exact summed resource and boundary cases

For a simple chordless path, let c be the number of nonempty connected
components of the selected induced graph. It is a forest of paths, so
`sum_i deg_S(i) = 2(r-c)`. Summing (1) gives

```
sum_i delta_i + r*r <= r*(e+1) + sum_i deg_S(i),
sum_i delta_i <= r*(e-r+3) - 2c.                 (3)
```

The first, nontruncated summed inequality is included in the Lean candidate.
The forest degree identity and second formula have a complete elementary
argument here and finite regression tests; they are NOT claimed Lean-checked.
When all calls meet (2), (3) also bounds their actual routing cost. Outside
that regime it bounds excesses, NOT distances.

For maximal nonempty support, this improves the mathematical routing budget to
`D + 3e - 2c <= D + 3e - 2`. When r=0, c=0 and the cut cost is zero: use D,
not `D-2`. A single selected cut has degree zero, not two.

## What this does not solve

Even exact endpoint savings do not justify a polynomial recursion on excess.
Four consecutive selected cuts have degrees `[1,2,2,1]`, permitting individual
excess caps `[e-2,e-1,e-1,e-2]`. Treating them as independent calls permits the
numerical majorant

```
T(e) = 1 + 2*T(e-2) + 2*T(e-1),   e >= 4.
```

With T(0..3)=[0,1,2,3], it is already 4,517 at e=10 and 104,655,701 at e=20.
Indeed T(e) >= 2*T(e-1), so this majorant is exponential. No assertion is made
that a polytope realizes this recursion or that its actual diameter is large.
For any fixed positive k, the separate-call power budget
`2*(e-2)^k + 2*(e-1)^k` eventually exceeds `e^k`; endpoint corrections alone
cannot make that scalar induction close. A joint geometric accounting argument
is still required for a uniform global polynomial.

## Reproduction and next action

Finite tests, completed in the current session:

```
python3 scripts/check_exact_selected_support.py
```

All 32,767 selected subsets of paths with at most 14 vertices were checked,
covering 212,993 selected-vertex counting cases and 229,369 support/gap budget
cases (gaps zero through six). Counts include empty selections. Receipt:
`research/EXACT_SELECTED_SUPPORT_CHECK_2026-09-12.json`.
Python syntax compilation also passed. These tests do not verify Lean or the
continuous geometric input.

The current container has no Lean/Lake executable and cannot resolve github.com;
the GitHub connector exposes reads/writes but no workflow-dispatch action.
No speculative Actions run, workflow change, dependency pin change, or credential
operation was made. The deliberately draft PR is blocked on:

1. `lake build Solutions.PolynomialExactSelectedSupport` in the pinned workspace.
2. Inspect every new declaration's transitive `#print axioms`; permit only the
   repository-standard logical axioms, with `hsmall` explicit.
3. Formalize the selected-forest degree sum to obtain (3) in Lean, including r=0.
4. After local green, use the existing final gate once and preserve its receipt.

For further mathematics, localize deficit-one high carriers to the internal
vertices of cut runs and bound their JOINT costs. Do not spend another cycle
reassembling #200, or mistake the sharper excess sum for a distance bound on
high-excess carriers. Polynomial Hirsch and the live high-dimensional leaf
remain unresolved by this candidate.
