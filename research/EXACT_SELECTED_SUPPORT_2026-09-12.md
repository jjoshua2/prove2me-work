# Exact selected-support accounting after #200

## Status and provenance

The #201 candidate is now Lean-verified after adding `classical` to its finite
cardinality proof and correcting `Finset.card_insert_of_notMem`. Integration
also preserves both #202 Lean sources unchanged from commit
`4797a18206c63e761628e556d5ca4bd1eef3c169` and adds the run-count proof and a
classical fixed-excess descent theorem. Frozen integrated proof source:
`117709458ec4b071dc846cd8443feea19ca2669b`.

`lake build Solutions.PolynomialSelectedRunBudgets Solutions.PolynomialFixedExcessLarman`
passes. The transitive axiom audit checks 30 required declarations and 406 total
reports, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
[Exact source hashes and local receipt](verification/2026-09-12-exact-support/local-verification.json).
The single final hosted build and its axiom audit also passed on that source.
The standalone classical fixed-excess theorem is **Proved** on Prove2Me
([49576ed3](https://prove2.me/theorems/49576ed3-5185-4951-9215-43283ef6169e),
accepted submission `cd24addc-446f-4d16-b814-85315057c98f`).
The selected-run and clipping assemblies retain local/GitHub verification status;
that server verdict concerns the separate fixed-excess statement only.

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

The compiled Lean source includes this end-to-end certificate theorem with
`SmallExcessHpolyBound` explicit, so it does not import a local target placeholder.
It returns both the exact additive route and the safe bound on its sum.
For target-cone certificates D is 1.

Condition (2) includes three cases, not just maximal support:

| Used support | Additional selected-graph condition | Consequence |
|---|---|---|
| r=e | degree at most two, automatic on the chosen chordless path | recovers maximal support |
| r=e-1 | degree at most one: isolated cuts and two-cut components | all calls have excess at most three |
| r=e-2 | degree zero: all selected cuts are isolated | all calls have excess at most three |

At deficit one, a carrier above the small-excess cutoff MUST have excess
exactly four and selected degree two. This localization is now Lean-checked.
Such a call is nevertheless routed by the fixed-deficit theorem below; it
is no longer a remaining distance obligation.

## Exact summed resource and boundary cases

For a simple chordless path, let c be the number of nonempty connected
components of the selected induced graph. It is a forest of paths, so
`sum_i deg_S(i) = 2(r-c)`. Summing (1) gives

```
sum_i delta_i + r*r <= r*(e+1) + sum_i deg_S(i),
sum_i delta_i <= r*(e-r+3) - 2c.                 (3)
```

Both summed inequalities and the degree identity are now Lean-checked in
`PolynomialSelectedRunBudgets.lean`, including application to the certificate's
actual list of carrier pairs. The implementation counts run starts: a selected
label with no earlier selected neighbor in the fixed path order. Chordlessness
makes this the usual selected-run count. No separate identification with a
Mathlib connected-component quotient is asserted. The nontruncated formal
identity is `sum(degrees)+2c=2r`, including empty selections.

When all calls meet (2), the formal route has padded length
`D+(r*(g+3)-2c)`. Outside that regime (3) bounds excesses; the following distinct
argument is what supplies an edge-distance bound.

For maximal nonempty support, this improves the mathematical routing budget to
`D + 3e - 2c <= D + 3e - 2`. When r=0, c=0 and the cut cost is zero: use D,
not `D-2`. A single selected cut has degree zero, not two.

## Every fixed support deficit now has an actual edge bound

The independently prepared #202 sources compile unchanged. For the smallest
common carrier of two parent vertices, its intrinsic dimension h and minimum
row count M obey `2h<=M`. Thus `h<=delta=M-h` and `M<=2delta`. This uses the
existing separated-endpoint row count on the irredundant intrinsic model.
Vertex hypotheses are essential. In particular a carrier of dimension at least
six has excess at least six; the excess-four/five cases cannot be that residual.

The support estimate gives `delta_i<=g+3`. Larman applied to the MINIMUM
intrinsic presentation gives, for every actual selected carrier,

```
diam(carrier_i) <= 2*(g+3)*2^g.
```

The SAME certificate assembles an ordinary-edge route of length

```
D + 2*(g+3)*2^g*r.
```

This closes deficit one at `D+16r` and deficit two at `D+40r` with no restriction
on selected-cut adjacency. Every fixed deficit is linear in r. The target-rooted
wrapper chooses the certificate and its deficit for each vertex pair with D=1.
The only diameter input to this route theorem is the already-Proved Larman
proposition. It does not require an induction hypothesis on open carriers.

There is also a general classical theorem in `PolynomialFixedExcessLarman.lean`:
any bounded n-row H-polyhedron with `n<=d+E` has padded diameter at most
`2*E*2^(E-3)`, with natural subtraction. For `d>E`, nonzero tight-row counting
finds a common equality section; deleting one row and dimension preserves the
excess cap and costs no access steps. At `d<=E`, at most 2E rows remain, so Larman
applies. This includes redundant, zero, empty, and lower-dimensional descriptions.
It yields the same conservative constants without the vertex-carrier size lemma.
Its classical source is [Santos (2012), Lemma 1.1, pp. 385 and 391](https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p07-p.pdf)
for shared-facet descent; the precise H-description statement and coarse Larman
constant are derived in the cited Lean source, not quoted from that paper.

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

## Reproduction and the actual next target

```
lake build Solutions.PolynomialSelectedRunBudgets Solutions.PolynomialFixedExcessLarman
python3 scripts/check_exact_selected_support.py
python3 scripts/check_support_deficit_budget.py
```

The initial receipt `EXACT_SELECTED_SUPPORT_CHECK_2026-09-12.json` is historical
and hashes the original candidate. The rerun in
[verification/2026-09-12-exact-support](verification/2026-09-12-exact-support/)
hashes the corrected source and again passes 32,767 subsets, 212,993 vertex
counting cases, and 229,369 support/gap cases. The #202 checker and its original
receipt are preserved, together with a fresh passing rerun. Finite checks cover
only counting and integer consequences; the Lean build and axiom audit provide
the separate formal proof evidence. No dependency pin or workflow was changed.

The remaining target is the JOINT cost of coupled carriers when deficit grows.
It is no longer the isolated deficit-one internal-carrier case. Moreover,
[the cube example from #202](SUPPORT_DEFICIT_INTRINSIC_BUDGET_2026-09-12.md)
shows that shortest repair certificates need not have logarithmic deficit: all
target-slack cube faces share a vertex, their labels form a clique, and a
chordless path uses at most two of them. Hence g can be at least d-2 while the
cube's actual diameter is only d. This example is mathematically explained and
finite-tested, not yet a Lean theorem in this integration.

A useful next bound must recognize product-like large-deficit carriers and
charge shared progress across calls; it cannot merely force g to be small.
The general fixed-excess bound remains exponential in E. Polynomial Hirsch
and the dimension-at-least-six leaf remain Open.
