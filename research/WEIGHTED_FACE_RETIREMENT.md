# Weighted face retirement: a linear three-face tail and its sharp-order obstruction

## Status and exact relation to concurrent work

This is a written mathematical proof and executed exact rational research,
NOT a new Lean compilation, Prove2Me acceptance, or solution of Polynomial Hirsch.
It analyzes the ACTUAL unchanged selector from merged #253:

    scripts/two_face_acquisition.py
    Git blob aa562f02dd492ecc47479381d637c6292757ebd3
    SHA256 ea395cf665fbbc45f15d4ea9fa35d10bb00efc55795732ff6bfb0fc125d430d7.

The first live STATUS read still described #252's fixed-radius acquisitions.
A pre-write check of the current main commit revealed that #253 had already
merged complete two-face acquisition and stronger whole-face fallback. The
independently prepared polygon selector was WITHHELD: it is not added to main,
repackaged as a new algorithm, or substituted in the experiments below.
The new contribution instead refines #253's cost accounting and supplies a
sharp-order corridor test of that exact executable. Coordination is on #253.

The input class remains SIMPLE bounded full-dimensional polytopes in ORIGINAL
H-coordinates, with genuine facet rows and supplied vertex endpoints. No graph,
neighbor list, factorization or target objective is supplied to the selector.
For an input with redundant inequalities, use its larger row count unless the
irredundant count is separately established. Nonsimple projected-image work
belongs to #250; #244's core/fibre assembly and #238 remain separate.

## 1. Replace maximum-size multiplication by actual polygon weights

Let P have dimension d, m original facets, and excess e=m-d. Let v be the target.
At a decision vertex x lock every target facet already containing x. The retained
face has dimension r=d-|active(x) intersect active(v)|. Simplicity implies r<=e.
The target-slack objective stays fixed until the first new target acquisition.

The #253 fallback applies only when NONE of the complete incident polygons
meets a missing target facet. It follows a strictly objective-increasing arc
to an endpoint dominating the maximum of EVERY inspected polygon. In particular
it attains the maximum on its chosen polygon F. If F has q(F) sides, this costs
at most q(F)-1 genuine original edges. The same F can never be selected for a
later fallback in that phase: later decision values are strictly larger than
its maximum. After a target acquisition it is excluded from the retained face,
because every earlier fallback polygon was disjoint from that target facet.

Consequently, for the set S of chosen fallback polygons,

    L_fallback <= sum_{F in S} (q(F)-1).                       (1)

This is a weighted version of the existing retirement invariant. Unlike the
coarse product (number of fallbacks)*(largest possible polygon), it does not
spend the largest polygon size repeatedly when the actual incidence structure
prevents that. The supporting Python ledger checks the original #253 certificate,
then binds each distinct selected original facet to its actual q and arc length.
It does not change the route and performs no inverse/LP/face search.

## 2. A linear bound for an arbitrary intrinsic three-dimensional phase

Assume r=3 at the start. The retained face Q is a simple three-polytope. Its
facets come from unique original rows not among the already locked d-3 rows.
There are three target facets in Q, and at most e other facets. Let H be the
dual graph of Q: vertices are its facets and edges represent facet adjacency.
It is a simple planar graph. Let N be its non-target vertices, |N|<=e.

Every selected fallback polygon is a facet of Q DISJOINT from all three target
facets. Its dual vertex therefore has no neighbor outside N. Its polygon size
is exactly its degree in the induced graph H[N]. The selected vertices are
all distinct by (1). Thus, if B is the number of fallback macros,

    L_fallback <= sum_{j selected} (deg_{H[N]}(j)-1)
               <= 2|E(H[N])|-B
               <= 6e-12-B.                                  (2)

There are at least three non-target facets when r=3, so e>=3 and the planar
bound 2|E|<=6|N|-12 is applicable, even if the induced graph is disconnected.
For completeness, the latter follows by adding planar edges between components
and triangulating to a maximal simple planar graph on the same at-least-three
vertices; Euler's V-E+F=2 and 3F=2E then give E<=3V-6.

The first target-acquisition macro has at most a=floor((e+2)/2) edges: every
original two-face has at most e+2 sides, and the rule chooses a shortest first-hit
arc. After that acquisition, Q is restricted to a target polygon. The rule is
SHORTEST on this polygon, not just bounded by two unrelated acquisition maxima.
Indeed it first reaches a neighbor of the target along a shortest of the two
boundary arcs, then follows the remaining target edge. Its complete remaining
cost is at most a. There are no more fallback macros.

This proves the algorithm-specific unconditional bound

    L <= 6e-12-B + 2 floor((e+2)/2)
      <= 6e-12   + 2 floor((e+2)/2),       r=3.                (3)

For r=2 the complete remaining route is shortest on its polygon, so

    L <= floor((e+2)/2).

For r<=1, L<=r. These statements apply to an intrinsic three-face even in a
much higher ambient dimension; no projection or graph transport is used. In
particular, the actual #253 route on every simple three-polytope has linear
length in its original facet count. This is NOT a new best three-dimensional
diameter estimate; much stronger low-dimensional existence results are classical.
It is a new cost argument for the specified certificate-producing selector.

### Effect on the unrestricted-dimension account

At initial r>=3, keep #253's higher-dimensional fallback charge unchanged, but
replace the last three-face tail by (3). With a=floor((e+2)/2), this gives

    L <= (r-1)a + 6e-12
         +(e+1) sum_{h=4}^r floor(binom(e,h-2)/(h-1))
      <= (r-1)a + 6e-12 + sum_{j=3}^{r-1} binom(e+1,j).       (4)

One may take the minimum with the older bound where it is smaller. The last
sum is STILL exponential when r and e grow together. The argument removes the
quadratic overcount for the three-dimensional tail; it does not make the
higher-dimensional non-target-face supply polynomial. No short-phase premise
is inserted to conceal this remaining issue.

## 3. Linear fallback is genuinely necessary, even with only hexagonal faces

The following family shows that (3)'s linear order cannot be reduced to a
constant merely because the dimension, polygon sizes and target-acquisition
count are fixed. It applies to ENTIRE #253 fallback macros, not just a weaker
single-edge variant.

Start with the tetrahedron having vertices (-1,-1,-1), e1,e2,e3, indexed0..3.
Stack vertex j>=4 beyond ONLY the front triangle (j-3,j-2,j-1), and choose
(j-2,j-1,j) as the next front. Every step can be realized rationally. If c is
the front's barycenter and each current facet is normalized by a_F z<=1, put

    delta = one half of min({1} union
                    {1/a_F(c)-1 : F != front, a_F(c)>0}),
    new_vertex=(1+delta)c.

All terms in the minimum are positive. The new point lies strictly beyond the
front and strictly beneath every other facet. This is an exact stacking
operation; the boundary update replaces only the front by its three new
triangles. The script checks those strict inequalities against ALL current
facets at every step. The original tetrahedron remains inside, so the origin
is strictly interior and the polar is a bounded full-dimensional polytope.

After m vertices have been constructed, take the polar P_m. It is a simple
three-polytope with exactly m genuine original facets and 2m-4 vertices.
Every boundary triangle in the stacked primal has label span at most3. Each
primal vertex participates in at most three later stacking operations; its
degree is therefore at most6. Dually, EVERY polygon facet of P_m has at most
six sides, independently of m.

Take source dual to (0,1,2) and target dual to (m-3,m-2,m-1). They share no
original facet for m>=8, so their minimal common face is all of P_m.
For a current dual vertex, write M for the largest label in its active triangle.
An incident polygon corresponds to one current label i<=M. Every vertex of
that whole polygon is a primal triangle containing i, so its largest label is
at most i+3<=M+3. Thus even a COMPLETE polygon macro increases M by at most3.

If an incident polygon could meet a target facet, some primal triangle would
contain both its label i and a target label at least m-3. Span<=3 forces i>=m-6,
hence M>=m-6. Initially M=2. Until such an acquisition becomes possible, every
macro is a fallback. Therefore the number B_3 before first acquisition satisfies

    B_3 >= max(0, ceil((m-8)/3)).                             (5)

This lower bound is independent of the phase objective, tie breaking and which
improving polygon maximum is chosen. It follows from the full original face
incidence, not numeric conditioning or an unexecuted exponential trajectory.
It applies to all rules restricted to one incident polygon per macro until
acquisition. #253's existing retirement bound supplies the complementary
B_3<=floor((m-3)/2). Consequently its fallback count on this family is Theta(m).
The route cost is also Theta(m): each macro has at least one and at most five
edges, and the bounded number of acquisition arcs also have bounded size.

This is NOT a Hirsch counterexample or a superpolynomial shortest-path lower
bound. The family itself has only O(m) vertices. Its role is to rule out a
constant-fallback argument and show that the new linear selector bound is of
the right asymptotic order, even with uniformly bounded polygon complexity.

## 4. Actual unchanged-selector results

All numbers below come from executing the exact #253 file, whose Git blob was
read back and matched byte-for-byte. No newly prepared selector is substituted.

| m facets | max polygon sides | fallback macros | route edges | graph distance |
|---:|---:|---:|---:|---:|
|8|6|0|4|4|
|12|6|2|7|7|
|16|6|4|11|9|
|24|6|7|17|15|
|32|6|10|23|20|

The nonshortest routes are deliberately retained. At m32 the previous generic
bound is480; the new linear-tail bound is192. Neither is asserted sharp in its
constant. The actual23-edge route includes20 fallback edges; its ten selected
polygons have total weighted charge48. The more precise observed charges are
saved, rather than replacing them with the coarse universal bound.

The reference graph comes from the fully checked stacking transcript and exact
polar face incidences. For m8/m12, independent all-active-subset SymPy enumeration
also reconstructs the same vertices and distances. For m16/m24/m32 that second
exhaustive subset enumeration is NOT claimed. Every committed original edge is
checked against the stacking-derived reference. Input rational sizes grow: the
largest m32 numerator-plus-denominator size is1451 bits. No uniform small-bit
or strongly polynomial construction claim is made.

## 5. Independent incidence tests, retained failures and reproduction

Four independent original three-polytope graphs (moment-curve polars with6/8/10
facets and a rational dodecahedron) supply808 ordered endpoint pairs and2036
executed #253 edges. All retired facet degrees, lack of target neighbors, selected
facet distinctness and weighted costs are checked against the independent dual
graphs. The routes include eight nonshortest cases. Twenty fallback macros
are exercised in the dodecahedron pairs, using40 actual edges and80 total
selected-facet charge. The path finder receives no reference graph.

The dodecahedral example has rows (0,+/-1,+/-8/5), (+/-1,+/-8/5,0),
(+/-8/5,0,+/-1), all with RHS1. Opposite vertices +/- (5/13,5/13,5/13)
require a fallback because their source polygons miss all target facets. This
particular no-access example is a control, not a replacement for the all-size
corridor proof.

The same three-dimensional tail is embedded in dimensions4/8/16 by taking a
product with already-locked interval coordinates. Each certified route still
has five genuine original edges and is covered by (3) using the original
excess. The whole product graph is not enumerated. Nine saved audits pass with
inverse, basis production and polygon tracing disabled. Seven false/unsupported
certificates are rejected, including attempting to call a four-dimensional
retained face a three-dimensional tail.

    python3 scripts/test_weighted_face_retirement.py
    python3 scripts/three_dimensional_face_accounting.py input.json route.json --output account.json

The new scripts depend only on byte-identical existing #253 and its original
simple-row auditor. The regression regenerates the report and complete worked
fixtures. Generic written proofs and Python checks are NOT Lean proof terms;
there is no new Actions or Prove2Me gate. Data-bound arithmetic checking does
not verify the Python parser or prove global boundedness/simplicity from one
local vertex. Those remain the stated input class, independently verified for
the finite reference models by their constructions.

## 6. Provenance and next research

Classical three-dimensional graph-diameter results predate this project. See
Victor Klee, *Diameters of Polyhedral Graphs*, Canadian Journal of Mathematics,
https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/diameters-of-polyhedral-graphs/DCA8BB9C48499747F83858D5B97A096B.
The planar Euler bound, stacking/polarity and product-face facts are classical;
no historical novelty is claimed for them. This contribution is the application
to #253's actual macro rule, weighted route certificates and matching-order
fallback example. It does not improve the best known general diameter bound.

Known worst cases for classical simplex pivot rules (Disser--Mosis,
https://arxiv.org/abs/2309.14034) also prevent inferring a universal guarantee
from a few favorable models, but do not automatically classify this nonmonotone,
target-given whole-face rule. Likewise our linear corridor lower bound does not
rule out a polynomial bound in higher dimensions.

The concrete next challenge is an analogue of the weighted planar incidence
estimate for the selected high-dimensional retired-face family, or a different
charge controlling that family. Merely counting all non-target facet subsets
retains the exponential term in (4). Completing this three-face account must
not be reported as closing arbitrary high-dimensional carriers, nor should the
already merged complete-face search be reimplemented in another branch.
