# Original-facet combinatorial segments, local reentry witnesses, and checked splices

## Research status and the conjecture-facing purpose

This contribution is exact research software and a written mathematical analysis.
It is NOT a new Lean compilation or Prove2Me acceptance. It does not claim to
prove Polynomial Hirsch. It imports the project's exact LP and original-edge
arithmetic auditor unchanged and does not alter an accepted theorem or selector.

The previous #257 bound counts all available vertices of a target-deleted
polyhedron. That inventory can genuinely be exponential. Here we implement a
route construction whose CLASSICAL guarantee instead controls which original
facets a route revisits. The construction is Adiprasito--Benedetti's combinatorial
segment, Section 3 of *The Hirsch conjecture holds for normal flag complexes*,
https://arxiv.org/abs/1303.3598, published DOI10.1287/moor.2014.0661.
Their theorem, not a new claim of this project, gives a nonrevisiting path on
normal flag complexes. The dual of a simple bounded polytope is normal.

The new engineering/mathematical interface is to DISCOVER the needed link graphs
from original rational H inequalities, with primal or strict dual certificates
for EVERY queried intersection. No vertex graph, full facet complex, shape chart,
or neighboring vertex is supplied to the producer. Its output is independently
checked as an actual original-edge route. We additionally expose exact reentry
cost and return an original-row missing-triangle witness involving the first
reentered facet, then optionally repair excursions using unchanged #253.

## A decisive known limitation: this is not a new universal route family

Labbé, Manneville and Santos, *Hirsch polytopes with exponentially long
combinatorial segments*, https://arxiv.org/abs/1510.07678, Mathematical Programming
165 (2017), DOI10.1007/s10107-016-1099-y, prove much more than occasional bad
choices: there are vertex-decomposable simplicial d-polytopes with
N+Theta(d^2) vertices and facet pairs for which EVERY combinatorial segment
has length at least 2^(d-3)N (Theorem E/4.5). Those polytopes themselves satisfy
the Hirsch bound. Taking N fixed already rules out a polynomial-in-total-input-
facets bound for all such segment choices after polarity.

Thus changing label tie breaking within this family cannot solve the conjecture
in general. This is a primary-source theorem, not extrapolation of our tests and
not a new counterexample. The source was checked during this continuation, and
the limitation is preserved as part of the new method, not hidden in a caveat.
The useful role is a certified short-route component on flag inputs and a new
way to locate/repair excursions outside that class. A successful general hybrid
must leave the restricted combinatorial-segment family on the known bad inputs.
The splice below is permitted to do that; no theorem that it always succeeds is
asserted. Nothing here is a reason to abandon other approaches to Polynomial Hirsch.

## 1. Exact intersection questions from ORIGINAL inequalities

Assume P={x in R^d:A_i x<=b_i} is simple, bounded, full-dimensional, with m genuine
facet rows. The program also checks boundedness by original-row certificates for
both signs of every coordinate. Global simplicity and facet irredundancy are the
stated input class; all finite test models separately establish them. Local
vertex audits do not silently certify simplicity at unvisited vertices.

For a row set S, define f_S=sum_{i in S} A_i and B_S=sum_{i in S} b_i. Then

    intersection_{i in S} facet_i is nonempty
      iff max_{x in P} f_S(x)=B_S.                              (1)

All selected slacks are nonnegative, so equality in their sum forces EVERY
selected row tight. A present answer includes an original feasible point with
those exact equalities. An absent answer includes nonnegative multipliers alpha
with sum alpha_i A_i=f_W for a nonempty W subset S and alpha.b<B_W. Weak duality
then excludes the W intersection, and hence the S intersection. The auditor
checks these finite identities and signs against the original A,b, without
calling any LP, elimination or rank routine.

The producer uses the existing exact capped Bland LP to FIND these witnesses.
It reuses present points and already-excluded subsets. A cap or failed optimization
is incomplete discovery, not an absent-face certificate. No floating tolerance
or heuristic rank is used. For rational bounded P, exact LP optima/certificates
exist, but this implementation has no polynomial simplex-pivot guarantee.

For locked original rows S, the dual link graph has vertices i outside S with
S+i feasible, and edges ij with S+i+j feasible. At most m+binom(m,2) intersection
questions construct its whole graph. This graph has at most m vertices even when
P has exponentially many vertices. It is a FACET-intersection/link graph, never
an asserted small original vertex graph. Normality gives the needed connectivity.

## 2. The exact classical segment, in row labels

A simple original vertex is represented by its d active labels F. To connect
F to a target label set Y in the link of S, choose a label p in F-S nearest Y
in that link graph. Let Y' be its nearest targets. In link(S+p), recursively
route to neighbors of p that reduce distance to Y'. The terminal facet contains
the next pearl p'. Its distance decreases by exactly one. Restrict Y' to the
nearest targets of p' and continue until a facet meets Y. Child paths are joined
with their fixed labels, which keeps them original facet-adjacency paths.

To connect two full active sets F,H, first reach any label of H, retain that
common label, and recursively finish in its link. The implementation initially
retains F intersect H as well; this merely starts the same construction in a
face link. The zero-dimensional-link step directly joins the two original
vertices on an edge. Equal endpoints are stationary. All ties are deterministic
in ORIGINAL facet labels. Unlike a numerical derivative rule, the resulting
label path is invariant under invertible affine coordinate changes and positive
row rescalings, provided the labels stay fixed. Arbitrary relabeling is not claimed
invariant, and exact LP witness values themselves need not stay identical.

The generated labels are converted to actual coordinates through their certified
intersections. Original inverse identities T*D=-I establish the vertex ranks.
For every consecutive pair, the auditor verifies the maximal original feasible
ratio in the released direction and the shared d-1 independent original rows.
This is an original edge, not an auxiliary-edge projection or a chord.

The final auditor DOES recompute BFS and replay the combinatorial recursion on
the graph derived from the verified answers. It does not perform geometric
discovery, optimization, inversion, convex-hull reconstruction, or search for
another original route. Calling it free of all graph computation would be false.

## 3. What can actually be bounded without a vertex inventory

The classical flag theorem says this particular combinatorial segment does not
leave and then re-enter any original facet when the dual boundary is flag.
Here flag means every pairwise-intersecting family of original facets has a
common intersection. This is stronger than checking only triples at the top
level. Links inherit flagness. The program does NOT infer global flagness from
one successful route, or pretend arbitrary polytopes satisfy it.

Let L be its raw edge count and R the number of entries into a previously seen
facet (one entering facet per edge). Direct counting gives the exact identity

    L = number_of_distinct_facets_encountered - d + R,          (2)
    L <= m-d+R.

Thus R=0 recovers the classical m-d bound even if the total number of vertices
is enormous. The report lists every reentry instead of presuming they are zero.
Nonflag runs may exceed m-d and are retained in the tests.

The route has a useful OUTPUT-sensitive discovery bound. A positive recursive
call owns a nonempty contiguous interval of output edges. At a fixed call-tree
depth, such intervals are disjoint. Depth is at most 2d+1: only a facet-call to
its set-call keeps the same link; every other recursive child increases S.
There are therefore at most (2d+1)L positive calls. A zero set-call can only be
the first child of a facet-call; charge it to that parent. The zero total route
adds only a constant. The deliberately loose implemented bound is

    recursive_calls <= (4d+4)(L+1).                            (3)

Each visited link graph uses at most m+binom(m,2) questions. Reconstructing output
vertices uses at most L+1 further questions; boundedness uses 2d optimizations.
With the optional missing-triangle diagnosis off, the number of exact LP calls
is at most the number of uncached questions plus 2d. On FLAG inputs, substituting
L<=m-d into (3) makes this a polynomial, O(d*m^3), query count. It is not a bound
on the number of Bland pivots, bit complexity, certificate serialization, or
runtime of global flag recognition. This bound also does not prove polynomial
query count on the published nonflag counterexamples, where L is exponential.

## 4. A route-local obstruction involving the reentered facet

The induction in Adiprasito--Benedetti's Lemma3.1 uses flagness at a specific
place: if a row w is incident to two consecutive pearls p,q, and p,q are adjacent,
then the triangle {w,p,q} must be filled in that recursive link. The rest of that
step uses graph distance and the first-hit property, not another global clique
hypothesis. Keeping the same induction gives this localized sufficient condition:

    Fix a row w. If every visited recursive link not already locking w fills
    every 3-clique containing w, the resulting path does not reenter w.       (4)

This is a written localization of the classical proof, not a new Lean theorem.
To see it, apply Lemma3.1 inductively to the children in the actual execution
tree. At a crossing of child segments, graph geodesicity puts a later pearl
incident to w at distance at most two from the earlier one. Distance two would
make w an earlier next-target hit; hence the pearls are consecutive. The only
additional step needed to lift adjacency into the earlier pearl's link is the
filled triangle {w,p,q}. The within-child case is the induction hypothesis.
The final common-target-label recursion has exactly the same decomposition.

Contrapositively, a reentry must encounter a missing triangle containing w in
one of these visited links. The implementation searches for such a certificate
for the FIRST reentered facet, with an explicit diagnostic cap. Its witness is

    S+w+p, S+w+q, S+p+q all feasible,
    S+w+p+q infeasible.                                       (5)

Every feasibility and strict-exclusion statement is tied to the original rows.
This is a missing triangle IN A LINK; it need not be a minimal global nonface.
A cap/absence of a found witness is never labeled global flagness. A found defect
is not claimed uniquely responsible, nor charged injectively to every reentry.
The fixed-row diagnostic makes at most binom(m-1,2) extra questions per visited
link when uncapped. No polynomial bound on total reentry debt is derived.

## 5. Checked excursion repair deliberately permits a different route family

A reentry at facet i defines an interval from the last vertex on i before leaving
to the first vertex on i after returning. Both endpoints are already known.
The repair module invokes unchanged #253 on them. Their common facet is locked,
so every replacement edge lies in i. Commit the replacement ONLY if its delivered
loop-erased path is strictly shorter than the removed interval. Re-audit every
nested certificate and the entire splice. This may cease to be a combinatorial
segment, which is allowed and important in light of the published lower bound.

Original endpoints and adjacency are preserved. If the initial segment has L
edges, at most L accepted repairs are possible because length is a strictly
integer-decreasing measure. A scan has at most L reentry excursions; without
caps the number of repair calls is at most O(L^2). This is not polynomial in
m,d unless L already is. #253's own search effort and route bound also remain
separate. A failed/capped trial leaves the previous valid route intact.

The method does NOT assume a reentry can always be shortened. Reentry debt need
not decrease on every accepted replacement; only edge length must. No claim is
made that all possible nonflag defects are repaired, that the result is shortest,
or that a local optimum under this repair has a polynomial edge count. Some
nonrevisiting paths are already nonshortest and offer no reentry to remove.

## 6. Tests, references and next precise boundary

The test stages report exact H-based production, independent reference adjacency,
BFS shortest distance, original #253 comparison, every raw reentry and each
accepted splice. Reference graphs are constructed only by the test, not passed
to either producer. Small flagness checks enumerate all cliques through size d+1
against independently reconstructed vertices; they are not the production algorithm.
The overlapping codimension-two cube truncations and rational dodecahedron
provide non-product flag inputs, not only axis-aligned cubes.

Large cubes are supplied as ordinary inequality matrices. Known 2^d vertex counts
come from their explicit cube construction; those graphs are not enumerated.
The 16-dimensional case reaches the opposite vertex in16 original edges with
12,862 distinct intersection answers,279 LP maximizations and586 internal pivots.
The query count exceeds the output count because many answers concern empty
intersections or the same witness; it is not mislabeled a vertex count.

Known stacked-polar corridor inputs are reused from #254, not reintroduced as a
new construction. Reference graphs come from their checked stacking incidences.
For m16 and m24 the new routes have9 and15 edges (shortest), versus11 and17 for
unchanged #253. These favorable cases do not erase adverse small-model results.
In a four-dimensional eight-facet nonflag example the raw segment uses5 edges,
exceeding m-d=4; the actual reentry splice reduces that instance to4.

The eight small reference graphs have 142 vertices and 267 edges in total.
Of 1,424 executed ordered endpoint pairs, 756 belong to independently verified
flag inputs and 668 to the nonflag holdouts. Two larger small models use fixed
80/100-pair samples; the others test every ordered pair. The raw segment uses
3,404 edges, repaired output 3,391, unchanged #253 3,389, and BFS reference 3,360.
The hybrid is therefore NOT an aggregate improvement over #253 on this suite.
Raw, repaired and #253 nonshortest counts are 44, 31 and 29 respectively.

All 13 observed raw reentries occur on nonflag models. Every first reentered
facet has a finite missing-triangle witness in a visited link. Thirteen accepted
splices remove those 13 observed reentries and save 13 edges, but 31 nonshortest
routes remain. In particular a successful repair scan does not mean optimality.
The four flag models yield 1,898 raw/repaired edges, zero reentries and four
nonshortest routes; nonrevisiting itself is not shortestness. The nonflag totals
are 1,506 raw versus 1,493 repaired versus 1,491 for #253, with shortest total1,466.

Six complete dense-affine label-path comparisons and twelve positive-row-scale
comparisons preserve the selected labels. Twenty-six saved route audits pass
with LP/inverse/basis production disabled; the repair consumer is also separately
replayed with replacement-route production disabled. There are 17 DISTINCT
malformed/capped control types, each exercised by the stage harness. Repeated
stage invocations of the same controls are not counted as new control types.

The full three-stage suite was rerun in a fresh directory holding only the eight
required scripts (three new, five unchanged dependencies). Every numeric/result
and source-hash field matches except elapsed seconds, and all three generated
fixture files match byte-for-byte. The committed replay JSON records both report
hashes and exact fixture digests. This is a clean dependency replay, not a full
repository clone or Lean compilation.

All final numerical totals and source identities are in the execution summary.
Full reports and worked certificates regenerate with the three test stages.
Independent raw and repair auditors are exercised with LP, inverse, basis
production and repair search disabled. Negative controls bind all selected
facets, query answers, route labels, caps, inverses, and replacement indices.
Python and the JSON parser are not Lean-extracted or formally verified. No
hosted compiler or Prove2Me submission is requested for this research-only PR.

The next conjecture-facing question is not whether a total face inventory is
small, nor whether arbitrary conservative segments admit a universal polynomial
bound (the latter is disproved by the cited paper). It is whether a controlled
hybrid repair/alternative route can bound the remaining reentry work on arbitrary
actual carriers. The current code supplies exact original-row defects and a
verified splice interface for testing that question, without inserting a short-
repair premise as if it were already proved. Existing #244/#238/#250 ownership
and #255/#256/#257 research remain unchanged.

Primary sources:
- K. Adiprasito, B. Benedetti, arXiv1303.3598, Section3, Theorem1.4 and Lemma3.1.
- J.-P. Labbe, T. Manneville, F. Santos, arXiv1510.07678, TheoremsB andE/4.5.
