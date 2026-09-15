# Graphical flag refinements: a static alternative to energy-descent schedules

## Status and the distinct contribution

This is a written mathematical argument and exact research software. It is NOT
Lean-compiled or Prove2Me-accepted, and it does not prove Polynomial Hirsch.
The input class is simple, bounded, full-dimensional polytopes with genuine
ORIGINAL facet inequalities. The objective is an ordinary-edge bound in their
original facet count, never a smaller extension's description.

The live frontier includes #262/#263's exact stellar defect accounting and
bounded macros, and another agent owns #264's further plateau experiments.
This work leaves those files/branches unchanged. It uses a different source of
control: choose an auxiliary graph on ORIGINAL facet labels, count its connected
original faces, and certify the entire resulting flag refinement in advance.
There is no assumption that each elementary subdivision decreases a potential
or that a short improving macro is always available.

Classical building-set/nested-set theory supplies the subdivision mechanism;
Adiprasito--Benedetti supplies the short route on a normal flag complex. The
specific two-component criterion, counted original-edge application, exact
sparse graph search and comparisons below are proved and checked here. No
claim of historical priority for all equivalent nested-set criteria is made.

## 1. Connected original faces and the correct nested complex

Let K be the simplicial boundary dual to a simple d-polytope P with m facets.
Its vertices are original facet labels. Let G be ANY simple auxiliary graph on
these labels, and define

    B(K,G) = {nonempty S in K : the induced graph G[S] is connected}.

An element S is called a tube for this construction. It must be an ORIGINAL
face of K. A graph-connected set that is not in K is never a refined vertex.

Define R(K,G) as follows. Its vertices are B(K,G). A family of tubes is a face
when its union is in K and each pair is either nested by inclusion, or disjoint
with no G-edge between them. Overlapping incomparable tubes are incompatible.
The union-in-K condition is indispensable: ignoring it can fill a genuine
original minimal nonface and destroy the subdivision interpretation.

For a face F of K, the maximal connected subsets of G[F] partition F into its
connected components. The Boolean interval [empty,F] in the face poset is the
product of the Boolean intervals on these components. Thus B(K,G) is a building
set in the exact sense of Feichtner--Kozlov, Definition 2.2. Their Definition 2.7
of nestedness specializes to the rule above: incomparable connected subsets
with an overlap or an edge between them have connected union; disjoint
anticomplete subsets have disconnected union, provided the join exists in K.
A clique in the pairwise compatibility graph need not have that join; this is
why the original-face union condition is kept separately.

Theorem 3.4 of Feichtner--Kozlov says that blowing up the building-set elements
in decreasing inclusion order gives the nested-set face poset. In a simplicial
face poset this operation is stellar subdivision at the corresponding face.
Singleton operations only relabel vertices and can be omitted. Consequently
R(K,G) is obtained by stellar-subdividing EVERY connected original face with
at least two labels, largest first. Smaller original faces survive until their
turn. The result is a same-dimensional subdivision of K. It is therefore a
simplicial sphere, in particular pure and normal. This is a classical theorem
applied with an explicitly checked building-set property, not a normality
assumption inferred from the finite tests.

Primary source: E.-M. Feichtner and D.N. Kozlov, *Incidence combinatorics of
resolutions*, Selecta Mathematica 10 (2004), 37--60, arXiv:math/0305154,
Definitions 2.2, 2.7 and Theorem 3.4. The actual PDF statements were inspected.
https://arxiv.org/abs/math/0305154

## 2. Exact flag criterion: at most two components per original defect

Write N(K) for ALL original inclusion-minimal nonfaces. Then

    R(K,G) is flag  iff  c(G[N]) <= 2 for every N in N(K).       (1)

Here c is the number of induced connected components. This is a condition on
whole original minimal nonfaces, not just on a sample of triangles. Missing
pairs automatically satisfy it. No small defect support or low cardinality is
assumed.

Necessity. Suppose a minimal nonface N has at least three G-components C_i.
Every C_i is a nonempty proper subset of N, hence an original face and a tube.
Any two components are disjoint and anticomplete; their union is a proper
subset of N, hence an original face. The tube vertices form a clique in R.
Their complete union is N, which is not in K, so that clique is not a face.
The refinement is not flag.

Sufficiency. Let T be a clique of tube vertices. Its maximal tubes are disjoint
and anticomplete, since every pair is compatible. If their total union U is
not an original face, take a minimal nonface N contained in U. Each connected
component of G[N] must lie inside one maximal tube: no auxiliary edge joins
different maximal tubes. By (1), N is therefore contained in at most two such
tubes. One tube is an original face; two tubes have an original-face union
because they are an edge of the clique. Both alternatives contradict N being
an original nonface. Thus U is in K, and the pairwise compatibility already
shows that the entire clique is a face of R.

The flat-block theorem of #260 is recovered by taking G to be the disjoint
union of complete graphs on its blocks. Connected original subsets then live
inside individual blocks and compatible tubes in a block form a chain.
The present graphs need not have complete connected components, so connected
faces from different overlapping portions of one component can be used without
creating every face of the entire block. This genuinely enlarges that class of
static certificates; it does not make every sparse graph valid.

## 3. Exact original-edge transport and the all-pairs bound

Let M=|B(K,G)|. Under (1), the classical normal-flag theorem supplies a refined
facet path of length at most M-d between any two refined facets. We next prove
that this counts ORIGINAL edges as well, instead of relying on an arbitrary
projection map.

The carrier of a refined simplex is the union of its tubes. For any nested
family, each tube has a private original label not belonging to any maximal
proper tube of the family below it. Otherwise the connected tube would be a
union of at least two disjoint anticomplete proper tubes, impossible; a sole
proper child also cannot cover it. Private labels chosen for different tubes
are distinct, because two tubes are nested or disjoint. Thus a refined simplex
with s vertices has a carrier containing at least s original labels.

A maximal refined simplex has d tube vertices and an original carrier of size
at most d; it therefore carries an original maximal d-set. Adjacent refined
maximal simplices share d-1 tubes, whose union has at least d-1 original labels.
Their full original carriers are consequently equal or adjacent maximal faces
of K. In P these are equal or adjacent original vertices. Delete consecutive
stationary carriers; the delivered path has no more edges than the refined one.
This proves

    diameter(P) <= M-d.                                        (2)

Compatible endpoint lifts preserve the original smallest common face. Order
labels common to both endpoint facets first. As each label is added, choose
the connected component of the growing prefix containing that label. These
successive tubes are nested or disjoint anticomplete, have original-face union,
and form a d-tube maximal face. Both lifts contain the common initial tubes,
whose union covers all original common labels. Apply the flag segment inside
the link of these shared tube vertices. Every original carrier keeps the common
labels. The code independently checks original endpoint equality, shared facets,
active inverse identities and maximal original feasible ratios on every edge.

Classical route input: K. Adiprasito and B. Benedetti, *The Hirsch conjecture
holds for normal flag complexes*, Theorem 1.4 and Section 3, arXiv:1303.3598.
Its theorem is not reproved or republished here. The existing #258 implementation
constructs that path in the new refinement, not necessarily a combinatorial
segment of the original K. Original reentries are allowed and recorded.
https://arxiv.org/abs/1303.3598

## 4. Quadratic sufficient classes from paths and cycles

If G is a path on m labels, a connected subset is an interval. Original faces
have at most d labels, so

    M <= sum_{s=1}^d (m-s+1) = dm-d(d-1)/2,
    diameter(P) <= dm-d(d+1)/2.                                (3)

The same bound holds for a union of paths: extend it to a single path when
counting connected subsets, which cannot decrease the count. For a union of
paths and cycles, i.e. maximum auxiliary degree at most two, there are at most
m connected subsets of any fixed positive cardinality. Thus

    M <= md,   diameter(P) <= d(m-1).                          (4)

Every inequality is conditional on the exact minimal-nonface criterion (1).
This is an all-dimensional polynomial class criterion, NOT a proof that every
polytope admits such a graph. The graph condition is a finite structural input,
not a supplied short route. Complete nonface classification, finding an optimal
graph and constructing the refined path can still be expensive. A route-size
bound does not itself bound LP pivots or bit complexity.

More generally the actual connected-ORIGINAL-face count M, rather than graph
edge count or degree alone, is the relevant quantity. A dense graph on a fixed-
dimensional complex may still have a modest M. Failure of the degree-two class
below does not prove that every graphical refinement is exponentially large.

## 5. A static commuting certificate for the actual #263 plateau

Reuse the SAME ten integer points from fixtures/mixed_absorption_plateau.json,
center and polarize as in #263. Its original polytope has d=5, m=10 and 36
vertices. A complete exact reconstruction verifies all 252 square systems,
minimal nonfaces and genuine facets before the refinement is tested.

The degree-two search finds the auxiliary edges

    01, 08, 23, 45, 56, 78.

These form disjoint paths 1-0-8-7, 2-3, 4-5-6, and isolated label 9. Every
minimal nonface has at most two induced components. Moreover every connected
set of three original labels is already a nonface. Hence the registry consists
of ten singleton tubes plus these six edges, so M=16 and (2) gives 11 edges
for every original endpoint pair.

No original simplex contains two of these selected edges that overlap at a
vertex: their connected three-label union is not an original face. Disjoint
edge subdivisions commute by their join action on a simplex, and overlapping
ones have disjoint affected simplex sets. Therefore all six original-edge
subdivisions can be performed in ANY order with the same final complex, after
renaming each fresh vertex by its original edge. The test independently executes
all 6!=720 orders, recomputes complete minimal nonfaces at every step using
#261's exact stellar formula, and checks this final equality and flagness.

There are 87 different W-trajectories among those orders. None of the 4,320
steps increases W, but 420 are neutral. There are 314 completely strictly
decreasing orders. Thus this is NOT an assertion that neutral steps are
unavoidable from the original input; #263's obstruction was a particular
reachable polytopal state, not a proof about every prefix. The static graph
certifies the end result independently of these trajectories, so it does not
need a bounded-macro existence assertion or a greedy potential schedule.

The six-edge construction matches #263's M16, rather than setting a new record
against its macro. It is optimal WITHIN the maximum-degree-two graphical class
by a completed finite branch search; it is not claimed globally optimal among
all subdivisions. Independent exhaustive flat-partition enumeration proves
that every #260 flat certificate on this original input has M>=18. This is a
representation-size improvement, not a new lower bound on original diameter.
The separate #264 plateau work is neither modified nor claimed superseded.

## 6. Sparse graph existence can genuinely fail

Consider the boundary of the cyclic four-polytope C(n,4), n>=6. Its higher
minimal nonfaces are exactly the stable triples of its cyclic label order.
This complete family description is reused from #262/#263. Under (1), every
such triple must contain an edge of G. Hence H=C_n union G has independence
number at most two: an independent triple of H would be a stable triple of
C_n with no G-edge. The complement of H is triangle-free.

For completeness, the elementary triangle-free bound is |E(J)|<=floor(n^2/4).
At every edge uv of a triangle-free J, deg(u)+deg(v)<=n. Summing over edges
gives sum_v deg(v)^2 <= n|E(J)|, while Cauchy gives sum_v deg(v)^2>=4|E(J)|^2/n.
This proves the bound, including the zero-edge case. Therefore

    |E(H)| >= binom(n,2)-floor(n^2/4).

If G has maximum degree two then |E(G)|<=n and |E(H)|<=2n. The displayed lower
bound exceeds 2n for every n>=11. No degree-two certificate exists on these
actual polytopal inputs, regardless of ordering or search effort. This is an
all-size deduction, not extrapolation from the arithmetic checks n11..100.

For n=9 the test exhausts all 20,160 Hamiltonian cycles up to rotation/reversal
and finds no valid one. A Hamiltonian path could be closed by one edge without
increasing any induced component count, so none exists either. That finite
result does NOT exclude a disconnected union of cycles and paths at n=9; the
stronger all-degree-two obstruction is the proved n>=11 statement above.

These are failures of this inexpensive certificate class, not Hirsch
counterexamples. Four-dimensional cyclic polars have other route bounds and
#263 already supplies a different quadratic stellar schedule. In particular
the density obstruction does not show that all graph choices have large M.
It prevents assuming that a useful sparse graph always exists.

## 7. Exact search, original-H production and completed checks

The graph producer branches on an unresolved original minimal nonface N with
more than two components. Any valid supergraph MUST add an edge between two of
these current components. All degree-allowed such edges are branched. Adding
graph edges can only increase the set of connected original faces, so the
current M is a valid branch-and-bound lower bound. Memoization is by exact
edge set. When a cap is reached only a best-found valid graph is returned;
optimality/nonexistence is asserted only after complete exhaustion. A caller
can also supply a graph directly; no search is required by the mathematical
certificate. The main verifier checks validity, not the searcher's optimality.

The generic original-H producer discovers ALL minimal nonfaces through size
d+1 using the unchanged #261 classifier and #258 exact primal/dual witnesses.
This may be exponential and may identify every original vertex. It never takes
a vertex graph as input, but that is not a claim of avoiding such enumeration.
Original boundedness gets both-sign coordinate dual bounds; global simplicity
and genuine facet presentation remain the input class, independently established
for the finite reference models. A few local bases do not prove them globally.

Connected-face enumeration grows from singletons by adding graph neighbors.
Every connected subset has such a spanning-tree order, and once a set is an
original nonface no superset is a face. This generates the ENTIRE tube registry.
The verifier regenerates it and replays refined-link BFS/recursion, then checks
all original edges. It does no geometric LP or inverse discovery, but it still
performs classification replay and combinatorial graph computation. Python and
JSON parsing are not Lean-extracted or formally verified.

Executed abstract layer: all 114 four-label complexes against all 64 auxiliary
graphs, totaling 7,296 pairs; 16,486 literal stellar operations; 24,714 pure
adjacent-carrier checks; 45,670 registry entries. Independent literal stellar
subdivision and nested-face computations agree. The flag criterion identifies
6,766 flag and 530 nonflag cases. Exhaustive graph enumeration separately
cross-checks every degree-two optimum from the graph branch search.

Executed original-H layer: five independent reference graphs, 52 endpoint pairs,
376 square systems. There are 104 delivered original edges, equal to both the
unchanged #258 raw routes and independent BFS total on this selected suite.
There are 108 refined edges and four stationary carriers. No benchmark
superiority is claimed; no sampled route is nonshortest. The generic producer
uses 1,724 LP maximizations and 8,532 internal pivots. No large graph or broad
random-polytope population was tested.

Exact best graphical versus exhaustive best FLAT counts are:

    original input         graphical M    best flat M
    simplex3                    6              6
    cyclic4/6                   8              8
    cyclic4/7                  11             12
    cyclic4/8                  16             20
    plateau5/10                16             18.

The flat comparison enumerates EVERY set partition, without branch-and-bound
pruning: respectively 15,203,877,4,140,115,975 partitions. Its validity test is
#260's complete at-most-two-block criterion and each block cost is its actual
nonempty original-face count. These are finite instance separations, not an
asymptotic lower bound for all graphical certificates or all refinements.
For cyclic4/8, our M16 is WORSE than #262/#263's more general M14 hierarchy.
Thus graphical refinement does not dominate arbitrary stellar schedules.

Ten malformed or capped certificates are rejected, including wrong auxiliary
labels, removed tubes, false routes, incomplete original nonfaces and missing
geometric witnesses. Five stored full audits pass with LP/inversion/basis and
intersection production disabled. The three test stages reproduce all fields
except elapsed seconds and the complete fixture bytes in a clean dependency
workspace. No Actions, Lean or Prove2Me workflow is requested for this research.

    python3 scripts/test_graphical_flag_refinement.py --stage abstract
    python3 scripts/test_graphical_flag_refinement.py --stage geometry
    python3 scripts/test_graphical_flag_refinement.py --stage obstructions
    python3 scripts/graphical_flag_refinement.py input.json graph.json --output route.json

## 8. The remaining conjecture-level issue

The payoff from a suitable graph is now explicit: an exact flag criterion,
a same-dimensional subdivision, a genuine original-edge carrier map and a
counted bound from connected original faces. This avoids having to prove that
an energy-decreasing elementary move or short macro exists at every state.
But the new missing ingredient is NOT solved: an arbitrary dual boundary need
not admit a degree-two graph, and arbitrary dense graphs may produce too many
tubes. A universal proof would need a polynomial bound on the relevant connected-
face registry for a suitable graph, a controlled hybrid with other subdivisions,
or another global original-edge argument. None is silently inserted as a
hypothesis claimed to establish Polynomial Hirsch.

The new files leave all previous accepted theorems, selectors, toolchain pins,
workflow permissions and other agents' branches unchanged. Classical sources
are explicitly used as sources, not presented as newly solved open lemmas.
