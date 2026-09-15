# From blockwise flag subdivisions to ORIGINAL-edge diameter bounds

## 0. Research status and the genuinely different route family

This is a research continuation of #258 in jjoshua2/prove2me-work. It reuses
that contribution's exact original-H intersection certificates and classical
combinatorial-segment implementation without changing either. Integration is
above main73900455acaa956ba82d57ac5e54821fd0f13f39, preserving concurrent
#259's exceptional-facet confinement result and frontier update. It is a written
mathematical derivation and exact executable research, NOT a new Lean or
Prove2Me acceptance. Simple, bounded, full-dimensional polytopes with genuine
original facet rows remain the input class.

The positive result is a GLOBAL structural diameter bound, not another numerical
progress estimate. Partition the original facet labels into blocks. If every
minimal empty facet intersection meets at most TWO blocks, a blockwise
barycentric subdivision of the dual boundary is flag. Its number of vertices
M gives an original-polytope route bound M-d. If every block has size at most
a fixed k, this is linear in the original facet count, with a k-dependent
coefficient. Neither a useful small-block partition nor polynomial recognition
is asserted for arbitrary inputs.

The route runs on the subdivided dual boundary and is then mapped to original
carriers. It need not be a combinatorial segment of the ORIGINAL complex and
may revisit original facets. This distinction is essential: the published
Labbe--Manneville--Santos examples force every original combinatorial segment
between specified endpoints to be exponentially long, even on Hirsch polytopes.
They do not prohibit other original-edge routes. We do not claim to have tested
our method on those published examples.

The imported short-path result is Adiprasito--Benedetti's classical normal-FLAG
Hirsch theorem, not a new theorem of this project. Their paper already discusses
Hirsch bounds on full derived subdivisions. Our contribution is the exact
partition criterion, its explicit count and original-carrier transport, and an
H-certificate implementation. No historical priority is claimed for every
possible equivalent subdivision formulation.

## 1. The subdivision, defined without a new polyhedral image

Let K be the boundary of the polar of a simple d-polytope P with m facets.
Equivalently, a subset of the m ORIGINAL facet labels is a face of K precisely
when their intersection in P is nonempty. K is a simplicial (d-1)-sphere; every
maximal face has d vertices. No polar coordinates need be computed.

Let B_1,...,B_s partition those labels. Define K^B as follows:

* A vertex of K^B is a nonempty face U of K lying in ONE block B_i.
* A collection of those vertices is a face exactly when the vertices inside
  each block form an inclusion chain, and their union is a face of K.

This is an actual subdivision of K. On an original simplex F, decompose it as
the join of the simplices on F intersect B_i. Barycentrically subdivide each
of those smaller simplices and take their join. The triangulations agree on
common faces because each barycentric subdivision restricts to the same
subdivision there. Realize each new vertex U at its barycenter inside the
original face U. These local triangulations cover each original simplex and
introduce no changes in underlying space. Thus K^B is a triangulated sphere,
in particular pure and normal. It need not be explicitly realized as another
convex polytope to apply the normal-flag theorem.

The new vertex count is EXACTLY

    M(B) = sum_i #{U : empty != U in K, U subset B_i}.        (1)

The construction uses induced block complexes, not arbitrary enumerations of
all original faces. A singleton block contributes one vertex. A two-label block
contributes three when the two original facets meet, otherwise two.

## 2. Exact flagness criterion: two blocks, not one

A minimal nonface N of K is an empty original facet intersection all of whose
proper subsets intersect. In a (d-1)-complex its size is at most d+1.

THEOREM. K^B is flag if and only if EVERY minimal nonface of K intersects at
most TWO partition blocks.

Proof of sufficiency. Take any clique of refined vertices. Within a block,
pairwise comparability makes its members one inclusion chain; let U_i be the
largest member of each represented block. Every U_i is a face of K, and every
U_i union U_j is a face, by the corresponding refined edge. If the full union
were not a face, it would contain a minimal nonface N. By hypothesis N is
contained in the union of at most two represented blocks, hence in some U_i
or U_i union U_j, a contradiction. The clique is therefore a refined face.

Proof of necessity. Suppose N is minimal and intersects t>=3 blocks. Its
nonempty pieces N intersect B_i are proper subsets, hence faces and refined
vertices. The union of any two pieces is still a proper subset of N, so these
vertices are pairwise adjacent. Their whole union is N, not a face. Thus they
form an unfilled clique and K^B is not flag.

This is an iff, not a sufficient test using a sampled set of triangles. A
missing edge automatically touches at most two blocks. Missing faces of size
four and higher matter: the boundary of a tetrahedron has no missing triangle,
but partition sizes2,1,1 fail the condition on its four-element missing face.
The tests explicitly reject that shortcut.

Nor must each higher defect lie WITHIN one block. For example each missing
triangle may contain a selected pair and one singleton from a different block.
An arbitrarily large connected family of defects can satisfy the criterion
with all blocks of size two. No factorization into disconnected components is
required.

## 3. Every refined dual edge becomes a genuine original edge or no move

A maximal refined simplex X has d vertices. Its original carrier is

    carrier(X) = union_{U vertex of X} U.

Inside one block a chain of length ell has union of size at least ell. Different
blocks are disjoint, so the carrier has at least d labels. It is an original
face, which has at most d labels. Hence the carrier has exactly d and is an
original maximal simplex, equivalently an original vertex of P.

Let X,Y be neighboring maximal refined simplices. Their common ridge has d-1
vertices. The union of its block chains has at least d-1 original labels and
is contained in both carriers. Each carrier has size d. Therefore

    carrier(X)=carrier(Y), or
    |carrier(X) intersect carrier(Y)|=d-1.                 (2)

In the latter case the original vertices are adjacent along an ordinary edge
of P, by simplicity. Delete consecutive equal carriers from a refined path;
(2) proves that every retained step is an original edge and that length never
increases. Longer repeated excursions need not disappear, and original facets
may be revisited. No claim of original nonrevisiting is inferred from refined
nonrevisiting.

This is NOT the generally invalid claim that an edge of an extension projects
to an edge of its image. There is no such extension here. It is full-dimensional
simplex adjacency under a subdivision carrier map, with the d-1 common-label
argument above. The implementation additionally checks each retained original
step by original inverse-column identities and its maximal feasible row ratio.

## 4. The global diameter bound and its useful quantitative regimes

Adiprasito--Benedetti Theorem1.4 gives a nonrevisiting facet path in a normal flag
(d-1)-complex with M vertices, of length at most M-d. Apply it to K^B and then
use the carrier map. For any partition satisfying Section2,

    diameter(P) <= M(B)-d
                <= sum_i (2^{|B_i|}-1)-d.                 (3)

The same construction can preserve the ORIGINAL smallest common face of the
requested endpoints. In each block, order their common active labels first
when choosing the two barycentric endpoint chains. The common prefixes cover
all their original common labels. Run the flag construction in the link of
that common refined face. Every lifted carrier continues to contain those
original labels. If the link has n_S vertices and maximal rank d-|S|, its own
bound is n_S-(d-|S|), also checked by the program. Equal endpoints have zero
steps. The global estimate(3) does not require them to be in general position.

If max |B_i|<=k, monotonicity of (2^t-1)/t for positive integers gives

    M(B) <= m*(2^k-1)/k.                                   (4)

For each FIXED k this is linear in m; k=O(log m) would give a polynomial.
The existence of such a partition on arbitrary inputs is NOT asserted.
For blocks of size at most TWO there is the especially transparent formula

    diameter(P) <= m-d+q,                                  (5)

where q is the number of intersecting two-label blocks, at most floor(m/2).
No sum over all visited (h-2)-subsets or uniform numerical gain appears in
this bound. It pays once for the vertices in the actual flag subdivision.
On original flag complexes, singleton blocks recover the classical m-d bound.

The classical theorem is only the normal-flag bound. The derivation of(3)
from the explicit partition and carrier interface is the new project argument;
it is not a new proof of that classical theorem or a claimed best general
polytope diameter estimate.

## 5. A coupled nonproduct family with an all-dimensional linear bound

Start with the product of r triangles, dimension d=2r, and write their variables
as x_i,y_i>=0 with u_i=x_i+y_i<=1. Successively add, for i=0,...,r-2,

    u_i+u_(i+1) <= 2-10^{-(i+1)}.                           (6)

Each cuts off the current codimension-two face u_i=u_(i+1)=1. That face exists:
set these two u's to one and all other u's to zero. All previous neighboring
cuts are then strict. The cut is small enough not to remove any other vertex.
Here is an explicit rational justification rather than an asymptotic epsilon
assumption. In the u-coordinates, the old rows are unit bounds and adjacent-pair
bounds on a path. Alternating column signs and row signs turn these into rows
of a directed-incidence matrix with a ground coordinate, hence every square
minor is0,+1 or-1. Before cut i the right-hand-side denominators divide10^i.
Every u-vertex therefore lies on that grid. Original vertices have at most
one positive variable in each x_i,y_i pair (otherwise the split varies on a
segment), and their u-values are vertices of this bounded path polytope.
Thus a positive old vertex slack in u_i+u_(i+1)<=2 is at least10^{-i}, strictly
larger than the next cut10^{-(i+1)}. Inductively this is exactly a small face
truncation, preserving simplicity and all old facets and creating one genuine
new facet. The final original facet count is m=4r-1.

Partition the two lower labels x_i=0,y_i=0 into r two-element blocks. All upper
u_i facets and the r-1 new cut facets are singleton blocks. On the original
product dual (a join of r triangle boundaries), subdividing those r lower
edges turns every triangle into a four-cycle, a flag complex. Each subsequent
cut in(6) is a stellar EDGE subdivision of the dual edge between two singleton
upper labels. Block refinement and this edge subdivision commute: in the
joined-chain description the two singleton vertices simply undergo the same
edge subdivision; all nontrivial block chains are unaffected.

A stellar edge subdivision of a flag complex is flag. Directly, its new
vertex has the old common-neighbor link and each endpoint, but the old endpoint
edge is removed; any new clique has at most one endpoint and corresponds to
an old clique containing that edge. Old cliques avoiding the removed edge
remain faces. Thus all the resulting block refinements are flag, equivalently
Section2's condition holds for every r.

Each lower pair still intersects at the origin, so it contributes exactly one
extra refined vertex. Consequently

    M=5r-1,    diameter(P_r)<=3r-1.                         (7)

This is not a Cartesian-product argument for the final input. The original
facet-normal matroid is connected: each lower-pair/upper triple is a minimal
linear dependence, and each adjacent upper-pair/cut triple joins neighboring
components. A nontrivial affine Cartesian product would split the genuine
facet normals into two nonzero direct-sum components, impossible here. Dense
coordinates alone are not being used to claim indecomposability.

This differs from #259's small exceptional-union parameter: here the union of
higher minimal nonfaces includes ALL m=4r-1 labels. A bound exponential in
that exceptional union can still be expensive, while the present block count
is linear. No claim is made that one parameter dominates the other universally.

The higher missing-face incidence hypergraph is also connected: the cut label
links missing triangles containing the lower pair on each of its two sides.
The count of higher defects in the tested r2/3/4 cases is4/7/10. Their connectedness
does not force one huge refinement block.

The executable receives only A,b,start,target and DISCOVERS the pair partition.
No truncation history, product chart or incidence graph is passed to it. It
recovers M=9,14,19 and the bounds5,8,11 for d4/6/8. The chosen test pairs have
2/3/4-edge shortest routes; these particular easy pairs do not establish the
all-pair theorem(7). The generic seven-model test separately includes every
unordered pair of the smallest coupled instance.

For these three family tests the independent reference graph is reconstructed
from the explicit stellar history, then ALL vertices and ALL their original
edge neighbors are verified on the final inequalities. Closed neighbor sets
and connectedness of the polytope graph certify completeness. The resulting
13/51/205 vertices and26/153/820 edges are small reference enumerations, not
claims of avoiding full original vertex discovery at these dimensions.

## 6. Exact H interface, but classification is not yet efficient

The implementation queries intersections of ORIGINAL facets using #258's
unaltered feasible-point and strict original-row Farkas certificates. It
classifies ALL minimal nonfaces, examining subsets up to size d+1 and pruning
supersets of already proved empty intersections. This cutoff is complete
because a minimal nonface has all proper subsets of size at most d.

If blocks are not supplied, a deterministic heuristic merges two smallest
blocks whenever a minimal nonface still meets at least three. A merge never
invalidates an already satisfied defect condition and reduces the block count,
so this eventually finds a valid partition. It is NOT minimum-cost block
optimization. At worst the bound degenerates to expensive near-full refinement.
An optional partition is also completely validated, not trusted.

The classification step can be EXPONENTIAL and can effectively enumerate all
original vertex active sets. The program's lack of a supplied original graph
must NOT be described as avoiding original vertex enumeration. A raw combination
cap fails before calling an incomplete list a global flag certificate. Exact
Bland LP discovery also has no polynomial pivot guarantee. Thus(4) is a ROUTE
LENGTH bound for a structural class, not a polynomial runtime statement for
the current recognizer even when a small partition exists.

After classification, the refined oracle answers a virtual face query using
within-block chain comparisons and ONE original intersection query. It lists
M refined vertices (nonempty block faces), but does not enumerate all refined
facets or their global dual graph. The old classical segment recursion asks
only for its needed link graphs. The certificate consumer reruns classification,
partition selection and BFS on those CERTIFIED link graphs, not geometric LP
or inverse discovery. Calling the consumer graph-free would be inaccurate.

The original route is checked separately using the real H-rows, full-rank
active bases, common d-1 rows and maximal original endpoints. Global simplicity
and genuine facet presentation are input hypotheses, not inferred by local
checks. The finite independent reference tests verify those hypotheses on their
models. Arbitrary nonsimple or projected-H inputs are not silently accepted
under the same theorem.

## 7. Why this particular partition budget cannot be universal

The simplex has the single minimal nonface consisting of all m=d+1 labels.
Section2 forces at most two blocks. If there are two nonempty blocks, each
induces a full simplex, so balancing their sizes minimizes(1):

    min M = 2^{floor(m/2)}+2^{ceil(m/2)}-2.                 (8)

The one-block choice has even more vertices. Thus even the BEST partition
in this scheme can have exponential cost although the original diameter is
one. This refutes a universal small-partition premise for this construction;
it is not an obstruction to polynomial routes or to ALL flag refinements.
Existing direct simplex routing already handles this easy input.

Indeed a different hierarchical edge-subdivision schedule flagifies the
boundary of a d-simplex with only d-1 new vertices. Split an edge of its unique
large missing face; the residual large missing face replaces that pair by the
new vertex. Repeat until only missing pairs remain. At each stage the complex
is a join of boundaries of already produced edges and one remaining simplex;
this gives the induction explicitly. The final complex is a join of d zero-
spheres, with2d vertices. This small written example demonstrates why the
limitation in(8) belongs to DISJOINT BLOCKWISE barycentric refinement, not a
claim that every flag-subdivision approach necessarily costs exponentially.
No generic hierarchical optimizer or tests of that schedule are included.

For a general normal flag subdivision, an analogous same-dimension carrier
argument still transfers facet walks to original walks: a common refined
ridge cannot sit in an original face of smaller dimension. Consequently a
polynomially sized suitable flag refinement would be a sufficient global route
mechanism. The present work proves one computable special construction and
its exact limitations, not that such inexpensive refinements always exist.

## 8. Independent tests and losses that must remain visible

The abstract suite generates every downward-closed complex on four labelled
vertices with all vertices present:114 complexes and all15 partitions each,
1,710 tests. It independently constructs the subdivided facets by joined
permutation chains, rebuilds the graph's maximal cliques, and checks the exact
iff of Section2. It passes1,468 valid partitions and4,506 adjacent-carrier checks
for pure complexes. This is a finite test, not a substitute for the proof.

Seven independent original-H graphs have89 vertices and165 edges. Four models
test all unordered distinct endpoint pairs; three use deterministic90-pair
samples. The418 route cases yield:

    refined edges983 = original edges898 + stationary carrier steps85;
    old raw original combinatorial segments863;
    unchanged #253 two-face routes858;
    independent shortest-distance sum854.

The new method has31 nonshortest routes versus9 for raw segments. It is NOT a
benchmark winner or replacement for the old default. Original reentry debt24
coexists with nonrevisiting refined paths, exactly illustrating the distinction
between the two route families. Every refined edge is checked against an
independently enumerated refined complex in the small tests, and every retained
original edge is checked against the independent original graph.

The three coupled-family tests contribute9 additional original edges and
independent graph checks. The global linear bound is from the written all-r
argument, not those three selected pairs. Fifteen malformed/forged/capped cases
are rejected, including missing classification answers, omitted higher nonfaces,
wrong blocks, false refined paths, a carrier diagonal, false original inverses,
false feasibility/separation witnesses and missing boundedness.

A stored full certificate replays with LP maximization, inverse construction
and basis production disabled. It still performs its documented finite subset
and link-BFS computations. Two scripts are the only new runtime/test code;
all seven older dependencies are byte-identical. The full reports, per-model
stages, seven pair tables and ten fixtures regenerate from these sources.

## 9. Verification boundary and next quantitative target

    python3 scripts/test_defect_block_routes.py --model holdout_moment_4_9
    python3 scripts/test_defect_block_routes.py --aux
    python3 scripts/test_defect_block_routes.py --assemble

Run every named model before assembly; a no-argument call runs everything.
The route CLI accepts A,b,start,target and optional blocks. --certificate
expects the inner certificate object. The consumer checks all data against the
original H-input and the complete declared classification, not a supplied flag
assertion. Exact rational tests and written proofs are NOT Lean verification.
No Lean skeleton, publication packet, Actions run or new platform verdict is
included. No accepted source, dependency pin, permissions or secret path changes.

The next meaningful target is a broader low-cost refinement/route construction
with a counted global supply, or a recognition certificate avoiding the current
exponential classification. A guarantee of useful small blocks for every carrier
would be false by(8). A constant numerical progress claim is not being substituted.
This contribution gives a new structural bridge to bounded original-edge routes,
but does not complete the arbitrary-carrier Polynomial Hirsch theorem.

## Primary attribution

Karim Adiprasito and Bruno Benedetti, The Hirsch conjecture holds for normal
flag complexes, arXiv:1303.3598v3, Theorem1.4, Section3 and Corollary1.9;
DOI10.1287/moor.2014.0661. https://arxiv.org/html/1303.3598v3
The normal-FLAG nonrevisiting theorem and its existing subdivision consequences
are classical and are not presented as a new proof here.

Jean-Philippe Labbe, Thibault Manneville and Francisco Santos, Hirsch polytopes
with exponentially long combinatorial segments, arXiv:1510.07678v1,
Theorem4.5/E; DOI10.1007/s10107-016-1099-y.
https://arxiv.org/html/1510.07678v1
This is a limitation of raw original combinatorial segments, not all routes.
Neither published construction is claimed newly implemented in this packet.
