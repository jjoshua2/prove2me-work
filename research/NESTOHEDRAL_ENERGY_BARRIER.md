# Unavoidable uphill defect weight on explicitly realized simple polytopes

## 0. Scope, coordination and the exact new question

Research continuation from main `2c517a877e8aab885ae1583d97fc2e2ae6d9b017`.
The exact mixed-defect accountant and carrier map from #262 are imported
UNCHANGED. Merged #263 and active #264 already establish real polytopal
plateaus escaped by neutral moves. Their results are not repeated here.
The cactus-incidence and graphical-refinement continuations recorded on #263
are separately owned and are not modified.

The new question is whether arbitrarily many neutral/auxiliary moves always
avoid having to increase the weight W=sum_high(|N|-2). The answer is NO.
There are explicit simple polytopes for which ANY edge-stellar flagification,
and even ANY sequence ending below the initial W, must first exceed it by
an amount growing with dimension. The proof concerns ALL such sequences,
not a fixed selector, a finite search radius, or a failed heuristic run.

For the smallest realized example, dimension6 and70 genuine ORIGINAL facets,
W starts at7 and every successful refinement must reach at least10. An
explicit eleven-step refinement attains peak10 and becomes flag. Thus the
minimum possible peak is exactly10. Its length is not claimed optimal.

These are NOT diameter lower bounds. The whole original graph has diameter12
by exhaustive exact graph computation; a classical coordinate-order argument
gives all-pairs upper bound21 without using flagification. The constructions
belong to the classical nestohedron/generalized-permutohedron class. The
contribution is the realization of arbitrary higher-defect patterns, the
first-ground-pair barrier, its sharp Fano witness, and the exact auditable
integration. No historical priority is claimed for every equivalent lemma.

No new Lean source, compilation, axiom audit, Actions gate or Prove2Me
submission is included. Written proofs, classical inputs and exact Python
checks remain distinct. Python and JSON are not Lean-extracted.

## 1. Realize any proper finite defect kernel inside a polytopal sphere

Let K be a proper simplicial complex on G=[n], n>=3, with every singleton a
face. Its minimal nonfaces are a complete finite antichain of sets of size
at least two; K need not be pure, spherical or itself polytopal. Define

    B = {{i}: i in G} union {S subset G: S is NOT a face of K}.       (1)

This is a connected building set. Two intersecting nonsingleton members have
a union which still contains a nonface, hence is a nonface. Two singleton
members either coincide or do not intersect. A singleton intersecting another
member lies inside it. Since K is proper, G itself is in B.

Use the classical nestohedron

    P_K = sum_(S in B) Delta_S,
    Delta_S = conv{e_i:i in S}.                                  (2)

The full simplex Delta_G is a summand, so P_K has dimension n-1. It is compact.
The building-set/nested-set theorem gives a simple polytope and identifies its
facets with proper B-members. These are classical results: Postnikov,
*Permutohedra, associahedra, and beyond*, Section7, Theorem7.4,
Propositions7.5 and7.10. They are not new assumed oracles.

### Exact ORIGINAL inequalities, including equality to (2)

Put C=|B| and h(T)=#{S in B:S subset T}. Then

    sum_i x_i=C,
    sum_(i in T) x_i >= h(T), T in B minus {G}.                    (3)

Every point of (2) satisfies these inequalities. An omitted nonempty subset
T is a face of K, so the only B-members inside it are its singletons and
h(T)=|T|; its inequality follows by adding the singleton inequalities.
Thus all subset lower bounds follow from (3).

For a linear objective with coefficients c_(pi1)<=...<=c_(pin), telescope:

    c.x = c_(pin)*C
          -sum_(j<n)(c_(pi(j+1))-c_(pij))*x({pi1,...,pij}).

All differences are nonnegative. The subset bounds give a global upper
bound, attained by selecting the highest-coefficient coordinate from EVERY
Delta_S. Consequently (3) and (2) have the same support function. The set (3)
is bounded because every coordinate has its singleton lower bound and their
sum is fixed. Equality with (2) follows by convex separation. This argument
also proves that enumerating all strict coefficient orders finds all vertices:
each vertex has a strict exposing objective, which can be made coordinate-
distinct inside its open normal cone.

Eliminate x_(n-1)=C-sum_(i<n-1)x_i. For a label T not containing n-1, the
original inequality row is -1_T with bound -h(T). When n-1 lies in T, the row
is 1_(G\T) on the remaining coordinates with bound C-h(T). This is an affine
coordinate chart of the same polytope, NOT projection of an extension.

Every proper B-label is genuinely a facet. For the supporting objective
-1_T, the exposed summands include Delta_T and Delta_(G\T), the latter from
Delta_G. Their direction spaces are disjoint and total dimension n-2. The
whole exposed face lies in the equality for T, so its dimension is exactly
n-2. This includes singleton T. Facet counts in this note refer to these
irredundant ORIGINAL inequalities.

### Its only higher minimal nonfaces are the original ones

In the nested complex, two proper B-labels are compatible when one contains
the other, or when they are disjoint and their union is not in B. A minimal
nonface of size>=3 must therefore be a pairwise compatible antichain whose
union lies in B. If such an antichain contained a nonsingleton B-member U,
then U already contains a nonface of K. The union of U with any disjoint
other member is consequently in B, producing an incompatible PAIR. This
contradicts higher minimality. Overlapping incomparable members are already
incompatible pairs as well.

It follows that every higher minimal nonface consists solely of singleton
labels. For those labels, minimal failure is precisely a minimal nonface of
K. Conversely, each original higher minimal nonface remains minimal in the
nested complex, because all its proper singleton collections are faces.
Thus

    higher defects of the dual boundary of P_K = higher defects of K. (4)

Only additional missing pairs, involving the new nonsingleton labels, occur.
In particular K embeds as the induced complex on the n singleton labels.
The n designated labels are called GROUND labels below. They are a SUBSET
of the original polytope's facet labels. Other original facet labels and
subsequently inserted vertices are both outside-ground labels; neither is
silently removed from the actual facet count.

As a separate literal construction, start with the boundary of the simplex
on G and subdivide every proper original nonface S in decreasing |S|, with
new label S. This realizes the same nested complex: the maximal nested sets
consist of an initial set of singletons followed by a chain of nonfaces.
The independent test implements these FACE stellar subdivisions directly
and compares every final maximal face with (3)'s complete vertex table.
These input-defining face subdivisions are not counted as later edge-repair
steps. Their number, and the number of original facets, may be exponential.

If f(K) counts all faces including the empty face, then

    m = n + 2^n - f(K) - 1.                                    (5)

There is no polynomial-size realization claim. The constructor enumerates
subsets and pairs of facet labels with explicit caps; a cap returns failure,
not a partial completed realization.

## 2. A sequence-independent first-ground-pair obstruction

Now assume K has exactly the triples of a Steiner triple system on n>=7
labels as its minimal nonfaces. Every pair belongs to exactly one triple.
There are q=n(n-1)/6 triples, and every label belongs to (n-1)/2 of them.
By (4), the original realized sphere has W0=q, even though it has additional
vertices and missing pairs outside G.

Consider ANY finite sequence of valid stellar EDGE subdivisions. Before an
edge with BOTH endpoints in G is subdivided, the induced complex on G is
unchanged. Indeed an edge involving an outside-ground vertex is not contained
in any ground-only face. It removes none of those faces and creates no new
ground-only face. Thus all q original triples remain minimal nonfaces and
all original ground pairs remain faces.

In particular, a sequence reaching flag, or merely reaching W<q, MUST have
a first ground-pair subdivision E={u,v}. The preceding sequence may be
arbitrarily long and may use neutral or increasing moves. No restriction on
its intermediate weights is needed.

Let {u,v,w} be the unique original triple containing E. At the first ground
pair operation:

1. The other q-1 original triples remain minimal nonfaces. They do not contain
   E, and all their original pairs remain edges after this one subdivision.
2. Exactly n-3 triples meet E in exactly one endpoint: (n-3)/2 through u and
   (n-3)/2 through v. For each such N, with fresh subdivision vertex z, the
   triple {z} union(N minus E) is a nonface by the stellar membership formula.
3. These n-3 triples are DISTINCT and MINIMAL, even after every preceding
   outside-ground subdivision. Their two old endpoints form a ground edge.
   A pair {z,p} is a face exactly when {u,v,p} was a face before the operation.
   The only original ground triple containing {u,v} which was a nonface is
   {u,v,w}. Neither residue endpoint can be w, by unique pair incidence.
   Hence both {z,p} and {z,q} are faces. No old auxiliary label can supply a
   smaller nonface contained in this entirely ground-plus-z triple.

All listed survivors and births have weight one, giving

    W immediately afterward >= (q-1)+(n-3) = q+n-4.             (6)

Therefore

    every flagification or net descent below W0 has peak W >= W0+n-4. (7)

This is a proof about ALL valid edge-stellar sequences, not enumeration of
first moves from the initial state only. Arbitrarily many neutral preparation
moves cannot evade it. It also does not require that the preceding moves were
productive in the original defect kernel.

Binary Steiner systems provide infinitely many examples. Take the nonzero
vectors of F_2^r, n=2^r-1, with triples {a,b,a+b}. Distinct nonzero a,b have a
unique third nonzero vector, proving the design axioms. The realized polytope
has d=n-1 and (7) forces extra weight at least n-4=d-3.

Thus NO FIXED additive allowance above initial W suffices for all simple
polytopes in an edge-stellar flagification strategy, even with an unlimited
number of neutral steps or unbounded checkpoint length. This does not rule
out polynomially growing allowances, polynomial-length refinements, higher-
dimensional stellar operations, other same-dimensional subdivisions, or
routes constructed without flagification. A required weight peak is not a
lower bound on the number of operations or on an original graph distance.

## 3. Sharp Fano instance and an explicit uphill escape

For n=7 the ground triples are

    012,034,056,135,146,236,245.

The building set has71 members. The original polytope is6-dimensional with
70 genuine facets,1,050 simple vertices and3,150 ordinary edges. The dual has
1,806 missing pairs and precisely those seven higher triples. All of these
counts are independently checked on the exact ORIGINAL H-system.

Every first ground pair consumes one triple and forces four newborn triples.
The sequence-independent lower bound is W>=10, not merely a local stall at7.
The following kernel labels describe an explicit eleven-step refinement:

    (0,1),(3,7),(6,7),(3,6),(0,10),(1,10),
    (0,3),(0,6),(1,3),(1,6),(2,4).                           (8)

Fresh labels in this seven-label notation start at7. In the full70-label
sphere, replace any new label t>=7 in (8) by t+63. The program audits every
step against the COMPLETE full minimal-nonface catalogue using #262 unchanged.
It obtains

    7,10,8,6,9,7,5,4,3,2,1,0.                              (9)

The maximum is10 and the last complex is flag. Consequently the minimum
possible peak over ALL eventual edge-stellar flagifications is EXACTLY10.
Eleven is a supplied successful length, not a minimum-length assertion.
There is a second uphill step6->9; non-increasing motion is not imposed inside
the trace. All old vertices remain vertices; this is subdivision, not fusion.

The final sphere has81 vertices and2,028 maximal facets. The classical
Adiprasito--Benedetti normal-flag theorem gives a refined facet path of length
at most81-6=75. The existing stellar carriers send every refined adjacency
back to equality or an actual previous adjacency, so original path length
does not increase. Every test route also preserves the original facets common
to its endpoints and passes the original H inverse/maximal-step audit.

The bound75 is WEAK. It is included to document a correctly completed repair,
not as a record diameter improvement. Complete original BFS gives diameter12;
the next section supplies a separate structural bound21. No long-distance
conclusion is drawn from the compulsory uphill move.

## 4. A direct polynomial route for the whole realization class

Every vertex of (2) is exposed by a generic coordinate order, with its
coordinate vector obtained by choosing the last element of each B-member.
Between any two such orders, bubble sorting makes at most binom(n,2)
adjacent transpositions.

At a wall for a single adjacent transposition, only those two coordinate
values tie. Each summand's exposed face is a point or the segment between the
two corresponding coordinate vectors. All nonpoint segments are parallel,
so their sum is a point or one ENTIRE exposed segment of P_K. Thus consecutive
vertices of the sorting trace are equal or actual ORIGINAL neighbors.
Delete stationary transitions. This proves the classical bound

    diameter(P_K) <= binom(n,2) = d(d+1)/2.                  (10)

This is the standard braid-chamber/generalized-permutohedron argument, not a
new classical diameter theorem. Endpoint coordinate orders are part of this
structured route constructor's input; no universal original-H recognition
claim is made. The full small test obtains such orders by enumerating n!.
For arbitrary models that enumeration is not a polynomial-time claim.

This comparison is essential: arbitrary higher-defect kernels can be
realized in a class with an explicitly polynomial ordinary-edge route.
Defect weight and its compulsory temporary growth therefore do not themselves
measure original distance. A promising general strategy may need to bypass
rather than fully simplify complicated defect patterns.

For the Fano example, (10) is21 and the actual graph diameter is12. On32 tested
endpoint pairs, carrier routes use237 edges versus230 shortest;7 are
nonshortest. Sorting routes use263 edges and17 are nonshortest. These are
research comparisons, not superiority or shortestness claims.

## 5. Verification, finite versus general statements, and replay

    python3 scripts/test_nestohedral_defect_barrier.py

Stages algebra/family/geometry/negative/assemble can be run individually.
The negative saved-fixture checks require geometry to have run first. All
assembly fields are bound to the two new source hashes and the TWO unchanged
dependencies. Explicit caps limit subset, facet-pair and permutation enumeration.

Algebra stage:48 proper complexes, including all nonempty three-uniform
catalogues on3/4 labels and mixed random antichains on4/5 labels. It checks272
literal input-realizing face subdivisions,2,670 generic coefficient orders,
1,069 distinct vertices,15,308 exact original-row slacks and1,069 complete
nested-facet comparisons. These abstract inputs are not assumed polytopal;
the explicit building-set construction produces their polytopal realizations.

There are96 additional first-ground-pair checks after randomly generated
outside-ground subdivision prefixes, including99 weight-increasing prefix
steps. These are adversarial finite checks of the general argument, NOT the
proof for all possible prefixes or a claim that their artificial prefix
complexes are polytopal.

Binary design checks r3,4,5 have respectively n7,15,31 and W7,35,155. All21,105,
465 possible first ground pairs have complete incidence/birth certificates,
with forced peaks10,46,182 and excesses3,11,27. Exact facet counts70 and29,733
are computed from ground subset membership for n7 and15. Full polytope
coordinates and graphs are constructed ONLY for n7. The n31 facet count is
not enumerated. The all-r result follows from (1)--(7), not those three tests.

The full Fano geometry checks all5,040 generic orders,1,050 active bases,
73,500 original row slacks,70 genuine-facet relative-interior witnesses and a
strict interior point. Literal relative stellar subdivision produces exactly
the same1,050 maximal dual faces. A separate pair-graph clique/splitting
procedure verifies the COMPLETE nonface catalogue, including absence of
omitted higher defects. Final maximal-clique enumeration matches the2,028
literal refined facets, independently checking flagness.

ALL6,084 refined adjacencies are transported through ALL11 subdivisions:
66,924 intermediate adjacency checks. Every original BFS source is explored,
giving1,102,500 ordered distances and exact graph diameter12. The original
and refined graphs are EXPLICITLY ENUMERATED. There is no graph-free or
polynomial-size general graph-construction claim.

Thirty-two endpoint pairs yield242 refined edges,237 transported original
edges andfive stationary carrier deletions. The separate sorting paths add263
ordinary-edge occurrences. Every delivered edge is checked against the same
original H-system, and all shared original facets are preserved by carrier
paths. These two route families are not necessarily the same or shortest.

The saved JSON fixture includes the exact H-system, building set, all missing
faces, the full eleven-step accounting, genuine-facet witnesses and two full
route examples with all needed original basis packets. A separate auditor
reconstructs the model and validates the finite certificates and actual edges
without objective-order enumeration, inverse production, geometric LP or route
BFS. Its13 carrier edges and13 sorting edges are replayed. It deliberately does
NOT recompute a graph-diameter field. Twenty-two malformed, incomplete or
forged requests are rejected, including missing first-pair cases, understated
births/peak, changed H-rows, false facet/inverse data and incomplete routes.

A clean workspace with only these two scripts and the frozen dependencies
reruns all four stages. Source hashes and all nontiming fields agree; the full
saved fixture agrees byte-for-byte because its payload excludes runtimes.
The raw reports and full fixture are bundled and regenerate. Committed compact
summaries are labeled derived and identify the full report by hash. None of
this constitutes a Lean proof of the code or an authenticated platform verdict.

## 6. Consequence and next genuinely open step

The plateau work #263/#264 is valid and useful, but arbitrarily long neutral
preparation is not universally enough. Any global defect-energy argument must
budget unavoidable positive debt, not just guarantee eventual strict descent
at bounded checkpoints. A fixed debt allowance is already excluded. Polynomial
allowance or total cost is NOT excluded or established here.

The construction also supplies a general way to turn abstract defect designs
into honest convex-polytopal stress tests, with explicit original facet counts.
Those counts can grow exponentially, so small abstract ground size must not
be substituted for original input size. All coordinate/order routes and
flag-carrier paths refer to the original polytope, not an extension projection.

The unrestricted Polynomial Hirsch objective remains a polynomial original-
facet bound for arbitrary carriers. The relevant next task is a repair ledger
controlling both unavoidable births and total schedule length, or a direct
route construction which can ignore higher defects as the special structured
class here already does. No missing global bound is inserted as an assumption
and called a completed result.

## Primary mathematical sources

Alexander Postnikov, *Permutohedra, associahedra, and beyond*, arXiv:math/0507163,
Section7 (Theorem7.4, Propositions7.5/7.10) for the classical building-set,
nested-face and simplicity statements. Original HTML consulted:
https://arxiv.org/html/math/0507163 . The support and order-wall arguments
used for (3) and (10) are written explicitly above.

Karim Adiprasito and Bruno Benedetti, *The Hirsch conjecture holds for normal
flag complexes*, arXiv:1303.3598v3; Mathematics of Operations Research,
DOI10.1287/moor.2014.0661. https://arxiv.org/html/1303.3598v3 . Its normal-flag
bound is a classical external theorem, not newly proved or published here.
The withdrawn arXiv1303.5885 is not used.
