# An all-affine barrier to global coordinate-level routing bounds

## 0. Status and the distinct project contribution

This is a complete written argument with exact executable certificates, NOT
Lean compilation, an axiom audit or a Prove2Me verdict. Baseline main is
`338d1f9e1cc20df86998efa5f0dc6e92916329e8`. The five project instructions and
live PR ownership were read. Coordination comment `5691688010` on #274 was
posted and read back. #275 owns a different all-affine ANGLE-conditioning
barrier and gain-cycle recognition; those sources and its run are untouched.
No blocked #270 companion is retried through this contribution, and #210 stays
reserved/retired.

#274 bounds ordinary diameter by the sum of coordinate-level counts. It is
natural to ask whether choosing a clever global affine chart makes that bound
polynomial for every polytope. This note rules out that precise hope, even on
classical Klee--Minty cubes of true graph diameter d and only 2d genuine facets.
The obstruction is uniform over ALL affine charts, not a list of bad sampled
matrices. In fact it persists in every finite-dimensional injective affine
embedding. It is NOT a diameter lower bound.

The classical family, its bit-labelled vertices and cube graph are attributed
to the source in Section 9. The new project interface is a parallel-length
counting obstruction to ALL global coordinate-level representations, together
with original-row shortest-path and face-adaptive-level certificates. No claim
of historical priority is made for the counting principle or cube geometry.

## 1. The parallel-length lemma

Let V be a finite subset of a real vector space. Suppose there are N pairs
(p_s,q_s) of points of V and one nonzero vector g such that

    q_s-p_s = lambda_s*g,

where the lambda_s are distinct positive real numbers. The pairs need not be
edges for this counting lemma; later they will be genuine original edges.
Let f be ANY affine real-valued functional whose linear part satisfies f_lin(g)
!=0. If K=|f(V)|, then

    N <= binom(K,2).                                         (1)

Indeed the N positive numbers |f(q_s)-f(p_s)| equal
lambda_s*|f_lin(g)| and are all distinct. Each occurs as the absolute difference
of one unordered pair of distinct elements of f(V). There are only binom(K,2)
such pairs. No norm, angle, conditioning assumption or rationality is needed.
Translations do not affect differences. An invertible linear change scales
all vectors parallel to g by the SAME image vector, so the counting obstruction
cannot be removed by making those edges numerically shorter.

More generally, for an injective affine map T into R^r, at least one output
coordinate has a linear part nonzero on g. Apply (1) to that coordinate. Thus
adding arbitrary finitely many AFFINE coordinates cannot eliminate the
obstruction while retaining injectivity. A general extension with a projection
is not an injective affine embedding of the original points, and is not covered.

## 2. The classical bounded simple family

For d>=1 and 0<epsilon<1/2 define Q_d(epsilon) by

    0 <= x_1 <= 1,
    epsilon*x_(i-1) <= x_i <= 1-epsilon*x_(i-1),  i=2,...,d.   (2)

Induction gives 0<=x_i<=1. The two bounds for any coordinate differ by at least
1-2epsilon>0, so at most one row of each pair can be tight. A vertex needs d
independent tight rows; therefore it has exactly one row from every pair.
Conversely, for any bit string b in {0,1}^d, the recursion

    x_0=0,
    x_i=b_i+(1-2b_i)*epsilon*x_(i-1)                         (3)

satisfies (2) and makes the chosen row tight. Its active matrix is lower
bidiagonal with diagonal entries +/-1, hence invertible. This supplies all
2^d vertices, each simple, without assuming a vertex enumeration oracle.

The polytope is full-dimensional: x_i=1/2 is strict for all rows. All 2d rows
are genuine facets. For the lower or upper row of coordinate i, set the other
coordinates to 1/2 and set x_i to its corresponding bound (0/1 for i=1,
epsilon/2 or 1-epsilon/2 otherwise). Every other inequality is strict. The
implementation constructs these exact relative-interior facet witnesses and
checks them after affine changes and positive original-row rescaling.

Two bit strings differing at one coordinate share d-1 independent original
tight rows and therefore are joined by an original edge. Conversely, strings
differing at two or more positions share at most d-2 tight rows and cannot be
adjacent. Their graph is the hypercube, so distance is Hamming distance and

    diameter(Q_d(epsilon)) = d,    genuine facets = 2d.       (4)

This is the classical graph classification, not a newly discovered diameter
result. It is restated because the all-affine obstruction must be tested on
true original edges and compared with true short routes on the SAME inputs.

## 3. Exponentially many distinct lengths in one parallel edge class

Let X_n be the set of last-coordinate values of the n-variable vertices.
X_0={0}, and (3) gives

    X_n = epsilon*X_(n-1) union (1-epsilon*X_(n-1)).           (5)

Each map is injective. The two image sets lie in [0,epsilon] and
[1-epsilon,1], which are disjoint because epsilon<1/2. Consequently

    |X_n| = 2^n                                             (6)

for EVERY real epsilon in the stated interval, not just generic or sampled
rational values.

Fix any prefix of d-1 bits and flip only the final bit. Its two vertices are
joined by an actual edge, and their difference is

    (1-2epsilon*x_(d-1))*e_d.                               (7)

This is positive. The 2^(d-1) different prefix values give 2^(d-1) different
positive lengths. These are PARALLEL edges; the result does not rely on having
exponentially many different edge directions or on a large shadow polygon.
For d=1 the one edge has length one, consistent with the formula.

## 4. Every affine chart has an exponential coordinate alphabet

Apply (1) with N=2^(d-1). For every injective affine T: R^d -> R^r, some output
coordinate takes K different values on the vertices of T(Q_d(epsilon)), where

    K(K-1) >= 2^d,
    K >= k_d := ceil((1+sqrt(1+2^(d+2)))/2).                 (8)

In particular this holds for ALL invertible square affine charts. It holds
with the fixed constant epsilon=1/4: exponentially delicate input parameters
are NOT needed. The sparse inequality input has only 2d rows and constant
nonzero coefficient values. The lower bound is exponential in the number
m=2d of genuine facets, of order 2^(m/4).

At least d output coordinates of an injective affine map are nonconstant on
this full-dimensional polytope. Each has at least two values. Therefore even
the more precise GLOBAL level-charge upper estimate satisfies

    sum_j (|coordinate_j(vertices)|-1) >= k_d+d-2.           (9)

A coordinate-level upper bound that is exponentially large is NOT evidence
that the graph diameter is large. Here (4) gives exactly d. Rather, (8)-(9)
show that optimizing this particular GLOBAL certificate over affine charts
cannot prove a polynomial bound for every polytope.

Some exact lower thresholds are:

| d | genuine facets | distinct parallel lengths | forced levels in some coordinate | true diameter |
|---|---|---|---|---|
|16|32|32,768|257|16|
|32|64|2,147,483,648|65,537|32|
|64|128|9,223,372,036,854,775,808|4,294,967,297|64|
|128|256|2^127|18,446,744,073,709,551,617|128|

The program computes the integer thresholds by integer square roots and checks
both inequalities bracketing the least K. The large counts are consequences
of (5)-(8), not enumerations of the corresponding large graphs or level sets.
The stated bound is NOT asserted to be the exact minimum K over all charts.

## 5. Same-polytope shortest paths and adaptive two-level faces

The positive counterpart is explicit. Decode two vertices into their bit
strings. Flip each differing bit once, in increasing coordinate order, and
recompute (3) after each flip. Section 2 proves every step is an original edge.
The path has exactly the Hamming distance, is shortest, and never reenters any
original facet. Every facet common to its endpoints is preserved. Under a
supplied affine chart, use the transformed ORIGINAL inequalities and transform
the vertices; no auxiliary edge or arbitrary projection is substituted.

There is a useful face-adaptive interpretation. Fix the target choices in the
first i-1 row pairs. Those equalities define a nonempty exposed face and fix
x_1,...,x_(i-1) to their target constants. Among the vertices of that face,
coordinate x_i then has exactly TWO levels:

    epsilon*x_(i-1)(target), 1-epsilon*x_(i-1)(target),

or 0 and 1 when i=1. Both choices occur by (3). If the current vertex is on the
wrong one, changing bit i is one edge within that face and fixes the next
target facet. This supplies a d-phase, one-edge-per-phase proof without a
global small alphabet. The certificate records both levels at every target
prefix face; the consumer recomputes them from the original affine family.
In a dense chart these objectives are the appropriate linear rows of its
inverse, not falsely claimed to be individual physical coordinates.

The consumer also accepts another supplied one-flip-per-differing-bit order
as a shortest path, but the explicit prefix two-level interpretation applies
to the increasing-order construction. The prefix-level certificate is an
independent fact about those actual target faces, not a claim that every
permuted route follows that prefix schedule.

This does NOT produce such a two-level face sequence in an arbitrary polytope.
It demonstrates precisely why the global obstruction leaves adaptive
face-specific invariants open. No general short-phase hypothesis is introduced
as a solved child theorem.

## 6. Distinctions from other obstacles and from known theory

This is not #275's angle-conditioning problem. It uses no angles and makes no
claim about a best Gram metric. In fact the present family can be diagonally
rescaled into signed-root normals: write x_i=epsilon^(i-1)*y_i. Then its pair
rows become y_(i-1)-y_i<=0 and y_(i-1)+y_i<=epsilon^(-(i-1)), with the first
coordinate in [0,1]. Thus a good signed-normal representation can coexist
with the all-affine global LEVEL obstruction. #275 owns the general gain-cycle
recognition algorithm; no duplicate recognizer is added here. #274 already
records the stronger classical curvature guarantee for signed-root normals
with arbitrary right sides.

The result also differs from a large shadow for ONE bad pair of projection
vectors. Every injective affine coordinate collection must contain a detecting
functional for e_d, so the obstruction survives all choices. Nevertheless it
does not prevent a single functional annihilating e_d from having two levels;
x_1 is an explicit such functional for d>=2. Nor does it say every coordinate
has exponentially many values.

The following remain OUTSIDE the obstruction: projective transformations;
nonlinear coordinate functions; replacing the polytope by a combinatorially
equivalent but different realization (the ordinary cube has two levels);
arbitrary higher-dimensional extended formulations with projection; and
objectives chosen adaptively on smaller faces. An injective affine embedding
is covered, but it must not be conflated with a general extension. No
unrestricted Polynomial Hirsch lower bound or counterexample is asserted.

## 7. Exact implementation and independent checks

`scripts/affine_level_barrier.py` recognizes a SUPPLIED affine image of (2).
It checks T*S=S*T=I, all positive original-row scales, and exact binding of
optional original H data to C*S*y<=h+C*S*offset. It does not discover hidden
cube representations of an arbitrary H-polytope. It decodes endpoints directly
from their original coordinates and constructs the bit path with explicit
triangular active-row inverses. It returns all 2d genuine-facet anchors.

Each delivered vertex has a full original-row inverse certificate. Each edge
has d-1 shared original rows and a right inverse. Matrix multiplication checks
rank and the entire H table checks feasibility and exact active sets. No
matrix inversion, elimination, LP, BFS or neighbor discovery is needed by the
consumer. Its multiplication skips zero terms for the large sparse instances;
small and charted paths are additionally accepted by #271's UNCHANGED original
arithmetic auditor, not only by the sparse loop.

The proof of the universal family properties is in Sections 1-5. The software
verifies rational binding, the explicit path and finite identities; it is not
a Lean proof of all real charts or universal correctness of its Python parser.
The source and report labels distinguish proved-formula large counts from
actually enumerated finite ones.

Executed checks:

- Seven complete reference H-graphs in dimensions 1..4, at epsilon1/4,1/3 and
  1/256 where listed: 194 active bases,58 vertices,97 original edges. The324
  tested endpoint pairs use552 edges and agree with independent graph distances;
  all324 paths also pass #271's original consumer.
- Direct enumeration of4,351 actual parallel edges across d1..12 at1/4 and
  d8 at1/3 and2^-160 confirms their distinct positive lengths. This is a finite
  check of the separate all-d/all-real argument, not its replacement.
- Twenty-eight exact affine chart cases across d2..8: identity, dense shear,
  strongly ill-scaled diagonal and a deliberate collision-producing chart.
  The last chart y_d=x_d-epsilon*x_(d-1) collapses half the values to zero but
  still has2^(d-1)+1 levels. The charts are sanity checks, NOT a universal search
  or a claim that their smallest observed K is optimal. One injective5D-to7D
  affine embedding with a constant coordinate is also checked.
- Actual opposite-bit endpoint routes in d16/32/64 have16/32/64 original edges,
  all facet anchors and all prefix-face two-level witnesses checked. Large full
  vertex graphs and exponentially large level sets are not enumerated.
- Twenty-four invalid records are rejected, including an affine functional
  annihilating the parallel direction, altered exact row data, singular or
  falsely inverted charts, invalid epsilon, missing prefix levels, false
  inverse products, omitted facets and repeated or missing bit flips.
- Fourteen saved records replay with route, vertex, active-inverse, facet-anchor
  and old elimination/search producers disabled, checking153 original edges.

The producer and consumer use standard-library exact rationals. Only the
independent reference tests use installed SymPy. All eight final raw reports
and14 complete fixtures are retained in the downloadable export; the clean
replay record states the actual byte comparisons. There is no timing field
excluded from those comparisons. No Lean toolchain, Actions workflow or
Prove2Me submission was run for this research-only work.

## 8. Remaining conjecture-facing target

The signed-level method remains valid and useful in its stated class; this
contribution rules out a universal repair by merely optimizing one global
affine coordinate chart. The appropriate unresolved task is an invariant
that can adapt to actual smaller faces or count only the transitions of a
chosen route without inventorying all levels in advance. The positive prefix
construction here is an explicit test case such a broader theory should cover.
It is not a proof that arbitrary carriers have those prefix faces or a small
adaptive charge. #267's separate total-refinement obstruction is unchanged.

## 9. Primary source and reproduction

B. Gaertner, C. Helbling, Y. Ota and T. Takahashi, *Large Shadows from Sparse
Inequalities*, arXiv:1308.2495v1 (2013), Section4, Definition5/6 and Section4.2,
provide exactly (2), its vertex recurrence and cube-edge classification.
Primary text: https://arxiv.org/html/1308.2495v1 . Their exponential shadow
statement is not substituted for the all-affine level argument in this note.

The unchanged arithmetic dependency is #271
`scripts/original_route_exclusion.py`, blob
`a764196e54970825823cad4575b947b507f95951`. Its complete source is not overwritten
in the repository patch; a byte-identical copy accompanies the standalone ZIP.

    for s in small parallel charts large16 large32 large64 negative audit; do
      python3 scripts/test_affine_level_barrier.py --stage "$s" \
        --out "/tmp/$s.json" --fixtures /tmp/affine-level-fixtures
    done

For saved single-record verification, pass the original input JSON and the
nested certificate to affine_level_barrier.py with --certificate and --output.
