# Nonsegment summands from final inequalities: exact capacity and joint packing

## Scope and provenance

This is an add-only continuation of PR #210 from
`4b82eedf97812059490e545a8a4d02822597f87b`. The preceding complete segment catalogue
is used unchanged. Its genuine remaining examples include segment-free polytopes
that have higher-dimensional Minkowski summands. This packet treats those directly.

The input is the ORIGINAL rational H-system R={x:Ax<=b}, requested endpoints,
and one or more finite candidate SHAPES given by point lists. Candidate scale,
residual inequalities, residual route and decomposition equality are not inputs.
This does not universally discover candidate shapes. Unlike a segment factor,
a triangle factor can have directions absent from an antipodal walk, so the
preceding segment-direction completeness theorem is not misapplied.

Main results:

1. For a candidate with k+1 listed points, a finite collection of positive
   dependence certificates in k allocation variables characterizes exactly
   the scales for which it is a Minkowski summand of R. Original-H LPs compute
   the maximal scale; original-row multipliers and a sharp point certify it.
2. For several candidates the SAME construction returns the complete region of
   simultaneously removable scales. Its nontrivial inequalities have NONNEGATIVE
   coefficients: it is a down-closed packing region. This replaces an invalid
   generalization of order-independent segment removal.
3. An integrated constructor recovers a simplex, pyramid, point or feedback core
   when recognizable, then returns edges independently checked on the original
   R. All five small test models and the large family are segment-free.

Farkas' alternative, finite convex hulls, and Minkowski summand/deformation cones
are classical. This work is an explicit original-H certificate and routing
implementation; no priority claim is made for every equivalent elimination or
summand-cone formulation. The two new Lean modules are UNCOMPILED finite cores,
not an end-to-end formalization of the Farkas alternative or circuit completeness.
No new Prove2Me verdict, hosted run, workflow or pin change is claimed.

## 1. Reduction to a small allocation system

Translate the first listed candidate point to zero, and write

    Q=conv{0,g_1,...,g_k},   h_i=max(0,A_i g_1,...,A_i g_k).

The implementation records this origin convention in its input hash. If the
user's original candidate was Q+v0, the maximal scale is unchanged and the
corresponding residual is translated by -t*v0. Affine dependence and redundant
listed points are allowed; exact duplicate points are removed. Complexity uses
k=number of distinct listed points minus one, NOT automatically affine dimension.

For t>=0 the endpoint erosion is

    E(t)={p:A_i p<=b_i-t*h_i}.

Always E(t)+tQ is contained in R. Equality holds precisely when EVERY x in R
has coefficients theta in R^k with

    -A_i G theta <= b_i-A_i x-t*h_i   for every original row i,
    -theta_j <= 0                     for j=1,...,k,
    sum_j theta_j <= t.                                      (1)

Indeed q=G theta belongs to tQ and p=x-q belongs to E(t). Conversely any such
Minkowski representation provides these coefficients. The candidate need not
be a simplex: barycentric variables parameterize any finite convex hull.

Let C be the (m+k+1)-by-k matrix on the left of (1). It does not depend on x,t.
Farkas' alternative says (1) is feasible iff every lambda>=0 with lambda*C=0
has nonnegative weighted right-hand side.

## 2. Why only small positive circuits need checking

Intersect the nonnegative null cone with sum(lambda)=1. This is a compact
polytope. Every point is a convex combination of its vertices. A vertex has
support I with rank(C_I)=|I|-1 and a strictly positive unique dependence; its
support size is at most k+1. These are the positive circuits enumerated here.
Conversely each such minimal positive dependence is a vertex of that section.
Thus checking them is COMPLETE, not an assumed sample of useful dependencies.

There are at most sum_(s<=k+1) binom(m+k+1,s) supports to inspect. A zero row of C
is a singleton circuit and cannot occur in a larger minimal support. The code
handles those singletons and omits their supersets exactly. For a small shape
supported on few original row directions, this can greatly reduce enumeration.
Every other support is tested by exact rational elimination. A prechecked cap
rejects oversized searches BEFORE returning any partial certificate.

For a positive circuit split its coefficients into lambda_i on original rows,
mu_j on nonnegativity constraints, and nu on the total coefficient constraint.
Its zero-normal identity is

    sum_i lambda_i A_i G_j = nu-mu_j.

Put

    v=sum_i lambda_i A_i,
    beta=sum_i lambda_i b_i,
    gamma=sum_i lambda_i h_i-nu.

Its necessary-and-sufficient allocation inequality is

    t*gamma <= beta-v*x.                                    (2)

The right side is nonnegative for x in R because lambda_i>=0. Therefore circuits
with gamma<=0 impose no restriction at t>=0. For the remaining circuits,

    t_max = min_c [beta_c-max_(x in R) v_c*x]/gamma_c.         (3)

This is polynomially many original-H LP calls for FIXED k. It is not polynomial
in unrestricted candidate size: for many candidate vertices this enumeration
can be exponential. No original vertex graph is enumerated by discovery.

A nonempty compact R and nonpoint Q have finite capacity: any direction with
positive width in Q supplies the obvious width-ratio upper bound. The standalone
implementation also handles noncompact input when the capacity is finite, but
explicitly declines its finite-capacity mode if no restrictive circuit exists.
The integrated all-endpoint router additionally certifies original boundedness
using original-row dual bounds on both signs of EVERY coordinate.

## 3. Exact equality and sharp maximality certificates

For each restrictive circuit, the stored Farkas multiplier y>=0 satisfies

    y*A=v_c,     y*b<=beta_c-t_max*gamma_c.                   (4)

Together with full circuit coverage, (4) verifies (2) for ALL x in R. Farkas'
alternative then gives allocations (1) for every such point and proves the
entire equality R=E(t_max)+t_max Q. A separately checked residual feasible point
is retained too, rather than relying on an unexamined nonemptiness claim.

One circuit c* and an original feasible point x* satisfy

    beta_c*-v_c* x* = t_max*gamma_c*.

Every larger scale makes that circuit's weighted allocation right-hand side
negative at x*. Hence the scale is maximal. This excludes EVERY proposed
residual K, not just our chosen erosion: if R=K+tQ then K is contained in E(t),
so failure for E(t) excludes K as well.

Verification reconstructs the complete positive-circuit list, checks all normal
identities and coefficient signs, and validates the sharpness point. It invokes
no LP solver. The discovery LP routine is the existing exact Bland simplex,
with explicit caps and no claimed polynomial pivot or strongly polynomial runtime.

### A triangle needs a genuinely three-way test

Let R=-conv{0,e1,e2} and Q=conv{0,e1,e2}. At x=0, attempting positive t requires

    theta_1>=t, theta_2>=t, theta_1+theta_2<=t.

Every pair is feasible; all three are impossible. The exact test at t=1/4 checks
all 15 two-constraint subsystems of the full allocation system as feasible,
while a three-row positive circuit certifies t_max=0. The erosion itself is
nonempty at t=1/4, so neither nonempty erosion nor pairwise compatibility would
prove Minkowski equality. The earlier two-row segment criterion cannot simply
be retained for a triangular candidate.

## 4. Several candidates: a complete joint packing region

For candidate shapes Q_l=conv{0,G_l}, introduce independent allocation blocks
and scales t_l>=0. The original-row part of (1) becomes

    -sum_l A_i G_l theta_l <= b_i-A_i x-sum_l t_l h_il,

with nonnegative coefficients and one total bound sum(theta_l)<=t_l per block.
Positive circuits now have support at most K+1, where K=sum_l k_l. Write nu_l
for the coefficient of block l's total bound. Each circuit gives

    sum_l gamma_cl*t_l <= delta_c,
    gamma_cl=sum_i lambda_i h_il-nu_l,
    delta_c=beta_c-max_(x in R) v_c*x.                       (5)

Primal AND dual original-H witnesses certify every delta_c exactly. A merely
conservative upper bound would produce only a sufficient region, so the verifier
checks matching primal/dual values for every retained circuit.

### The coefficients are nonnegative, not arbitrary signed constraints

For an external minimal circuit (some original lambda_i positive), its block
multipliers satisfy

    nu_l = max(0, v_c*g_l1,...,v_c*g_lk).

If nu_l were strictly larger, every nonnegativity multiplier in that block
would be positive as well. The support would contain the complete internal
simplex dependence (-e_1,...,-e_k,ones), contradicting minimality. If nu_l=0,
all v_c*g_lj are nonpositive and the same equality holds. Therefore gamma_cl
is a support-function subadditivity deficit and is nonnegative. Internal-only
circuits have no positive scale restriction and are safely excluded.

Consequently (5), together with t>=0, is an exact down-closed packing region.
It is convex. For compact R and nonpoint candidates each coordinate is bounded
by a width ratio, so it is a compact polytope. The implementation can optimize
any supplied linear extraction objective with an additional primal/dual
certificate. This is NOT a claim to optimize residual diameter or to discover
the best candidate shapes.

### Nonsegment maximal removals do not commute

Let T=conv{0,e1,e2}, S=[0,1]^2, and R=T+(-T). The hexagon R satisfies

    |x|<=1, |y|<=1, |x+y|<=1.

Both T and S have individual removable capacity one. But the exact simultaneous
region for R=K+sT+tS is

    s>=0, t>=0, s+t<=1.                                    (6)

The computed coefficient system simplifies to these three inequalities through
sequential Farkas-certified redundancy removal. Removing T maximally leaves
-T, which has zero S capacity; removing S maximally leaves a segment, which has
zero T capacity. Twenty-five coefficient pairs are checked against independent
complete planar Minkowski reconstruction, agreeing exactly with (6).

This is a failure of commutativity between two FULL-DIMENSIONAL candidate shapes,
not just between parallel copies of a segment. Separate maxima must not be
mistaken for a feasible simultaneous extraction. In the segment-only case the
previous transverse-capacity theorem explains why the region instead has a
product structure in distinct factor directions.

## 5. Original-edge routing after a nonsegment extraction

The integrated constructor uses the certified E(t_max) H-system and sequential
original-row redundancy proofs. It recognizes point/pyramid/feedback cores using
existing routines, and adds a direct simplex certificate: d+1 retained facets,
each omitted-row solution feasible and strictly off its omitted row. All those
d+1 points are checked, giving a full simplex model rather than assuming a graph.

At a requested original vertex x, the sum of all tight original normals exposes
x uniquely. The proved Minkowski equality then forces a unique maximizing point
of tQ; subtracting it recovers the actual residual vertex. The same original-row
multipliers certify its supporting objective. The old implicit wall lifter is
reused without changes, and every final edge is ALSO rechecked on the original
R by feasibility, active rank, common rank d-1 and endpoint blockers.

For a single candidate with v distinct vertices and an L-edge residual route,
there are at most v-1 genuine added changes per linear objective interval:
each candidate's affine support function wins on one interval and cannot return.
Thus the classical vertex-sensitive lifting estimate is

    lifted length <= L+(L+1)(v-1) = (L+1)v-1.                (7)

The verifier checks non-return of these candidate choices along each interval.
It also retains the older direction-sensitive estimate, using the smaller
per-interval bound when appropriate. Formula (7) is a classical Minkowski
fiber/lifting consequence, not a newly claimed best diameter theorem.
For a triangle over a simplex core B=1 it gives 5; over a pyramid B=2 it gives 8.
The returned routes need not be shortest or remain in the requested endpoints'
smallest final face. Carrier-specific applications must use that actual face.

## 6. Segment-free examples, including a large nonproduct family

The five small original-H models are a tetrahedron plus a nonparallel triangle,
two nonparallel triangles, two nonhomothetic tetrahedra, the product of two
triangles, and a pyramid plus a triangle. The earlier antipodal catalogue proves
ALL FIVE have zero segment factors. Their complete original graphs and complete
Minkowski reconstructions are independently checked by vertex/hyperplane methods
in the small TEST HARNESS, not passed as inputs to recognition.

The tetrahedron-plus-triangle example has 11 vertices and 12 facets. A maximal
scale-one triangle removal recovers the tetrahedron and a three-edge sample route.
The original segment recognizer genuinely has nothing to remove there.

### A segment-free family with billions of vertices

For d>=4, let P be the pyramid with apex (1,0,...,0) and cube base at z=0:

    z>=0, z-x_i<=1, z+x_i<=1  for 1<=i<=d-1.

Add t*conv{0,e1,e2}, t=3/7, in two horizontal coordinates. The FINAL H-description
is obtained by replacing the first two upper bounds with z+x_i<=1+t and adding

    2z+x_1+x_2<=2+t.

All other rows are unchanged. There are exactly 2d genuine final facets. For
fixed z, put w=1-z. The first two coordinates form [-w,w]^2+t*triangle, a pentagon
for z<1 and a triangle at z=1. The untouched coordinate pair (d>=4) forces z<=1.
Hence this is exactly P+tQ, not a guessed H-relaxation.

Its vertices are those of the base pentagon times the (d-3)-cube, plus the three
top vertices. Thus

    number of vertices = 5*2^(d-3)+3.

The face z-x_1=z-x_2=1 is a pyramid over a (d-3)-cube. Its 2^(d-3) apex-to-base
edge directions are all genuine directions of the full polytope.

The family is SEGMENT-FREE. Project a hypothetical segment factor into (z,x_i)
for each untouched coordinate i>=3. Those projections of R are triangles, which
have no nonzero segment factors (a shortest parallel fiber is a point). Thus
the factor has z-component and all untouched components zero. Expose z=1:
its full segment then survives in the top triangle, again impossible unless
it is zero. This proves the claim in all d, separately from finite tests.

It is not an affine Cartesian product. Its genuine facet normals form a connected
linear matroid: the rows -e_z and e_z-e_i form a basis, and each e_z+e_i creates
an elementary dependence linking e_z with coordinate i. The last mixed row
also belongs to this connected component. A nontrivial affine product would
split the facet normals into two nonzero direct-sum components. This does not
claim absence of projective models or of other higher-dimensional summands.

Only the normalized TRIANGLE SHAPE is supplied. Its scale3/7, the residual pyramid,
the support objectives and route are discovered. The large tests give:

| Dimension | Genuine original facets | Proved vertex count | Sample ordinary edges |
|---|---:|---:|---:|
|12|24|2,563|4|
|24|48|10,485,763|4|
|32|64|2,684,354,563|4|
|8, hidden affine coordinates|16|163|3|

All have an eight-edge sufficient all-endpoint bound from (7). No shortestness
claim is made for these sample routes. Original vertex graphs are not enumerated.
The 32D extraction needs only four restrictive circuit inequalities; rows
annihilating the candidate span contribute only trivial singleton circuits.
Unknown dense affine coordinates/translation and row scales are tested in the
8D case, with the transformed candidate shape supplied but not its scale/chart.

### Why higher-dimensional candidate discovery remains separate

A product of two triangles has an antipodal two-edge walk: each edge changes
one factor. A true triangular factor has three edge directions, only one of
which that walk need contain. So the previous complete SEGMENT-direction argument
does not recover arbitrary simplex shapes. The new input requirement is explicit
and cannot be removed by reusing that proof unchanged.

## 7. Formalization, execution and remaining target

Two new Lean files contain 194 lines and 12 axiom printouts. They prove scaled
finite-hull support bounds, original-row combination bounds, allocation support
deficits, a sharp scalar maximality implication, a three-way infeasibility
control, packing-region convexity/downward closure, and finite route arithmetic.
They are UNCOMPILED. The full Farkas alternative, positive-circuit generation,
whole global equality, joint completeness and original-H route algorithm are
proved/described above and executable, not all new complete Lean declarations.
No unknown analytic diameter theorem or mission ancestor is added as an axiom.

Four new Python files contain 654 lines. They reuse existing exact LP, redundancy,
core and wall-lifting code unchanged. Discovery's circuit cap is checked before
partial results can escape. Original boundedness for point/pyramid core claims
has its own complete coordinate-dual certificate. Verification calls no simplex
or path search; it recomputes finite circuit/rank/algebraic evidence and the
explicit core formula. Immutable circuit enumeration is cached for repeated
verification, without treating cached routes as free cost.

The final suite checks 255 route certificates with 479 ordinary-edge occurrences.
Five independently enumerated small graphs have 46 vertices, 84 edges and 456
ordered distance checks; all 251 unordered endpoint pairs are routed. Nine complete
antipodal catalogues (five small, four large) independently confirm zero segment
factors. There are 105 independent positive-circuit/feasibility comparisons,
15 pairwise checks in the triangular obstruction, four old-segment specializations,
25 independently reconstructed joint coefficient points, and 25 rejected forgeries.
The execution receipt is the authoritative count if a later test revision changes
these values. Exact code hashes and unchanged dependencies are recorded there.

Seventy-eight returned small routes are longer than shortest graph distances;
this limitation is counted, not suppressed. The new example scale certificate is general for
supplied finite shapes, but the short residual recognizers remain sufficient,
not universal. Optimizing extraction weights is not automatically minimizing
diameter, and an arbitrary segment-free carrier need not contain any useful
small finite candidate. The remaining target is candidate-shape discovery and
routing beyond the recognized residuals, with controlled total candidate size.
No Polynomial Hirsch conclusion follows merely from these recognition successes.

## Primary references

Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums
of polytopes, Canadian Mathematical Bulletin 62 (2019), 741--755,
arXiv:1806.07643v1; DOI 10.4153/S0008439518000668.
https://arxiv.org/html/1806.07643v1
The classical face decomposition and vertex-sensitive diameter framework are
used, not claimed newly invented here.

Katharina Jochemko and Mohan Ravichandran, Generalized permutahedra: Minkowski
linear functionals and Ehrhart positivity, Mathematika 68 (2022), 217--236,
DOI 10.1112/mtk.12122, especially the recalled Shephard criterion in Theorem2.2.
https://londmathsoc.onlinelibrary.wiley.com/doi/10.1112/mtk.12122
The present original-H elimination is an exact certificate implementation of
classical convex duality/summand ideas, with explicit scope rather than a priority
claim for all equivalent characterizations.
