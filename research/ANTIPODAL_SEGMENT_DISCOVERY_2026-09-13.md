# One antipodal walk gives a complete segment-factor catalogue

## 1. Contribution and verification boundary

This is an add-only continuation of PR #210 from
`1dd8d9b79cf31358a1a1052866f03f13a2d64398`. Earlier segment extraction and
wall-lifting sources remain unchanged. The new input is just the ORIGINAL
rational H-system A,b and endpoint vertices. No candidate directions, segment
lengths, zonotope generators, residual model, affine chart, or parent route are
supplied.

The principal theorem is general for a nonempty compact polytope: ANY ordinary
edge walk between two uniquely opposite-exposed vertices contains every
nonzero segment-summand direction. Thus a finite original-H walk is a certificate
that a list of directions is COMPLETE, not merely a heuristic sample. The old
exact capacity tester can filter that list and extract a canonical maximal
zonotope summand. Its residual has no nonzero segment summand in ANY direction.

The theorem does not bound the length or computational cost of finding the
antipodal walk by a universal polynomial. The exact implementation uses capped
lexicographic simplex and can take many pivots. Its successful certificate is
complete; a cap is a failed search, never a certificate of missing factors.
Finding such a diagnostic path is not used as an assumed short-route premise in
an unconditional Polynomial Hirsch proof.

The general catalogue need not leave an easy residual. The integrated route
constructor recognizes point cores, pyramids (including lower-dimensional
cores), and the earlier positive-feedback model. Other residuals are explicitly
unsupported, even when their complete catalogue was successfully computed.

The supporting Minkowski face facts are classical. Deza--Pournin,
*Diameter, decomposability, and Minkowski sums of polytopes*, arXiv:1806.07643v1,
Section 2, Lemmas 2.1 and 2.2, recall unique face decomposition and projection of
adjacency to summands. Section 3 explains the resulting diameter monotonicity.
The antipodal cover and exact original-H implementation here are derived uses
of that framework, not a claim of a new general Minkowski face theorem or
priority for every possible segment-recognition formulation.

One new Lean file contains 174 lines and nine axiom printouts. It is an
UNCOMPILED proof candidate. It proves original-row switching geometry, exposing
coefficient lemmas, finite coverage and distinct-step lower bounds. The complete
polytope-to-binary-allocation construction, all-direction exhaustion, simplex
algorithm and integrated recognition are written/executable arguments, not
silently promoted to end-to-end Lean theorems. No platform acceptance is claimed.

## 2. Every segment factor defines a binary vertex label

Assume R=K+[0,tg], with K a compact convex polytope, t>0 and g nonzero. Every
vertex x of R has a unique decomposition x=k+epsilon*tg, epsilon in {0,1}.
One proof uses a strictly exposing functional: the exposed face of a Minkowski
sum is the sum of its exposed faces; a singleton sum forces both faces to be
singletons. A functional uniquely exposing x cannot be orthogonal to g.

There is also a direct convexity proof. A decomposition with an interior
segment parameter would express x strictly between two different feasible
points. Two decompositions using different segment endpoints would, by taking
the midpoint of their K-components, produce such an interior decomposition.
Hence the bit epsilon(x) is well-defined independently of a chosen exposer.

Let x,y be adjacent vertices whose bits differ. Orient g so x=k and y=l+tg.
Then x+tg and y-tg are feasible in R. For any original row a.z<=b tight at BOTH
x and y, feasibility gives

    a(x+tg)<=b=a(x),     a(y-tg)<=b=a(y).

Since t>0, the first gives a.g<=0 and the second a.g>=0, so a.g=0.
The common tight rows of an ordinary edge have kernel span(y-x). Therefore g
is parallel to y-x. This proof is valid at nonsimple vertices and retains all
original row occurrences; it does not confuse a merely feasible segment with
an edge.

Thus the bit of a segment summand can change along a graph walk ONLY on an edge
parallel to that summand. This is the elementary geometric fact behind the
complete cover, not an assumption that every edge direction is a summand.

## 3. Antipodal exposure forces every factor to appear

Choose c such that c has unique maximizer u and unique minimizer v on R.
For every segment summand [0,tg], c.g is nonzero. Its maximizing and minimizing
segment endpoints are opposite, so epsilon(u) differs from epsilon(v).

On ANY finite ordinary-edge walk u=x_0,...,x_L=v, that binary sequence must
change at some adjacent position. By Section 2 that edge is parallel to g.
Consequently

    every segment-summand line is one of the L walk-edge lines.        (1)

No shortestness or monotonicity is required for this completeness statement.
The implementation constructs a c-decreasing walk, which also implies each true
segment direction occurs exactly once: every bit switch in that direction has
the sign of its c-improvement, so the bit cannot switch back. Nonfactor edge
directions can still repeat. Distinct factor lines require distinct edge steps.

If q is the number of distinct positive-capacity directions, then every walk
between u,v has length at least q, and q<=diam(R). In particular the set of
segment factors is finite, independently of a prior all-edge enumeration.
This supplies a complete candidate list of size at most the measured diagnostic
walk length. It does NOT supply an a priori polynomial bound on that length.

The antipodal requirement cannot be dropped. A single square edge misses the
other square factor. Even listing ALL edges incident to one vertex is insufficient:
a triangle plus [0,(1,-2)] has a vertex with no incident edge in the segment's
direction. The tests independently construct that pentagon and show that the
new two-edge antipodal walk from the same vertex does discover the missing factor.

## 4. Exact construction from A,b and one vertex

The diagnostic source may be the user's requested start. The algorithm verifies
it against every original inequality and requires full active rank. It first
proves boundedness using nonnegative original-row dual combinations that bound
each positive and negative coordinate. These finite identities are checked
without invoking an optimizer.

An independent active row basis B at the source is selected with symbolic
feasibility for right-hand sides b_i+epsilon^(i+1). This uses finite rational
coefficient dictionaries, not a floating perturbation. No reported vertex or
edge belongs only to a perturbed problem.

Pick c as a positive combination of B, with weights 1+z,1+z^2,...,1+z^d.
It uniquely maximizes at the original source. Optimize -c using original-row
basis pivots. A negative objective multiplier selects a leaving row; exact
lexicographic slack ratios select the entering row. Each exchange keeps d-1
independent original rows. A nonstationary original limit is therefore an
ordinary edge, verified again using all original common tight rows and endpoint
blockers. Stationary symbolic pivots do not enter the graph walk.

At termination the dual multipliers for -c are required to be STRICTLY positive
on a full-rank tight basis. This proves that the opposite endpoint is unique,
rather than choosing an arbitrary vertex of a tied minimizing face. A tied
terminal multiplier triggers a new rational z and a fresh walk. For every
independent d-1-row span, lying in that span is a nonzero polynomial condition in
z of degree at most d: the starting B spans the whole space. There are at most
binom(m,d-1) such spans. Thus more than d*binom(m,d-1) distinct rational trials
suffice in principle. Operational caps can be much smaller and report failure.

Boundedness, endpoint strict support and the actual ordinary-edge sequence are
all the verifier needs for (1). It does not repeat the pivot search. The stored
pivot log and trial counts are discovery diagnostics, not geometric proof
assumptions. The verifier reconstructs the list of canonical directions from
ALL nonstationary edges and rejects a missing direction or added unrelated
candidate. It accepts only exact rational numbers.

There is no assertion that the implemented pivot rule is strongly polynomial.
The initial degenerate active-basis search and the full path can be exponential.
No full vertex graph, full edge-direction list or normal-fan enumeration is
performed. These are distinct computational statements.

## 5. A complete maximal zonotope factor, not a partial peeling

Apply the preceding exact fiber-capacity/Farkas tester to each canonical walk
direction, removing its full proved capacity. Zero-capacity tests remain in the
certificate; dropping a candidate would invalidate completeness.

The earlier transverse-capacity theorem implies that removing one segment does
not change capacities in other nonparallel directions. Therefore positive
parameters in this list are exactly the original maximal parameters, independent
of the diagnostic source, objective, or extra zero-capacity walk directions.
With the convention that each direction's first nonzero coordinate equals one,
the output is

    R = K_0 + Z_max,
    Z_max = sum_g [0,mu_g(R)*g].                              (2)

The residual original-row right-hand sides are fixed by these normalized factors.
They are not path-dependent.

If K_0 contained any nonzero segment in a new direction, that direction would
also be a segment direction of R and hence in the complete walk list. If it
contained one in an extracted direction, it would increase that factor beyond
its proved maximum. Both are impossible. Thus K_0 is SEGMENT-FREE in every
direction, not merely exhausted on a guessed list.

Moreover every zonotope summand of R is, up to translation, a Minkowski summand
of Z_max: each of its generator lines appears in the list, and the sum of its
parallel generator lengths cannot exceed the corresponding maximal capacity.
This identifies a greatest zonotope summand, up to the stated translation and
orientation normalization. The residual is uniquely determined with that
normalization.

Segment-free is NOT the same as Minkowski indecomposable. The product of two
triangles has no nonzero segment summand, but is the sum of its two complementary
triangle factors. The tests retain this distinction. An octahedron is a separate
example where complete zero-factor recognition succeeds while the integrated
point/pyramid/feedback router declines the residual.

## 6. Full peeling can reveal a lower-dimensional, easier core

The previous supplied-direction procedure deliberately removed only two thin
planar factors of the star examples, leaving a feedback box. Complete extraction
also removes the ordinary leaf and planar coordinate segments. The residual
need no longer be full dimensional or a feedback box.

The new router therefore checks two particularly simple exact H-certificates
after sequential Farkas-certified redundant-row deletion:

POINT: All retained inequalities are equalities at one point a. Any other
feasible point would generate an unbounded ray from a, since every right-hand
side equals its value at a. Boundedness inherited from R rules this out.

PYRAMID: There is a feasible point a and one retained row j such that every other
retained row is tight at a, while row j is strict there. Boundedness implies
that every ray through a feasible x!=a exits at row j; no other row can become a
new blocker along that ray. Therefore every non-apex vertex is on that base row.
At such a vertex, deleting row j from its active equalities leaves rank d-1:
rank cannot be smaller by adding one row, and cannot be d because a also
satisfies all those equalities. Thus every other vertex is adjacent to a,
including in a lower-dimensional ambient description. The core diameter is at
most two.

Both certificates are discovered by exact linear equations, not supplied by the
user. The earlier positive-feedback recognizer is a fallback. Boundedness and
all original implications are already in the packet. The route-specific core
edges are independently checked again against the actual residual inequalities.

The unchanged Minkowski wall lifter then reconstructs an actual route in R.
For a q-direction factor and a core bound B, it gives (q+1)B+q. Point cores give
q; pyramid cores give 3q+2; feedback cores give (q+1)d+q. All final edges are
independently verified against the original H-description. A certificate and
recognized chart can be reused for different requested endpoint pairs; a new
antipodal discovery is not necessary for every query.

## 7. Distance lower bounds and recognized zonotopes

The decomposition supplies a binary coordinate for each segment factor at ANY
original vertex. A path must use at least one edge for each factor bit differing
between its requested endpoints. Since one edge cannot be parallel to two
distinct factor lines,

    distance(x,y) >= number of differing factor bits.         (3)

If an explicit linear functional annihilates every factor direction but separates
x and y, at least one more edge is required: that step cannot be charged to a
factor-bit change. The verifier checks such a quotient separator exactly.

For a point residual, the whole polytope is a zonotope with now-discovered
positive segment generators. The one-segment objective lift changes exactly the
factor bits that differ, once each. Its length equals (3), so the route is
SHORTEST. This is a certificate-producing H-to-zonotope recognition and shortest-
path procedure, not a new theorem that zonotope graphs have sign-distance
shortest paths. The classical graph/normal-fan fact is implemented with the
original H-data and a complete generator-discovery certificate.

The diagnostic walk can itself already be short, or even coincide with the
requested path. The benefit in that case is NOT a faster first path; it is a
complete reusable factorization, new endpoint routing, and an independent
optimality certificate. This distinction applies to the large examples below.

## 8. Large final-H examples with no candidate directions

Use the preceding final-H star-times-zonogon family. Its star dimension is d-2;
its planar factor has four generators, including two nearly parallel ones.
Only A,b,start,end are passed to the new constructor. The complete list has

    d-3 leaf segments + 4 planar segments = d+1 factors.

The one additional tested walk direction has zero capacity. After removal the
core is a (d-2)-dimensional pyramid over a (d-3)-cube. The first star coordinate
annihilates every segment factor but separates the requested endpoints. All
factor bits are opposite. The lower bound is therefore (d+1)+1=d+2, and the
returned route meets it.

| Dimension | Original genuine facets | Diagnostic edges | Positive factors | Shortest route |
|---|---:|---:|---:|---:|
|12|28|14|13|14|
|24|52|26|25|26|
|32|68|34|33|34|
|8, hidden dense affine chart|20|10|9|10|

The 32D example has 8,589,934,592 vertices and at least 536,870,941 ordinary-edge
directions by the family's separate explicit combinatorics. The diagnostic walk
examines only34 directions, and proves that its33 positive ones are the ENTIRE
segment-factor list. Its two nearly parallel planar generators use epsilon2^-160.
No full graph or global direction enumeration is performed. The 8D case hides
all coordinates behind a dense rational affine transformation and unknown
translation; no transformed candidates or chart are passed either.

The resulting uniform all-endpoint bound from the pyramid lift is 3d+5, not
an assertion that every pair needs d+2 edges. The displayed pairs are certified
shortest using the factor-plus-quotient lower bound. They are not a newly harder
polytope family or an affine-indecomposability claim.

## 9. Executed checks and limits

Nine independently enumerated small original-H graphs have82 vertices,135 edges
and1,566 ordered distances. The suite reconstructs ALL ordinary edge directions
of these small models and independently tests the capacity of every such line.
Across38 separate antipodal discoveries, the positive factor list and maximal
lengths exactly match those complete independent reference tests. Residual H
right-hand sides agree for all tested diagnostic sources/objectives.

Reusing the recovered decompositions gives824 small endpoint-pair route
certificates with2,902 edges. Of those,591 have an independently certified
matching distance lower bound, including every route in the recognized zonotope
and point-core models. The tests retain227 nonshortest lifts; no universal
shortestness claim is made for nonpoint cores. All returned small routes and
lower bounds are compared to separate BFS distances.

Four larger/dense-affine cases and the duplicate/constant-row boundary give
829 total final-route certificates and2,992 ordinary-edge occurrences. All five
additional routes have matching lower bounds. The reference graph enumeration
is confined to the small test harness and is not a discovery dependency.
Twenty forged/malformed/unsupported cases are rejected, including non-antipodal
supports, omitted candidates, incomplete extraction, invalid lower bounds,
nonvertex sources, unbounded inputs, false apexes and diagonals offered as edges.

The complete catalogue is a general finite-success result, not a promise of
polynomial discovery work. The returned route may be long; pivot/genericity/
active-basis caps are explicit. Residual point/pyramid/feedback recognition is
not universal. The next general obstacle is routing a segment-free residual,
or finding a useful nonsegment decomposition, not supplying candidate segment
directions by hand. No general Polynomial Hirsch conclusion is drawn.

## Primary reference

Antoine Deza and Lionel Pournin, *Diameter, decomposability, and Minkowski sums
of polytopes*, Canadian Mathematical Bulletin62 (2019),741--755,
arXiv:1806.07643v1, DOI10.4153/S0008439518000668.
Primary text consulted: https://arxiv.org/html/1806.07643v1 .
Sections2--3 supply the classical unique-face/adjacency projection framework.
The previous repository note `SEGMENT_PEELING_FROM_H_2026-09-13.md` supplies the
exact capacity/Farkas and transverse-capacity arguments reused without edits.
