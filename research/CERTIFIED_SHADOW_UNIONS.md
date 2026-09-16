# Finite-bit original-H shadows and certified path-local unions

## Status and scope

Research continuation from main `5e811793529ebacce9731c39cfe3d1b9d082e7c2`.
This is written mathematics and exact rational software, NOT Lean compilation,
axiom auditing or Prove2Me acceptance. No existing proof, selector, dependency,
workflow, toolchain pin or secret is changed.

The current #267 result precludes universally polynomial-sized COMPLETE forward
stellar flagifications. Here no flagification or complete incompatibility list
is computed. The input consists of rational original inequalities A x <= b and
two original vertices u,v. The constructor finds a genuine original-edge shadow
path inside their common face. It permits nonsimple vertices, redundant rows,
and bounded lower-dimensional presentations. It then optionally switches between
several such paths by finding a shortest path in their DISCOVERED edge union.

The classical ideas are parametric/shadow linear programming and dichotomic
weighted-sum envelope enumeration. The contribution is their concrete certified
original-row implementation, a deterministic cofactor-based finite-bit genericity
construction, explicit handling of nonvertex LP optima, and a separately audited
union-path interface. No historical novelty claim for all equivalent algorithms
or perturbations is made.

**Literature guard.** Alexander E. Black, arXiv:2403.04886v2, Theorem 1.2, gives
simple d-dimensional polytopes with 4d facets and two vertices for which EVERY
coherent path between them has at least 2^d edges. Thus even choosing endpoint
objectives freely cannot guarantee one universally short shadow. This is a
stronger warning than failure of a particular pivot rule. It does not disprove
Polynomial Hirsch. The present complete-shadow primitive cannot overcome it
by itself; splicing paths is permitted, but no universal small union or discovery
cost is proved either. The paper's lower-bound family is NOT reconstructed or
experimentally replayed here. The tests below are separate controls.

Other agents own bounded-length SMT search, Fano/nestohedral direct transfers,
and private-marker graphical refinements, as recorded on #267. None is duplicated
here. The earlier interrupted Fano energy investigation is left to its claimant.

## 1. Original vertices, common faces and deterministic genericity

Let P={x:A x<=b} be nonempty and bounded in R^d, d>=1, with vertices u,v.
All coefficients are rational. At each original vertex choose d independent
tight ORIGINAL rows, denoted B_u and B_v. Such a basis exists even at nonsimple
vertices and when P is lower-dimensional: otherwise the common active kernel
would give a locally feasible line through the alleged vertex. The implementation
stores rational right-inverse identities to verify these rank assertions.

Let J be all original rows tight at both u and v. The working face is obtained
by adding the reverse inequalities -A_j x<=-b_j for j in J. It is the intersection
of the common supporting faces, hence the smallest face containing both endpoints.
An edge of it is an edge of P. Alternatively the output verifier establishes
each edge directly with ORIGINAL common-row rank and endpoint blockers, independent
of this face theorem. Boundedness of P is certified by both signed coordinate
objectives using original-row primal/dual certificates. There is no supplied
strict-interior point, simple-polytope assumption or image-edge projection.

### Cofactor bounds without enumerating edge directions

Multiply each original row AND its right side by a positive rational scale to
obtain a primitive integer row, without reversing its orientation. Let H>=1
bound the absolute coefficients of all resulting normal vectors. A direction
of any original edge is parallel to a nonzero integer cofactor vector g from
d-1 independent common tight rows. The determinant expansion gives

    |g_j| <= G=(d-1)! H^(d-1).                              (1)

This also covers lower-dimensional P: its affine-hull equalities contribute
to the d-1 tight-row rank. For d=1 the cofactor of the empty matrix is one.
The constructor does NOT enumerate these row subsets or edge directions.

Write the integer endpoint basis rows in chosen orders as U_i,V_j,
i,j=0,...,d-1. Put

    C=2(d H G)^2,        R=2C+2,
    f=sum_i R^(d-1-i) U_i,
    h=sum_j R^(d(d-1-j)) V_j.                              (2)

All coefficients in these sums are positive, so f uniquely exposes u and h
uniquely exposes v in P: equality in their upper bounds forces the full tight
basis, whose intersection is the specified vertex. Those objectives remain
valid on the working face.

For a nonzero cofactor direction g, f(g) and h(g) are nonzero integer-polynomial
evaluations. At least one coefficient is nonzero by basis invertibility; every
coefficient has absolute value at most dHG<=C. An integer polynomial with
coefficient bound C cannot vanish at R, since its leading term has magnitude
at least R^s and the lower terms have sum at most C(R^s-1)/(R-1)<R^s.

For two NONPARALLEL cofactor directions g,k, consider

    f(g)h(k)-f(k)h(g).

Its coefficient from (i,j) is U_i(g)V_j(k)-U_i(k)V_j(g), of absolute value
at most C. Its exponent d^2-1-i-dj is distinct for every ordered pair (i,j),
so no coefficients are silently combined. At least one coefficient is nonzero:
otherwise, choosing j with V_j(g)!=0 would imply U_i(k)=lambda U_i(g) for
every i, forcing k=lambda g by invertibility of U. The same leading-term
argument proves that this determinant is NONZERO. Therefore

    c(t)=(1-t)f+t h

cannot annihilate two independent original edge directions at any real t.
Any exposed face of dimension at least two contains two such independent edge
directions. Every exposed working face along 0<=t<=1 is consequently either
an original vertex or an original edge. Endpoints are uniquely exposed.
Parallel but distinct edges cannot occur in a higher-dimensional common exposed
face without producing a second independent direction.

This is quantitative genericity from original rows, not an oracle, a randomized
success assertion, or a finite sample of directions. It is deliberately
conservative: endpoint objective bit lengths are
O(d^3(log H+log d)). Clearing the input row denominators changes log H by at
most a polynomial in rational input size. The huge integer VALUES are not a
polynomial-magnitude claim or an assertion of good numerical conditioning.
The reverse common-face rows have the same coefficient bound.

## 2. Output-sensitive support queries construct the whole shadow

Every vertex x defines the affine score f(x)+t(h-f)(x). The desired path is the
upper envelope as t runs from zero to one. At a query with known supported
vertices x,y whose slopes are increasing, their scores intersect at

    t = f(x-y)/(h-f)(y-x).                                  (3)

The active interval contains this t in (0,1). Query max c(t)(z) over the exact
working H-face, using positive primitive scaling of c(t) to control arithmetic.
If the optimum equals the common value at x,y, they lie on one exposed face.
By Section 1 it is an edge, and the original-rank certificate confirms it.
If the optimum is larger, choose an ORIGINAL vertex z attaining it. Its slope
lies strictly between those of x,y. Recurse on x,z and z,y.

Why is that finite? Original supported vertices are finite, a split strictly
separates the slope range, and each inserted vertex is on the true envelope.
The usual dichotomic argument therefore enumerates every envelope transition.
The implemented stack avoids Python recursion limits. Once its leaves are
ordered, consecutive support inequalities also certify whole-interval maxima:
a shared vertex maximizes at both neighboring wall objectives and hence at
every convex interpolation between them. The endpoint intervals use f and h.
Nonparallel simultaneous ties have already been excluded, and each direction
can occur at only one t. The final path is simple and h-increasing.

If the completed path has L>=1 edges, the binary recursion has L leaves and
L-1 split nodes. There are exactly **2L-1 PRIMARY support queries**. This is
not the count of internal tableau pivots, and L is not uniformly polynomial.

### A real LP-output hazard and its counted remedy

The reused exact LP solver shifts a feasible seed and splits free variables.
A basic feasible point in THAT lifted tableau may project to an interior
point of an original exposed edge. Thus its optimum must not be assumed to
be an original vertex. For instance, maximizing y on

    x-y<=0, -x-y<=0, y<=1

from seed (0,0) returns (0,1), interior to the top edge. We check active rank.
When needed at an internal split, add the exact support equality c(t)(x)=M
and maximize h on that face. Section 1 makes h nonconstant on every edge,
so this SECONDARY solve returns a unique original vertex. We check its rank
again against original rows, not the added support equality.

This is at most one extra solve per split. Therefore total support calls are
at most 3L-2, plus the separately counted 2d original boundedness calls. The
initial coordination comment's 2L-1 should be read as primary queries only;
secondary tie resolution is not a free oracle. The actual sheared-hexagon
regression triggers this branch: a primary optimum (-2,1) lies inside the
edge from (-3,1) to (-1,1), and the secondary solve produces (-1,1). Its
three-edge route uses five primary and one secondary support calls.

Exact Bland simplex is reused UNCHANGED. Its pivot cap and the shadow-query
cap are explicit failures, not completed negative route certificates. No
polynomial pivot count, runtime, or full-graph shortestness is asserted.

## 3. The returned path is independently tied to ORIGINAL inequalities

Each path vertex has a feasible coordinate vector, d tight original rows and
a rational right inverse. Each leaf edge has d-1 shared original tight rows
and a rectangular right inverse A_I R=I. This proves their rank without doing
rank search in the verifier. Distinct feasible endpoints make the resulting
face exactly one-dimensional. Original start and end blockers bound the line
in the two opposite directions, proving the entire maximal edge, not a chord
or a partial ray step.

Every support solve includes a feasible point and nonnegative original-working-
row multipliers representing the same objective and value. The verifier checks
these identities, the exact query tree, increasing wall times, intermediate
slopes, secondary equality restrictions, endpoint objectives and all original
common rows. No LP, inverse discovery, rank elimination, vertex enumeration or
route BFS occurs in single-shadow verification. This does not make the Python
program or its JSON parser Lean-verified.

The affine genericity theorem provides termination and completeness of the
producer. Soundness of the DELIVERED original route is additionally secured
by the original-row certificates even if one does not trust that discovery
argument. Whole-envelope claims also have explicit support and ordering checks.

The supported class is broader than simple full-dimensional polytopes. Tests
include nonsimple crosspolytopes and pyramid apices, embedded lower-dimensional
squares, duplicate/redundant/zero rows, an interval and a single point. More
than d tight rows can reflect redundancy or lower dimension; that diagnostic
is not mislabelled as a count of nonsimple vertices.

## 4. Switch between paths instead of choosing only the best full shadow

For a finite collection of endpoint-basis orderings, construct and verify one
shadow for each. Form an undirected graph from ONLY the vertices and edges
actually returned by these paths. Find its shortest u-v route. It can take a
prefix from one shadow and a suffix from another, using all edges in their
original geometric sense; it is not required to remain monotone for a common
objective. No extension graph, complete polytope graph or original-neighbor
oracle is supplied.

The union verifier audits every constituent, reconstructs their finite edge
union, and checks the selected path uses only those edges. It also checks an
integer label D on every union vertex with D(u)=0, D(v)=L_selected and
|D(x)-D(y)|<=1 on every union edge. Telescoping shows that ANY union route has
length at least L_selected. This is an exact shortest-IN-THE-DISCOVERED-UNION
certificate requiring no BFS in the verifier. It does not establish global
shortestness without a separate original-polytope lower bound.

If candidate lengths are L_i, support work is bounded by sum_i(3L_i-2) for
nonstationary candidates, plus repeated boundedness checks. Union size is at
most the sum of their output sizes. A short SELECTED route does not retroactively
make long constituent discovery cheap. We do not assert a universal polynomial
number of candidates, polynomial candidate lengths, or a small sufficient union.
In particular, fully computing each candidate remains subject to Black's
all-shadow obstruction. A truly general successor would need control of only
useful prefixes, restarts, or another original-edge source, with a new proof.

## 5. Executed positive and adverse controls

The cyclic-polar inputs are the SAME moment family used as a direct-route
control in #267, not a newly discovered small-diameter class. Let d=2k,
n=4k+1, v(t)=(t,...,t^d), and center at the mean. We use positively scaled
integer inequalities

    [n*v(t)-sum_s v(s)] . x <= n.

Endpoints have active blocks {1,...,d} and {d+1,...,2d}. Consecutive blocks
shift by one label and give the known d-edge route: a product of consecutive
paired-root factors is nonnegative on all sampled moment parameters, and
Vandermonde independence proves the exposing facets and simplicity. Disjoint
endpoint facet sets force at least d ordinary exchanges, so this reference
route is shortest. Its coordinates, feasibility, active rank and every maximal
original edge are computed and audited separately here, not supplied to the
shadow constructor.

We tried rotations of the ordered source tight basis. The reported two-candidate
schedule is (k-1,0),(k+1,0), where the second coordinate rotates the target basis.
It was chosen after exploration in d6, not pre-registered and not proved optimal.
The exploratory run tried all36 rotations there; those search costs are not
included in the final two-candidate query count. The schedule is then replayed
at all three sizes, retaining its d8 failure to attain shortestness.

| Original d,m | Default single shadow | Two sampled shadows | Shortest union | True distance |
|---|---:|---:|---:|---:|
|4,9|6|5 and5|4|4|
|6,13|12|8 and8|6|6|
|8,17|20|13 and13|10|8|

The d6 union contains13 vertices and14 original edges;30 primary support calls
build its two candidates. Its selected six-edge route is shorter than BOTH
sampled shadows and is globally shortest by the separate original-facet bound.
This does NOT prove that no other single shadow has six edges. The d8 union
has21 vertices/23 edges and50 primary calls; it remains two steps too long.
Only the d4 family receives independent full active-system graph enumeration
(126 systems,27 vertices,54 edges). The d6/d8 comparisons use the proved cyclic
family and the independently audited d-edge path, not a full graph.

The generic suite independently reconstructs11 small original graphs:
70 vertices,132 edges and2169 square active systems. It constructs249 endpoint
routes with298 edges versus285 BFS edges, with11 nonshortest routes. There
are408 primary support queries and ONE actual secondary query. Reference
checks include3514 whole-support/interval comparisons and13700 nonparallel
edge-direction determinant tests. Additional cofactor tests check54 bounded
vectors and42 pair determinants, and9664 finite integer-polynomial controls.
Eighteen malformed/forged/capped cases are rejected. The original-route auditor
passes with LP, inverse and rank discovery disabled.

Four additional opposite-box cases d6/8/10/12 give6/8/10/12 shortest routes
without graph enumeration, by the independent coordinate-change lower bound.
The d12 objectives have up to7877 bits; the d8 cyclic objectives up to30337
bits. These demonstrate the concrete conservative arithmetic cost, not a
practical floating-point recommendation. A d10 cyclic exploratory attempt did
not complete within the tool-call budget, so no completed d10 cyclic result
is reported.

Eight additional small union instances, including nonsimple and embedded cases,
use18 original edges, all matching independently computed full-graph distances.
The union auditor passes with LP, inverse, rank discovery AND BFS disabled;
nine forged union/potential cases are rejected. These counts do not make the
experimental schedule a universal benchmark winner or a theorem about arbitrary
numbers of shadows.

## 6. Reproduction and exact boundaries

    python3 scripts/test_certified_rational_shadow.py
    python3 scripts/test_certified_shadow_union.py

The first supports --stage small, auxiliary, large, assemble. A source-hash
check rejects stale stage receipts. Production commands:

    python3 scripts/certified_rational_shadow.py input.json --output shadow.json
    python3 scripts/certified_shadow_union.py input_with_basis_rotations.json --output union.json

Both --certificate options consume the inner certificate or the saved wrapper.
The union input adds a finite list `basis_rotations`, not a graph or decomposition.
Only exact rational numbers/strings are accepted. The command-line tools raise
Python's integer-string conversion guard to250000 digits; data exceeding it
still fails rather than being rounded. The digit limit is a resource guard,
not a mathematical bit-complexity claim. Library callers using unusually large
certificates may need the same explicit guard setting.

Four new scripts import just one unchanged production dependency,
`scripts/exact_farkas_lp.py`, Git blob ea511a79164d953792942d8be3dd3537646738d6.
SymPy is solely an independent small-graph/minor test dependency. The original
full reports and six generated fixtures regenerate and are bundled; compact
committed summaries are labeled derived. Clean replay and exact file identities
are recorded separately. No new Lean skeleton, accepted theorem change, Actions
gate, Prove2Me registration, or platform status claim is included.

The conjecture-level goal remains a uniform polynomial original-edge bound.
This interface eliminates a supplied generic-position or edge-direction oracle
and permits certified path-local recombination. It does NOT remove either the
published coherent-path obstruction or the need to control total useful search
and route cost. A complete flagification is no longer a premise; a universally
short coherent path must not replace it as another false premise.

## Primary references

Alexander E. Black, *Exponential Lower Bounds for Many Pivot Rules for the
Simplex Method*, arXiv:2403.04886v2 (2024), especially Theorem1.2 and the normal-
fan/parametric interpretation in Section2. Primary HTML actually consulted:
https://arxiv.org/html/2403.04886v2 .

Anthony Przybylski, Kathrin Klamroth and Renaud Lacour, *A simple and efficient
dichotomic search algorithm for multi-objective mixed integer linear programs*,
arXiv:1911.08937. The primary abstract supplies context for weighted-sum
output-sensitive enumeration; the binary query count here is proved directly.
https://arxiv.org/abs/1911.08937 .

Repository #267 supplies the existing cyclic-family control and the distinction
between global refinement size and local original path length. Its result is
reused and is not republished by this continuation.
