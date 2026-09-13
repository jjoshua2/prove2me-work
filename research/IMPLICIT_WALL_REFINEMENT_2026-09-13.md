# Route through a coarse normal fan; charge the added walls, not the thin cones

## 0. Provenance and the change of direction

This add-only continuation is based on PR #210 at
`42b16e946361ed311b4538ff4c2eb75e245b74d8`. That head includes the independently
prepared complete fork-corridor recognizer. No earlier graph recognizer,
return-block package, solver, proof or publication packet is changed here.

The preceding work distinguishes harmless near-singular bases from genuinely
narrow positive normal cones. Both still leave a limitation: a theorem requiring
every cone of the FINAL polytope to be wide cannot certify a family with an
arbitrarily thin actual vertex cone. This continuation stops imposing that
requirement. It routes through a COARSER normal fan with known short routes,
and charges a separate finite set of additional comparison hyperplanes.

The main constructive theorem needs only a supplied ordinary-edge route of
an implicit H-polytope P and a finite representation of an added Minkowski
summand Q. With L parent edges and q distinct pair-difference directions in
that ADDED representation, it constructs at most

    L+(L+1)q = (q+1)L+q

ordinary edges of P+Q. No list of all vertices or directions of P is needed.
For a tau-wide coarse fan, a separate five-segment argument gives the stronger
existential estimate B+5q, where B is the classical wide-fan diameter expression.
This additive claim uses the published three-segment construction, not just an
abstract parent diameter bound.

A concrete family simultaneously has exponentially many genuine edge directions
and arbitrarily thin vertex normal cones after EVERY affine preconditioner,
but still has the uniform all-endpoint bound (q+1)d+q. Exact returned routes
through dimension32 require only18 added directions, not the more than536 million
directions provably present in the final polytope.

These bounds are derived using standard support-face and normal-fan principles.
Minkowski diameter lifting is a classical subject; see Deza--Pournin below.
No claim is made that all underlying normal-fan facts or the basic lifting
principle are new, or that the resulting constants are best. The contribution
is the explicit direction-sensitive certificate, its implicit-base implementation,
the additive refinement argument, and the simultaneous thin-cone/many-direction
stress family. Polynomial Hirsch is not proved for arbitrary carriers.

## 1. Input, endpoints, and support evidence

Let P={x:Ax<=b} be a polytope, and let

    Q = sum_s conv(V_s)

for finite nonempty rational point lists V_s. Constant summands and redundant
listed points are permitted. Define D to be the set of distinct UNORIENTED
nonzero lines span(v-w), for points in the SAME V_s. Let q=|D|. Parallel classes
are counted once. D can overcount true edges of Q; that is safe. There is no
need to construct Q's full graph. In particular Q can have exponentially many
vertices even if it is supplied as a modest number of segments.

The fine endpoints are specified by rational functionals c_start,c_end that
uniquely expose a parent vertex and a point in each V_s. Their sums are vertices
of P+Q. Every vertex of the sum admits such an exposing functional: its exposed
face is the sum of the exposed summand faces, so a singleton forces every one
of those faces to be a singleton.

The input includes a SIMPLE parent graph route p_0,...,p_L between the projected
parent endpoints. An arbitrary existing route can first be loop-erased without
increasing its length. The implementation checks each listed point against all
original inequalities and verifies full active rank. Each consecutive pair has
shared active rank d-1 and actual endpoint blockers. These facts identify its
entire parent face as a segment, rather than merely a direction of possible motion.

Endpoint objectives come with nonnegative multipliers on original rows that
are tight at the endpoint. Their positive support has rank d, certifying that
the exposed parent face is that vertex. No optimization oracle, unverified graph
adjacency, or supplied numerical diameter bound is used by the verifier.
The code also accepts some lower-dimensional and unbounded H-inputs when the
same vertex/segment certificates hold; the all-endpoint diameter statements
here are stated for polytopes, and the wide-fan corollary uses intrinsic dimension.

## 2. Construct a piecewise-linear objective itinerary

For every parent edge [p_(i-1),p_i], choose a positive combination c_i of ALL
original rows tight at both endpoints. Let c_0 and c_(L+1) expose the requested
fine endpoints. The objective itinerary joins these L+2 vectors consecutively.

A basic support identity is indispensable. If f<=alpha and g<=beta on a set,
and 0<t<1, then attaining the maximum (1-t)alpha+t beta of (1-t)f+t g forces
BOTH maxima to be attained. This follows because the two weighted deficits are
nonnegative. Therefore its support face is the intersection of the two support
faces whenever that intersection is nonempty.

On the open objective segment (c_j,c_(j+1)), the parent support face is exactly
{p_j}: at an interior vertex, the two distinct incident edges meet only there;
at the endpoints, a singleton intersects the adjacent edge. Thus the parent
vertex remains fixed on each of the L+1 open objective segments.

Choose the normals generically relative to D. At a parent-edge corner c_i,
no added comparison can vanish unless its direction is parallel to that parent
edge. Inside each objective segment, comparison events for distinct directions
are required to occur at different parameters. Original endpoint objectives
can be perturbed inside their exposing cones without changing the fine endpoints.

### Exact finite genericity, not a floating perturbation

Weights on a face's supporting rows are varied by positive powers z,z^2,... of
a rational parameter. For corners use 1+z^j; for endpoints add z^j to the supplied
multipliers. A finite positive bound on z preserves all initially strict added
point comparisons at an endpoint.

Every prohibited wall equality is a nonzero polynomial in z, except the allowed
parallel comparison at a parent-edge corner. A coincidence of two interior wall
crossings, with neighboring objective a fixed, is the linear condition

    c . ((a.g_2)g_1-(a.g_1)g_2) = 0.

It cannot vanish identically on the edge-normal span unless the bracket is
parallel to the parent edge. But the bracket is orthogonal to a, while a strictly
exposes one endpoint relative to that edge, so this is impossible for a nonzero
bracket. Distinct nonparallel lines and the neighboring normal's genericity
exclude the zero bracket. The same argument applies at the final corner with
both neighbors prescribed. On a vertex's full-rank active span it is simpler.

Each nonzero polynomial has degree at most the number of supporting rows. The
code tries more distinct rational z values than the sum of these degree bounds.
This proves finite termination. All denominators, objective coordinates, event
times and vertex coordinates are exact rational numbers. The number of arithmetic
operations and their bit sizes are polynomial in the EXPLICIT route, H-data and
added point lists. Finding a short parent route is a separate problem.

## 3. Every retained event is a whole exposed segment

On an open objective segment, only added summand maximizers can change. Each
added direction defines one hyperplane, and a linear objective segment crosses
that hyperplane at most once. There are at most q such crossings per segment.
At a separated event, every tied maximizing summand face is a point or a segment
parallel to the single crossing direction. The parent face is a point.

At a parent-edge corner, the parent exposed face is precisely its edge. All
nontrivial added exposed faces are parallel to that edge by genericity. Hence
the Minkowski sum of these exposed faces is again a segment, possibly longer
than the original parent edge.

For rigor, support values add under Minkowski addition. Equality in their sum
forces equality in each term. The complete exposed face is therefore the sum
of the summands' exposed faces, not just a set containing the proposed endpoints.
The sum of parallel intervals is exactly an interval. All changing summands
move in the same orientation: their difference has positive product with the
change between the objectives on the two sides. Thus nontrivial changes cannot
cancel. Every retained event is an ORDINARY edge of P+Q.

There are exactly L retained parent-edge events and at most (L+1)q additional
comparison events. Inactive comparisons may be discarded. This proves

    dist_(P+Q)(u,v) <= (q+1)L+q,                              (1)
    diam(P+Q) <= (q+1)diam(P)+q.                             (2)

The case p_0=p_L is important: fine endpoints may be different even though their
parent endpoint is the same. One within-cone segment gives at most q edges.
Parallel added directions may expand a parent edge, but cost only that one edge.
A one-dimensional interval case is checked directly.

The lift is not asserted shortest, monotone in a fixed primal objective, or
contained in the fine endpoints' smallest common face. The small tests retain
35 examples where the constructed lift is longer than the independently computed
fine graph distance. To use the theorem inside a carrier, provide a model of
THAT carrier; do not assume an ambient lift stays in it.

## 4. A stronger additive theorem from a wide COARSE normal fan

Suppose P is full dimensional with tau-wide vertex normal cones. Put

    B(d,tau) = (8d/tau)(1+ln(1/tau)).

Dadush--Haehnle's proof of Theorem11 constructs a three-segment objective walk
between suitably deep centers of two chosen parent cones, with at most B expected
parent-fan crossings. Consequently a realization with that bound exists. The
number THREE matters; the theorem here does not follow merely by substituting
a parent graph-diameter bound into an unspecified objective itinerary.

The requested fine endpoints need not be exposed by the deep centers. Connect
the fine source objective to the chosen source center inside its parent cone,
and connect the target center to the fine target objective similarly. These
two segments cross no parent-fan boundary. Together with the three published
segments there are five. Each of the q added hyperplanes is crossed at most
once on each segment, so

    diam(P+Q) <= B(d,tau)+5q.                                (3)

Generic perturbation avoids simultaneous independent events. Formally use a
slightly smaller tau to allow the deep centers to be chosen generically, apply
the integer crossing bound, and let that smaller value approach tau. The final
integer route length is at most floor(B)+5q. If the projected parent endpoints
coincide, the direct within-cone q-edge route already suffices.

The proof is more general than a Minkowski representation: it applies to a
POLYTOPAL fan refining a tau-wide coarse fan when its added codimension-one
walls lie in a certified union of q hyperplanes. No width assumption is made
on the fine cones, and no lower separation between added hyperplanes is needed.
The implementation supplies the Minkowski refinement automatically, not an
arbitrary fan-coarsening recognizer.

The exact deterministic constructor in this packet implements (1), NOT the
random three-segment coarse walk used for (3). A certificate of a few-segment
coarse objective walk could be combined with the same event verifier, but this
packet does not claim to implement the cited expected-length distribution or
an end-to-end optimizer for arbitrary implicit P.

## 5. Simultaneously many directions and genuinely thin feasible cones

Let d>=4 and p=d-2. Define the parent by 2d inequalities:

    0<=x_0<=1,
    0<=x_i<=1+x_0 for 1<=i<p,
    0<=x_p,x_(p+1)<=1.

This is a star-shaped variable-interval model times a square. Its vertices have
one lower/upper choice per coordinate. Every choice pattern exists; changing
one choice holds d-1 independent defining equalities fixed and gives an ordinary
edge. Hence any two parent vertices have a route of at most d edges, obtained
by changing their differing choices once. This is a proved route construction,
not an input assumption about an unknown graph.

Add q>=2 segments. Two have generators

    g=(0,...,0,1,1),   h=(0,...,0,1,1+epsilon), epsilon>0.

The other q-2 generators can be dense, subject to nonzero products with the two
exposing objectives described next. They genuinely mix the coordinate blocks;
no affine-indecomposability claim is inferred from dense coefficients alone.

### Exponentially many true directions persist

An objective zero on the p star coordinates and equal to (1,2) on the square
exposes a translate of the entire p-dimensional star polytope: the square and
all added segments contribute unique points. The star has directions e_i for
its leaves and (1,1_S) for each subset S of p-1 leaves, arising from

    (0,1_S) -> (1,2*1_S).

All are ordinary edges, and the lines are pairwise distinct. Thus the FINAL
polytope has at least

    2^(d-3)+d-3

true edge directions. The method never enumerates this dictionary.

### Some actual cone remains thin under EVERY affine preconditioner

An objective negative on every star coordinate and zero on the square exposes
a translate of the two-dimensional zonogon generated by

    e_1, e_2, e_1+e_2, e_1+(1+epsilon)e_2.

All other added segments contribute unique points. This is an actual exposed
eight-vertex face, not an artificial basis containing infeasible row choices.

After any invertible affine transformation, the induced linear map on this
face's tangent plane is invertible. Write the first two transformed directions
as u,v; the other two remain u+v and u+(1+epsilon)v. For the sine s of the angle
between unoriented lines, determinant cancellation gives

    s(u+v,u+(1+epsilon)v)*s(u,v)
      = epsilon*s(u,u+v)*s(v,u+(1+epsilon)v) <= epsilon.

Some pair of direction lines has sine at most sqrt(epsilon). Consecutive lines
in their cyclic order have a gap no larger than that pair's smaller gap. The
zonogon's normal fan is the arrangement of their four perpendicular lines,
so an actual vertex cone of this face has width at most sqrt(epsilon) (a safe,
not sharp, estimate).

A vertex of this exposed face is also a vertex of the full polytope. Projecting
an ambient normal-cone ball orthogonally to the face's tangent space gives a
same-radius ball in the intrinsic face cone. Its center norm cannot increase;
if the projection were zero with positive radius it would contradict pointedness
of the face cone. Thus ambient width at that vertex cannot exceed intrinsic
width. After EVERY affine preconditioner the final polytope therefore has some
vertex normal cone of width at most sqrt(epsilon).

This is a true positive-cone-width obstruction, not merely a poor inverse bound.
The lower bound on its number of edge directions and this all-preconditioner
thin-cone statement coexist with the constructive bound

    diam(final polytope) <= (q+1)d+q,                        (4)

independent of epsilon. It is a limitation of width/direction-based proof inputs,
not an example of large diameter.

### Executed high-dimensional instances

The tests choose dense added generators with exact nonzero exposing products,
construct parent all-lower/all-upper endpoints, and generate their actual lifts.

| Dimension | Parent H-rows | Added directions | Verified edges | Bound (4) |
|---|---:|---:|---:|---:|
|12|24|6|19|90|
|24|48|12|51|324|
|32|64|18|66|626|

At d32, epsilon=2^-160, the final polytope has at least536,870,941 edge directions
and minimum normal-cone width at most2^-80 after every affine preconditioner.
Only18 ADDED directions are used in the lift. No complete refined vertex graph
or refined H-description was constructed. The count64 belongs to the PARENT
inequalities, not a falsely claimed facet count for the Minkowski sum.
All refined endpoints and steps are certified through the original parent
inequalities and every listed summand point. The displayed lengths are not
claimed shortest. The eight-vertex exposed planar face is independently enumerated.

## 6. Connection to the actual selected-carrier accounting

When the same actual selected carriers have coarse-wide models with parent
three-segment cost at most K*h_i^3 and q_i additional hyperplanes, (3) gives
local cost at most K*h_i^3+5q_i. Using the verified aggregate sum h_i<=3e and
h_i<=H, the original deferred certificate assembles

    D + 3K H^2 e + 5 sum_i q_i.                             (5)

Added walls are charged per selected carrier occurrence. They are not silently
deduplicated across unrelated subcalls. The new Lean arithmetic/route adapter
keeps actual local routes and their budgets explicit. It neither formalizes the
external analytic theorem nor asserts a small coarse refinement for every carrier.

Alternatively, without a wide parent fan, (1) lifts any independently certified
short parent route: network, cyclic, hidden product, feedback, or another direct
solver. Such composition preserves the graph cost and does not require exposing
or listing all parent edge directions. This is the implemented constructive mode.

## 7. Executed evidence, limitations, and formalization

The final suite checks297 exact route certificates and666 ordinary-edge
occurrences. Eight independent small comparisons recover37 base vertices and46
base edges, then61 refined vertices and80 refined edges by complete point-sum
and supporting-hyperplane enumeration. They recompute521 ordered fine graph
distances and test every unordered pair including stationary endpoints. Of291
small lifts,87 have a stationary parent projection, thirteen base-edge events
expand parallel summand segments, and35 lifts are deliberately recorded as
longer than the actual shortest fine route.

Three high-dimensional no-graph-enumeration lifts add136 checked edges. Three
boundary tests include a one-dimensional interval, an implicit-equality line
parent, and no added summands. Twenty forged/malformed cases are rejected:
wrong endpoint support, false normals/multipliers, omitted events, missing
corners, changed summands, nonvertex/infeasible parent points, parent diagonals
and refined diagonals offered as ordinary edges. There are120 rational affine
cross-ratio checks and651 budget algebra cases. The all-affine/all-dimension
claims rest on the proofs, not these finite samples.

Two new Lean candidates contain225 lines and ten axiom printouts. They prove
positive support-face intersections, affine wall-root uniqueness, finite event
counts, and actual selected-route budget composition. They are UNCOMPILED.
The full exact normal-selection algorithm, fine-fan realization argument and
analytic three-segment theorem are not all complete Lean declarations merely
because these cores exist. All earlier repository sources remain unchanged.

The outstanding general premise is a short exact COARSE description or a small
added-wall refinement of a carrier. An arbitrary H-polytope has not been shown
to admit one. Passing an already-short route to the lifter is not solving that
route problem from scratch. This work supplies a compositional method that
survives thin cones and huge full direction sets; it does not turn those
requirements into an unconditional Polynomial Hirsch theorem.

## Primary references and attribution

Daniel Dadush and Nicolai Haehnle, On the Shadow Simplex Method for Curved
Polyhedra, arXiv:1412.6705, Theorems10/11 and the explicit three-segment proof:
https://arxiv.org/html/1412.6705 . That construction is the external ingredient
in (3); the implementation and arithmetic cores do not import it as a Lean axiom.

Antoine Deza and Lionel Pournin, Diameter, decomposability, and Minkowski sums
of polytopes, Canadian Mathematical Bulletin62 (2019),741--755,
arXiv:1806.07643, DOI10.4153/S0008439518000668:
https://arxiv.org/abs/1806.07643 . It gives classical projection/fiber diameter
bounds involving a summand's vertex count. The present q-based lift replaces
that potentially enormous finite fiber enumeration by added-wall sweeps. No
claim of priority for every possible version of such a normal-fan lift is made.
