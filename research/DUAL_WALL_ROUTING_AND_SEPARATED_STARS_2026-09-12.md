# Direct dual-wall routes and an obstruction to universal target-face locking

## Scope and current repository state

Baseline main is `980681f765b7458d69aee61318dfcfcaa9e2f6af`. Merged #206/#209
supply the automatic full-availability clipping certificate and its aggregate
intrinsic dimension bound. Merged #207 supplies the occurrence/debt primitives.
A separate agent is completing publication of #208. This continuation does not
modify those sources, workflows, dependency pins or platform records.

The preceding selective-carrier work suggested acquiring a target facet or
pair by an inexpensive connector inside a proper source-containing face, then
recursing only in the newly fixed face. The cyclic pair-locking construction
really does this. The first result below proves that this first-step pattern
cannot be a universal rule, even if the permitted proper-face dimension is
unrestricted. The second result gives a genuinely different, constructive
solved-carrier method: sweep the exposing objective through a finite wall
arrangement rather than lock primal target facets.

These are not claimed to be new classical diameter theorems for zonotopes or
polymatroids. The direction-count monotone bound is explicitly classical; see
Blanchard--De Loera--Louveaux, *On the Length of Monotone Paths in Polyhedra*,
Theorem 1.3 and Corollary 1.4 (arXiv:2001.09575; journal DOI
10.1137/20M1315646). Its Lemma 2.5 credits Gritzmann--Sturmfels for normal-fan
refinement by an edge-direction zonotope. The work here is an explicit exact
rational constructor, finite exposed-edge verifier, a precise obstruction to
our proposed locking strategy, and integration with the actual selected-carrier
mass bound. No uniform Polynomial Hirsch result is asserted.

The three NEW Lean modules are uncompiled candidates. Their exact scope is
listed below. The mathematical derivations and executed rational tests are
separate evidence, not a Lean or Prove2Me verdict.

## 1. A simple source and target whose facet stars are disjoint

For d>=2 and 0<tau<1, define

    Q(d,tau) = {x in R^d : 0<=x_i<=1,
                              x_j-x_i<=tau for every i!=j}.

Both u=0 and v=1 are simple vertices: precisely their d coordinate lower or
upper inequalities are active. Every difference inequality is strictly slack
there. The set is bounded, full dimensional, and has exactly d(d+1) facets.
Coordinate facets have an open relative interior by setting their other
coordinates strictly between the bounds. For a difference facet x_j-x_i=tau,
choose 0<x_i<1-tau and every other coordinate strictly between x_i and x_j;
all other inequalities are strict. Thus no inequality in this count is merely
an unused or redundant description row.

If x_j=1, every coordinate satisfies x_i>=1-tau>0. Consequently

    {x in Q : x_i=0} intersect {x in Q : x_j=1} = empty

for EVERY source facet i and target facet j, including i=j. Every proper face
containing u lies in some facet containing u. Such a face therefore misses
EVERY target facet. In particular:

> No connector lying in one proper face through u can acquire even one target
> facet, regardless of its length or the allowed dimension of that proper face.

This refutes a particular universal target-locking rule, not all selective
repair certificates. A prefix may use several faces before acquiring a target
facet, or the entire carrier may have a direct certified solver.

The obstruction is not an artifact of globally nonsimple inputs. Allow the
difference bounds to vary independently in a sufficiently small open interval
about tau, still strictly between zero and one. Source and target stay simple,
their facet stars remain disjoint, and all original facets persist. For a
nonsimple vertex, d+1 or more describing equalities must be consistent. Any
dependency involving a difference row imposes a proper affine equation on its
independently variable bound. Dependencies using only coordinate rows cannot
create an extra consistent equality (opposite bounds are distinct). Avoiding
finitely many proper affine hyperplanes therefore gives rational descriptions
of SIMPLE polytopes with the same separation in every dimension. This does
not say the perturbations preserve the zonotope representation or its d+1
route theorem. An exact 3D perturbed example has 12 facets, 20 simple vertices,
and independently computed endpoint distance five.

## 2. The unperturbed obstruction has diameter exactly d+1

There is an explicit Minkowski decomposition

    Q(d,tau) = tau*[0,1]^d + [0,1-tau]*1.             (1)

For the forward inclusion, adding the same diagonal coordinate to a point in
the scaled cube preserves every coordinate difference, and both summands give
the coordinate bounds. Conversely, for x in Q let

    s = max(0, max_i x_i - tau).

Then 0<=s<=1-tau, s<=x_i<=s+tau for every i. Hence x=s*1+tau*y with
y in [0,1]^d. The Lean candidate proves this interval characterization and the
facet separation directly, with the finite nonempty-index condition explicit.

This is a zonotope with d+1 distinct generator directions: the coordinate
axes and the diagonal. Its vertices are

    0, 1,
    tau*1_S and (1-tau)*1+tau*1_S,
        for every nonempty proper subset S of {1,...,d}.

The only impossible sign patterns for exposing these sums are all negative
coordinate signs with a positive diagonal sign, and the reverse pattern. All
other patterns are realized by choosing the magnitudes of the positive and
negative objective coordinates appropriately. This proves the complete count
2^(d+1)-2 without enumerating the graph. Vertex representations are unique:
strict exposure makes every chosen endpoint in each summand mandatory.

Move from 0 by adding coordinate generators until a nonempty proper S is
active, add the diagonal generator, then add the remaining coordinate
generators. Every step is an ordinary edge; alternatively the dual sweep
below supplies its explicit exposing functional. The route has d+1 steps.
Across any edge of a zonotope with pairwise nonparallel generator directions,
exactly one generator sign changes. The antipodal endpoints differ on all
d+1 signs, proving the lower bound d+1. Thus diameter equals d+1.

An even sharper stress test is the two-edge route

    0 -> tau*e_j -> (1-tau)*1+tau*e_j.               (2)

The final point is on target facet x_j=1, yet it shares NO active inequality
with 0. Its smallest common face with 0 is the entire d-dimensional Q.
Consequently a full-dimensional, high-excess carrier can contain an extremely
short connector. Lack of a proper-face connector is not evidence of a long
route. The tests check both edges in (2) by original-row active rank, not by
calling the two segments circuits.

At d=24 the unperturbed polytope has 600 facets and 33,554,430 vertices. The
constructor returns a shortest 25-edge antipodal route and the separate
full-dimensional two-edge connector. The graph is not enumerated. All returned
vertices and edges are checked against the 600 original inequalities. Complete
independent H-basis enumeration verifies the entire vertex lists for d=2,3,4.

## 3. A direct exact route for finite Minkowski sums

Let the INPUT define

    P = sum_s conv(V_s),

where each V_s is a nonempty finite rational point set in R^d. Sets may contain
redundant points; exact duplicates are removed. They need not be simplices,
segments, simple polytopes, full dimensional, or mutually independent.
Constant summands are permitted. The endpoints are specified by rational
objectives c_0,c_1 that uniquely maximize a point in every summand. Their sums
are the requested vertices of P. Any vertex admits generic exposing objectives,
but automatic recovery from an arbitrary H-description is not implemented.

Form the dictionary of unoriented nonzero lines

    D = {span(a-b) : a,b in the SAME V_s, a!=b}.

Parallel pairs, including pairs from different summands, represent ONE wall.
Let q=|D|. Each direction g defines the comparison wall c.g=0 in objective
space. The dictionary may contain nonedge pair differences; that only enlarges
the safe bound. It is computed from all supplied points rather than an alleged
incomplete edge list.

Choose generic c'_0,c'_1 exposing the same endpoints, and sweep

    c(t)=(1-t)c'_0+t*c'_1, 0<=t<=1.

A summand's maximizing point can change only at a dictionary wall. Every wall
is crossed at most once because c(t).g is affine in t. Coinciding walls from
parallel pairs are treated as one event. The perturbation below prevents
simultaneous crossings of distinct, nonparallel walls.

Between consecutive events, every summand has a unique maximizer. Their sum is
an exposed vertex of P. At an event, some summands may have tied maximizing
points, but every tied difference is parallel to that event's direction g.
Their maximizing faces are therefore points or collinear segments. An event
where none of the maximizers change costs no edge and is explicitly discarded.

### Why every retained event is an ordinary edge

For a linear functional f, the support value of a Minkowski sum is the sum of
the support values. If a sum of feasible summand points attains that value,
every summand attains its own support value: all support deficits are
nonnegative, so their sum can vanish only termwise. Therefore

    exposed_face_f(P) = sum_s exposed_face_f(conv(V_s)).      (3)

At the event, write those faces as a_s+[0,eta_s]*g with eta_s>=0, orienting g
consistently. Their Minkowski sum is exactly

    sum_s a_s + [0,sum_s eta_s]*g.                            (4)

If any maximizing summand changes, the total length is positive. Indeed each
change has positive scalar product with c'_1-c'_0, so changes cannot cancel.
Equations (3)--(4) prove that the entire exposed face is exactly the connecting
segment, not merely that the endpoint difference is parallel to a possible
edge direction. It is an ORDINARY EDGE of P.

The resulting route uses each dictionary direction at most once, hence

    route length <= crossed comparison walls <= q.           (5)

It strictly improves the perturbed target objective. Because initially
nonzero comparison signs are preserved, it weakly improves the original target
objective. The verifier checks these inequalities at every retained event.
For genuine segment summands, each separating generator wall must change a
vertex sign, so the route length is exactly the endpoint sign distance and
is shortest. For general summands the route need not be shortest or stay in
the endpoints' smallest common face. Both limitations are tested explicitly.

### Finite rational genericization, with a termination proof

The implementation uses no random tolerance or symbolic infinitesimal. For
an objective c, try

    c(z)=c+(z,z^2,...,z^d),   z=1/(B+r).

Choose integer B strictly larger than four times
max_g ||g||_1/|c.g| over nonzero comparisons, and larger than one. This preserves
every initially strict comparison sign, including all winner/loser gaps.
For each nonzero g, c(z).g is a nonzero polynomial of degree at most d, so at
most d candidate parameters fail it.

First genericize the target. For a fixed generic target c'_1, two different
wall-crossing times coincide precisely when

    c(z).[(c'_1.g_j)g_i-(c'_1.g_i)g_j]=0.

The bracket is nonzero because the lines are nonparallel and target evaluations
are nonzero. This again excludes at most d parameters. Thus at most

    d*(q+binom(q,2))+1

trials suffice for the source, with q*d+1 for the target. All computations,
root-avoidance comparisons, crossing times and coordinates are rational.
The bit lengths and operation count are polynomial in this EXPLICIT finite
Minkowski input and the objectives. This is not a polynomial-time algorithm in
an unrelated H-description: the required Minkowski representation might be
unavailable or very large.

## 4. Hereditary solved carriers and a quadratic clipping bound

Exposed faces of finite Minkowski sums have the form (3), so they retain such
representations. Of particular use are positive sums of coordinate simplices:

    P = sum_s w_s * conv{e_j : j in B_s},  w_s>0.

These include positive hypergraphic/nestohedral examples; they are a subclass
of generalized permutohedra, not a claim that every generalized permutohedron
has a positive simplex-sum representation.

Construct a graph on the coordinate indices, joining any pair occurring in one
summand. If its nontrivial components have sizes r_1,...,r_c, their difference
vectors span a direct sum of dimensions r_i-1. The affine direction space of
a Minkowski sum is the sum of its summand direction spaces (fix all other
summands to see each inclusion). Hence intrinsic dimension is

    h=sum_i(r_i-1).

All dictionary directions lie inside these components, giving

    q <= sum_i binom(r_i,2) <= h(h+1)/2.                     (6)

An exposed face merely restricts each B_s to its maximizing elements, so the
same argument uses the face's INTRINSIC dimension, not the original number of
coordinates. Arbitrary injective affine images preserve the edge count.
The exact tests construct twelve exposed-face inputs, including point faces,
and check their ranks, direction counts, supporting level and actual routes.

Now take the SAME full-availability deferred clipping certificate already
proved in #206/#209. Its actual carrier dimensions satisfy sum_i h_i<=3e,
where e=n-d. If each selected carrier has a certified representation of the
above kind, its dual sweep supplies actual local cost L_i satisfying
2L_i<=h_i(h_i+1). If h_i<=H, summing gives

    2 sum_i L_i <= (H+1)sum_i h_i <= 3e(H+1).

The actual assembled ordinary-edge budget is therefore

    D + floor(3e(H+1)/2).                                    (7)

Taking H=d and D=1 gives a uniform quadratic bound for this certified carrier
regime, without an excess cutoff, Larman, small detour slack, or a sibling
excess-conservation assumption. This is NOT a proof that arbitrary carriers
admit these representations. For an arbitrary finite Minkowski sum, q need not
be bounded by h(h+1)/2; the explicit direction bound (5) remains its certificate.
A generic zonotope with many directions already refutes that stronger claim.

`PolynomialDualSweepRouting.lean` proves the actual same-certificate assembly
and the doubled summed budget from geometric sweep certificates and (6). The
finite support-slice theorem supplies their edge evidence. The coordinate
simplex dimension/count bridge and the genericization existence argument are
proved here and tested, not yet full additional Lean declarations.

## 5. Exact examples, implementation, and independent checks

The implementation never enumerates the whole Minkowski polytope's vertex set.
The verifier reconstructs the complete direction dictionary and every crossing
from the original summand lists and supplied objectives, recomputes the unique
maximizers between events, and checks the whole exposed segment at an event.
It independently checks endpoint binding, event ordering, all tied summand
points, common directions, consistent orientations and final coordinates.
Higher-rank simultaneous events, omitted events, false diagonals and changed
requested endpoints are rejected. Perturbation trial counts are construction
metadata, not trusted geometric proof evidence.

Executed large examples:

- The spread box in dimension 24: 600 H-facets, 33,554,430 vertices by the
  proved formula, 25 actual antipodal edges. Every returned vertex and edge is
  independently checked against all H-rows; a two-edge full-carrier connector
  is checked separately.
- The permutohedron on 24 coordinates (dimension 23), represented by 276
  segment summands: 24! = 620,448,401,733,239,439,360,000 vertices by its standard
  permutation description. The route crosses all 276 generator directions
  exactly once, so its 276 edges are shortest by sign/inversion distance.
  Only 277 route vertices are constructed; the graph is not enumerated.
- A 15-dimensional positive sum of 120 coordinate simplices from intervals
  on 16 indices: 120 certified edges. It is not a zonotope in the supplied
  representation, and shortestness is NOT claimed.
- An 8-dimensional dense zonotope with 100 distinct directions: 57 separating
  walls and 57 shortest ordinary edges. It is not being incorrectly assigned
  the coordinate-simplex intrinsic bound.

For the small independent cross-checks, the tests enumerate ALL sums of listed
summand vertices, then recover all supporting facets by exact hyperplane
enumeration. A point is retained as a vertex only if its active normals have
full rank; adjacency requires shared rank d-1. These H-graphs have 77 vertices
and 118 edges across eight models, with 893 independently computed ordered
distances. Every constructed route on them is checked against that separate
H-graph. Exact affine changes with row-free translations test coordinate
invariance. Complete H-basis enumeration of the spread family in dimensions
2--4 supplies an additional independent test of (1).

The complete suite checks 441 routes/certificates and 1,456 ordinary-edge
occurrences, twelve intrinsic exposed-face models, 36,213 integer aggregate
budget cases, and seventeen rejected malformed/forged inputs. The receipt
contains the actual source hashes. The general-Minkowski triangle control
returns two edges between adjacent endpoints and leaves their common edge;
this prevents silently upgrading (5) to shortestness or a general
common-face-preservation theorem. To route a given carrier, supply its OWN
exact face model rather than assuming the ambient sweep stays inside it.

## 6. Formalization, integration, and what remains

Three new modules contain 408 Lean lines and thirteen axiom printouts:

- `PolynomialMinkowskiExposedEdges`: support extrema, finite-hull reduction,
  termwise support equality, exact parallel-interval addition, ordinary edges.
- `PolynomialDualSweepRouting`: supporting-slice sweep certificates, actual
  route extraction, and the same-selected-carrier quadratic summed budget.
- `PolynomialSeparatedFacetStars`: disjoint source/target facets and the
  explicit spread-box diagonal-interval decomposition.

They have NOT been compiled in this session. There is no Lean/Lake executable
in the working container; no hosted trial workflow or platform mutation was
used. A compiled generic sweep certificate is not by itself the complete
hypergraphic existence theorem or automatic recognition of an arbitrary
H-carrier. The full cyclic/normal-fan literature is not imported as an axiom.

The next general challenge is still representation or geometric selection:
carriers can have too many directions, no short explicit Minkowski model, and
no target-accessible proper face. This continuation gives a new direct solved
case and a sharp obstruction to a too-restrictive recursive access rule. It
does not replace the unsolved general selection premise with another assumed
polynomial diameter bound.
