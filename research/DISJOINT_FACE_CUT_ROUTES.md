# Route-local conditional expectations for disjoint shallow face cuts of a box

## 0. Status, provenance and the actual new interface

This is a complete written class argument and exact executable research, NOT
Lean compilation, an axiom audit, a Prove2Me verdict, or Polynomial Hirsch.
Starting main is `f2957916eee3d28e407253d0ff8fec6271747f26`. Coordination was
posted on #272 as comment `5690955296`. The accepted/pending formal work, #270's
blocked companion and retired #210 are not altered or retriggered.

#272 controls a GLOBAL edge-direction cover after cuts, with an overlap
certificate. Here we use a different, ROUTE-LOCAL quantity: the exact expected
number of cap detours on a random coordinate-order path. Conditional
expectations choose an order deterministically. The construction uses no LP,
direction catalogue, full vertex graph, complete minimal-nonface list or
random search. It explicitly handles cuts removing WHOLE positive-dimensional
box faces, not only individual corners. A single allowed cut can remove
exponentially many old vertices.

The finite geometry/rank auditor `original_route_exclusion.py` from #271 is
reused byte-identically. Polytope truncation graph facts, the implication from
nonrevisiting paths to the Hirsch bound, and conditional-expectation
derandomization are classical principles; no historical-priority or new
best-known diameter bound is claimed. This contribution is their explicit
input-bound, counted original-edge construction and its executable certificates.
It is not an independent reimplementation of #272's more general cut theorem.

## 1. The checked geometric class

Let B be the nondegenerate axis box l_i<=x_i<=u_i in R^d, d>=2, and let k
additional ORIGINAL inequalities be c_F*x<=b_F. Put S_F={i:c_Fi!=0}, with
s_F=|S_F|>=2. The face F maximizing c_F on B fixes each i in S_F to its
sign-selected endpoint and leaves other coordinates free. Define

    w_Fi=|c_Fi|*(u_i-l_i),
    beta_F=max_B(c_F*x)-b_F,
    alpha_Fi=beta_F/w_Fi   (i in S_F).

Require 0<beta_F<min_(i in S_F) w_Fi. In normalized distances delta_Fi away
from the fixed endpoints of F, the removed CLOSED neighborhood is

    sum_(i in S_F) w_Fi*delta_Fi <= beta_F.

The polytope retains the other side. This neighborhood contains exactly the
old vertices of F and no other old corner. A boundary cap is a weighted
(s_F-1)-simplex times the free-coordinate box.

The code proves neighborhoods pairwise disjoint from the rows. Two distinct
faces must disagree on a coordinate fixed by both. If they disagree on at
least two, then the sums of their normalized distances total at least two,
while each neighborhood has total normalized distance less than one. They
cannot meet. If they disagree on only coordinate i, require

    alpha_Fi+alpha_Gi < 1.

Every point of F's neighborhood is within alpha_Fi of its i-endpoint, and
similarly for G's opposite endpoint, proving disjointness. These tests use all
cut rows; an asserted overlap bound is not trusted. Duplicate/intersecting
faces, touching caps, deep cuts and unsupported charts are rejected.

The box center is strictly feasible: the cut deficit there is
sum w_Fi/2 >= min w_Fi > beta_F. Hence the final polytope P is full-dimensional
and bounded. All 2d+k listed inequalities are genuine facets. For a cap, take
each supported normalized distance alpha_Fi/s_F and each free coordinate at
its midpoint. This lies only on that cap. For an old box facet, pick a corner
on it. If removed, move along a transverse old edge within the facet to the
midpoint of its positive surviving segment; codimension>=2 permits choosing
that direction. This point is strict for every cut. A sufficiently small
move toward the relative center of the old facet makes every other box
inequality strict while retaining every cut slack. The code returns and
checks all these exact rational facet-interior witnesses.

## 2. Complete local geometry and genuine original edges

Every old corner outside the deleted faces remains a vertex. For each old
corner c in one deleted face F and each i in S_F, there is a new vertex on
its transverse old i-edge, at distance alpha_Fi times that edge's length.
Call it (c,i); i is the port. These are ALL vertices. Indeed near a cut only
one added row can be active. A vertex must have at least d-1 active box rows,
so it is on a transverse old edge; the cut equality gives the listed point.
With no active added row, it is an old corner. No two cut boundaries meet.
The exact total vertex count is therefore

    2^d + sum_F (s_F-1)*2^(d-s_F).

The count is a formula, not a claim that the large graphs were enumerated.
All vertices have exactly d tight original rows, with an explicit triangular
inverse. There are three edge types:

1. The positive surviving segment of an old cube edge, joining uncut corners
   or the appropriate cap ports. Pairwise separation makes its length positive.
2. A simplex edge switching ports (c,i)->(c,j) at the same old corner in F.
3. A free-coordinate cap edge (c,i)->(c xor e_j,i), j outside S_F.

Each pair shares d-1 independent ORIGINAL tight rows. The endpoints are
feasible vertices. Their common one-dimensional face is exactly the segment
between them, so the step is an ordinary edge. It is not a projection of an
auxiliary edge. The producer supplies full original-row vertex inverses and
common-row right inverses; #271's unchanged consumer checks the products.

## 3. Lift any coordinate order, with no global graph

For source and target vertices use their unique states (a,p) and (b,q), where
p or q is absent at an uncut corner. Let D be the coordinates where a and b
differ, h=|D|. Choose a permutation of D and flip each coordinate exactly once.

A deleted face F is visited by the base-corner chain in at most one contiguous
interval: all initially wrong fixed coordinates must already be flipped and
no initially correct fixed coordinate may yet be flipped. While the chain
lies in F, free-coordinate flips use edge type 3 with the port unchanged.
Before leaving F along fixed coordinate i, switch to port i if needed, then
use its old-edge segment. Entering a cut face sets the port to that entering
coordinate. At the end, switch to the requested terminal port if necessary.
For h=0, there is just a zero-step path or one simplex cap edge.

The lifted length is h plus the number of required port switches. An internal
visit to a deleted face has exactly one switch: its entering and leaving
coordinates are distinct. Each endpoint face contributes zero or one switch.
Free-coordinate steps are already included in h; counting them again would
wrongly charge an exponentially large face inventory.

Every path of this type is NONREVISITING in the original facets. A fixed
coordinate bound occurs on a single interval because its base coordinate
flips at most once; fractional endpoint/port intervals can only shorten that
interval, not create a second one. Each cap is active precisely during the
single contiguous visit to its deleted face. If both endpoints share an old
facet, it is never left; if they share a cap, the entire path stays on it.
Thus the route preserves every common original facet and the least common
original face. Simplicity and no reentry imply length<=m-d=d+k: each step
acquires one previously unused facet, starting with d.

## 4. Exact expected cost, not an assumed progress potential

Select a uniform random permutation of the remaining D. For each face F,
ignore it if a fixed coordinate outside D is permanently wrong. Otherwise let
A_F be its initially wrong fixed coordinates in D and B_F its initially
correct fixed coordinates in D, with a_F=|A_F|, b_F=|B_F|. The contribution to
the expected number of extra port switches is exactly:

* a_F,b_F>0: 1/binom(a_F+b_F,a_F). The chain visits F iff every A_F coordinate
  precedes every B_F coordinate in their induced relative order.
* a_F=0,b_F>0 (source in F): 1-indicator(p in B_F)/b_F. The first B_F flip
  determines the exit port uniformly, regardless of interspersed free flips.
* a_F>0,b_F=0 (target in F): 1-indicator(q in A_F)/a_F. The final A_F flip
  determines the entry port uniformly.
* a_F=b_F=0: indicator(p!=q), because the whole route remains in F.

No independence between different faces is required; linearity of expectation
suffices. Adding h gives the exact expectation E(a,p;b,q). For corner cuts the
internal term specializes to 1/binom(h,a_F).

At a current state and each remaining coordinate i, compute its immediate
original-edge cost c_i (one or two) and the remaining expected cost E_i.
The tower identity is

    E = average_i(c_i+E_i).

Choose a minimizing i. Repeating gives an actual integer route length

    L <= floor(E(initial)).

The code checks the tower identity in construction; its certificate consumer
checks only the selected exact arithmetic inequality, not the optimization
search. Termination is immediate since one previously unflipped coordinate
is consumed each time. There is no numerical objective-gap assumption and no
risk of infinitely small progress. Work uses O(d^2) candidate evaluations,
each inspecting k face patterns, plus polynomial rational certificate work.
The represented box, original cuts and endpoints are explicit; an arbitrary
hidden cubical representation is not discovered.

## 5. Uniform 2d bound and its sharpness

If h<d and h>0, there are at most h-1 internal visits and two endpoint switches,
so EVERY coordinate-order splice has length<=2h+1<=2d-1. The h=0 case costs at
most one. If h=d, endpoints cannot lie in the same deleted face, and both
endpoint ports belong to D. Each endpoint-switch expectation is at most
1-1/d; the expected internal contribution is at most d-1, because a base path
has only d-1 interior corners and faces are disjoint. Consequently

    E <= 2d+1-2/d < 2d+1,
    L <= floor(E) <= 2d.

With zero or one cut endpoint the bound only decreases. Combining with
nonrevisiting yields the all-pairs class bound

    diameter(P) <= min(d+k,2d).

This does not claim that the expectation-minimizing rule is always shortest.
When EVERY cube vertex is shallowly truncated, choose cap endpoints above
opposite corners with the SAME port i. In a shortest path, let r count old-edge
bridges. Its cube projection has r>=d, with r-d even. Between successive bridges
there must be a cap switch; otherwise the second bridge immediately backtracks.
For r=d, the first and last flip coordinates differ, so at least one endpoint
switch is also needed. The length is at least d+(d-1)+1=2d. For r>=d+2 it is
at least 2r-1>2d. The constructed route attains 2d. Thus the 2d dependence cannot
be decreased for the entire class, although this family has exponentially many
input cuts. The test checks dimensions2,3,5; the argument holds for all d>=2.

Another family cuts every first neighbor of source0 but retains target1.
Every first edge ends at a point with NO target facet, so acquiring the d
target facets requires at least d additional edges. The construction attains
d+1 in every dimension; tests include3,6,12. This is not a Hirsch counterexample.

## 6. Same-input comparison with #272 and a genuine noncorner extension

The exact deterministic `capped_box` generator from #272 is repeated with its
same seed, rows, signs, weights, cut depth1/5 and endpoints0,1. For its actual
prior dimensions4,8,16, the new routes have4,8,16 edges. Its previously supplied
reverse-coordinate comparison has7,15,31 edges and is regenerated/rechecked
using the SAME original rows. Its stored shadow-route counts are not rerun by
this new code. The32D extension of that generator is NEW here:32 edges versus
a rechecked63-edge reverse-order route, with126 genuine facets. It is not
mislabelled an already-executed #272 benchmark.

All four new route lengths d are shortest: the d target upper facets are absent
at the simple source, and an edge can acquire at most one. The expected costs
are16/3,2389/280,11640331/720720,1199323839961/37400557600 respectively. The actual
realized path can beat the floor of its initial expected-cost guarantee.

For the noncorner experiment, remove the earlier corner cuts lying inside the
face x0=x1=0, and add the cut -x0-x1<=-1/5. In dimension32 this single cut removes
2^30 old corners. The resulting input has25 cuts,89 genuine facets and vertex
count formula5,368,709,864. Starting at the cap point(1/5,0,...,0) and targeting1,
the new method returns32 edges with NO shared endpoint facet, expected cost
8897022897629/273491577450 and floor32. Its all-pairs structural bound is57,
not the observed diameter. Neither the huge old deleted face nor the final
vertex graph is enumerated. An8D companion has23 facets and8 delivered edges.
These noncorner inputs are new, not substituted for the same-input comparison.

## 7. Adverse cases, exact checking and reproducibility

The independent small suite reconstructs ALL original active bases and the
rank-adjacency graphs for10 models, including3 positive-dimensional-face-cut
models. It checks2079 bases,156 vertices and256 graph edges. All615 tested
routes have zero reentries and1497 total edges, equal to BFS on these pairs.
For1572 tested coordinate permutations, their exact average matches the stated
formula. Small models do not prove a general optimality claim.

A separate5D/17-corner-cut example explicitly disproves greedy optimality:
the chosen path costs6, while order(3,0,1,4,2) gives5. All120 orders are tested,
and the shorter original-edge certificate is saved. Its five missing target
facets establish shortestness5. Tiny cuts through2^-160, actual cap endpoints,
nonunit rational boxes and positive cut-row rescalings are also tested.
Twenty-one malformed or unsupported records are rejected. Deep cuts and
intersecting/touching caps are limitations, not reported failures of a universal
algorithm. No result is inferred from a timeout.

The consumer rebuilds only the explicit class geometry and chosen finite splice,
checks conditional arithmetic and invokes #271's unchanged original-row inverse
auditor. Saved replay disables order selection, path production, inverse/
elimination discovery and facet-anchor production. It still checks all original
inequalities, exact active sets, right-inverse products, all facet anchors and
common-facet retention. These rational checks are not Lean extraction or a
formal universal correctness proof of the Python parser.

All four stages rerun with two new scripts and one byte-identical dependency.
Full raw reports and17 serialized fixture files accompany the bundle and
regenerate from the committed tests. Compact repository summaries are labeled
as derived research records, never platform receipts. No Actions gate is
appropriate for this research-only contribution.

## 8. Remaining unrestricted obstacle

Disjoint neighborhoods of single ORIGINAL box faces make the visit condition a
simple precedence event, and the cap graph a simplex times a box. Arbitrary
cuts do not have either property. Intersecting caps can require several active
cut rows and do not admit these state/port or expectation formulas. Neither a
low-overlap representation nor a cubical base is asserted for arbitrary carriers.

The progress is a concrete route-local replacement for a global direction
inventory on this class, including exponentially large deleted faces. Extending
it requires proved local transition/visit control, not merely assuming an
expected polynomial number of detours. #267's complete-refinement obstruction
and all existing unrestricted gaps remain in force.

Primary background (not a claim of historical priority): Klee--Kleinschmidt,
The d-Step Conjecture and Its Relatives, Mathematics of Operations Research12
(1987), DOI10.1287/moor.12.4.718; Holt, Maximal nonrevisiting paths in simple
polytopes, Discrete Mathematics263 (2003), DOI10.1016/S0012-365X(02)00525-3.
Project sources at the frozen baseline: `research/CUT_STABLE_DIRECTION_ROUTES.md`,
`scripts/test_cut_direction_routes.py` blob6ba3d4d78784494a1d472339bb11ac7c534b5e14,
and the unchanged #271 `scripts/original_route_exclusion.py`
bloba764196e54970825823cad4575b947b507f95951. The expectation and geometric
specialization above are proved in this note, not inferred from those citations.
