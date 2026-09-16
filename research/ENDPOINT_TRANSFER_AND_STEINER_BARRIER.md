# Direct endpoint-transfer routes and a compulsory stellar-energy barrier

## Status and the change from complete refinement to an actual path

This is written mathematics and exact research code, not a Lean compilation,
axiom audit, or Prove2Me acceptance. It does not prove Polynomial Hirsch.
The live starting point was main `5e811793529ebacce9731c39cfe3d1b9d082e7c2`.
The merged #267 persistence result already rules out a universal polynomial
TOTAL size for forward-stellar flagification. That obstruction is preserved;
this work does not try to rescue its refuted premise with another energy rule.

Instead, we construct actual original edges directly in a classical structured
class. The new project interface counts DISTINCT ENDPOINT TRANSFERS, not all
summand states, all defects, or all vertices of a flag refinement. It retains
all common exposed endpoint faces. A recovered Fano/Steiner construction then
shows why the distinction is useful: an actual nestohedral polytope has a
compulsory positive energy climb under every edge-stellar flagification, yet
its selected endpoints have a directly certified nine-edge shortest route.

The quadratic generalized-permutahedron diameter bound, coordinate-simplex
support formula, and nestohedral realization are classical. No historical
novelty for those statements, or for every equivalent sorting argument, is
claimed. The contributions here are the explicit endpoint-only group count,
its original-H certificate integration, and the universally quantified
positive-barrier construction applied to the current refinement strategy.

## 1. Exact positive construction: one edge per endpoint-transfer pair

Let

    P = sum_{B in C} w_B Delta_B,
    Delta_B = conv{e_i : i in B},  w_B>0,

where C is a finite list of nonempty subsets of an n-element ground set.
The list and positive weights are a SUPPLIED presentation. No claim is made
that this presentation can be found for an arbitrary H-polytope.

For a total coordinate order pi, increasing from left to right, set

    v(pi)=sum_B w_B e_{max_pi B}.

An objective with this strict order uniquely exposes v(pi). Every vertex of
P arises this way: choose a uniquely exposing functional, and perturb it to
have distinct coordinates without changing the unique maximizer. Equivalently,
each of the finitely many summands has a unique maximizing coordinate there,
so any sufficiently small tie-breaking perturbation preserves every summand.
The decomposition of an exposed vertex into these fixed summands is unique.

Fix orders pi and sigma for source x and target y. Put

    s_B=max_pi B, t_B=max_sigma B,
    G={(s_B,t_B) : B in C, s_B != t_B},
    mu_uv=sum_{B:(s_B,t_B)=(u,v)} w_B.

**Endpoint-transfer theorem.** There is an actual ordinary-edge path in P from
x to y of EXACTLY |G| edges. Every summand remains at its source coordinate
until it switches directly to its target coordinate, exactly once if they
differ. Every exposed face of P containing both endpoints contains the whole
path. In particular, when dim P=n-1,

    length = |G| <= binom(n,2) = d(d+1)/2.

The result is a bound for this supplied class, not an unrestricted facet-size
bound. It needs positive weights; cancellation in signed simplex sums is not
covered by this endpoint-transfer proof.

### Construction and the once-only assertion

Transform pi into sigma by fixing sigma's largest coordinate first, then its
second largest, and so on. To fix a coordinate, move it right by adjacent swaps
within the still-unfixed prefix. Fixed coordinates form an unchanging suffix.
Unfixed coordinates retain their original relative order.

For one summand B, until its sigma-largest coordinate t_B is processed, none
of the previously fixed coordinates belongs to B. Consequently the relative
order inside B remains its original order, and its winner is s_B. While t_B
moves right, it becomes B's winner precisely when it passes s_B. No future move
can change it, because t_B is now in the fixed suffix above all remaining
members of B. Thus every summand changes once directly between its endpoint
choices, or never changes if s_B=t_B.

All summands with the same pair (u,v) change at the same swap of u and v.
Different pairs cannot be represented by the same adjacent swap. No unordered
pair is swapped twice, and the opposite orientations cannot both belong to G:
they would require contradictory inequalities in the endpoint total orders.
This proves the exact |G| count and its binomial upper bound. Stationary swaps
are recorded separately and removed from the original route.

### Why each positive event is a whole original exposed edge

At a swap of adjacent coordinates v,u, choose a supporting objective whose
coordinates have that order except for the single tie f(u)=f(v). Every simplex
support face is either a singleton or the coordinate segment [e_u,e_v]. The
WHOLE support face of their positive Minkowski sum is therefore

    a + mu_uv [e_u,e_v].

The two order-induced vertices are its endpoints. For mu_uv>0 this is a
nondegenerate exposed one-dimensional face of P, hence an ordinary edge of
P itself. For zero mass it is a point, not an edge. This is not the projection
of an arbitrary permutohedron or extension edge. The certificate explicitly
checks every component's entire maximizing face and the summed endpoints.

The target rank vector strictly increases on every positive event. Thus the
route has no repeated vertices, independently of deleting stationary swaps.

### Preservation of every common face and scoped optimality

Let f expose any face containing x and y. Support additivity and positivity
force both e_{s_B} and e_{t_B} to maximize f on each Delta_B. Every intermediate
summand choice is one of those two, so every intermediate sum remains in the
same f-face. This proves common-face preservation without a new face-search
or exposure oracle.

The path is shortest in the restricted class where a summand is permitted to
use ONLY its source or target coordinate. Every pair in G must switch on some
edge. All actual edge directions of a positive coordinate-simplex sum are
coordinate differences: equivalently its normal fan coarsens the braid fan,
or directly any one-dimensional support sum has only collinear component
faces. One edge can account for only one unordered transfer pair. Hence any
path obeying the endpoint-only restriction needs at least |G| edges. This is
NOT unrestricted shortestness; Section 6 gives an unbounded approximation
ratio within a familiar class when that restriction is imposed.

## 2. Binding the route to genuine nestohedral H-inequalities

A connected building set B contains every singleton and the full ground set,
and is closed under unions of intersecting members. Give every member a
positive rational weight and let T=sum_{S in B}w_S. The canonical polytope is

    sum_i x_i=T,
    sum_{i in S}x_i >= f(S):=sum_{U in B,U subset S}w_U,
                       S in B, S != [n].                  (1)

These are EXACTLY the positive coordinate-simplex sum, not just inequalities
valid on sampled vertices. To see this without an equality oracle, consider
any subset R. The maximal building-set members inside R partition R: singleton
coverage and the intersecting-union condition prove this. Every building-set
member inside R belongs to one partition block, so its full subset inequality
is the sum of the displayed block inequalities. Thus (1) implies the usual
inequality x(R)>=f(R) for every subset R.

For coordinates c ordered increasingly by pi, summation by parts gives

    c.x = c_max*T - sum_{k<n}(c_{pi(k+1)}-c_{pi(k)})x(prefix_k)
        <= c_max*T - sum_{k<n}(c_{pi(k+1)}-c_{pi(k)})f(prefix_k)
         = sum_{S in B}w_S max_{i in S}c_i.

The right-hand side is the Minkowski-sum support value, achieved by v(pi).
Conversely every simplex sum satisfies every row. Boundedness follows from
the singleton lower bounds and the fixed coordinate sum. Equality of support
values in every direction proves whole-set equality. The positive full-ground
simplex gives dimension n-1.

Every displayed proper S-row is a genuine facet. At the objective equal to
-1 on S and 0 off S, its supporting sum contains the simplex Delta_S in the
S-coordinates and Delta_[n]\S in the complementary coordinates, from the S
and full-ground terms. Their independent direction spaces have combined
dimension n-2. The entire face is contained in the proper S hyperplane, so
its dimension is exactly n-2. For a singleton the first space is zero, as it
should be. Simplicity and the nested face lattice are the classical connected
building-set theorem, cited below.

The code eliminates x_(n-1)=T-sum_{i<n-1}x_i. This is a BIJECTION from the
supporting affine hyperplane to R^(n-1), not an extension projection. Input
A,b must match the complete resulting canonical row system exactly. Raw source
and target coordinates are supplied; endpoint orders are obtained from the
sum of their tight original normals and deterministic coordinate tie-breaking.
An original active-basis certificate verifies strict vertex exposure, and the
recovered coordinate-sum vertices must equal the requested endpoints.

After the whole-support audit, every delivered step receives a SECOND original-
H check: feasible simple endpoints, active inverse identities, one common
original ridge, and the full maximal edge step. All common original facets
are checked again. Verification replays no LP, inverse discovery, or basis
construction. It does reconstruct the small deterministic sorting schedule
and exact component sums. Building-set recognition, the supplied summand list,
and canonical H binding are explicit; unknown affine/projective charts and
arbitrary-H hidden-structure discovery are not implemented.

## 3. Realizing arbitrary higher-defect clutters as actual simple polytopes

Let H be a nonempty antichain of subsets of an n-element ground set, with every
member of size at least three. Define

    B_H = {all singletons} union {S : some N in H is a subset of S}.

It is a connected building set: a union involving a nonsingleton member still
contains its witness N; the other cases follow from singleton intersection.
The unit-weight polytope (1) is therefore a genuine simple rational polytope.

By the classical nested-complex theorem its dual boundary has vertices the
proper members of B_H. Its HIGHER minimal nonfaces are EXACTLY H on the
singleton labels; every other minimal nonface is a pair.

Indeed, two incomparable labels are incompatible if they overlap, or if they
are disjoint and their union belongs to B_H. Every antichain involving a
nonsingleton already has such an incompatible pair because B_H is upward
closed above nonsingletons. A compatible collection thus has a chain of
nonsingletons and singleton labels contained in its smallest chain member.
The only remaining obstruction is a collection of singleton labels whose
union contains a member of H. Its minimal obstructions are exactly H.

This supplies an actual polytopal realization rather than calling the induced
singleton complex itself a sphere. Its facet number |B_H|-1 can be exponential
in n. The construction and tests do NOT hide that cost or call the presentation
polynomial in the original clutter's encoding length.

## 4. A compulsory positive barrier for every edge-stellar completion

Let H be a Steiner triple system on n>=7 labels: every pair is in exactly one
triple. Then q=|H|=n(n-1)/6. In the nested complex above, the initial energy is
W0=q for W=sum_high(|N|-2).

**Barrier theorem.** EVERY finite sequence of forward stellar EDGE subdivisions
that ends flag has an intermediate state with

    W >= q+n-4.

This allows arbitrary earlier auxiliary-edge moves, weight increases, neutral
moves, and unbounded lookahead. It is not just the observation that the initial
productive moves all increase W. Larger-face subdivisions, inverse moves and
coarsenings are outside this theorem.

Proof: consider the first edge in the sequence whose two endpoints are original
singleton labels. Before it, the induced complex on those labels is unchanged:
subdividing an edge that includes an auxiliary label removes no all-original
face, and every new nonface containing a fresh label still contains one. In
particular all q original triples remain minimal. A flag completion must have
such a first edge, since otherwise those triples survive forever.

Let that first original pair be E={a,b}, and let {a,b,c} be its unique triple.
The q-1 triples not containing E persist. There are exactly n-3 triples meeting
E in one endpoint: each of a,b belongs to (n-1)/2 triples, and the shared one
is omitted in each count. For N={a,u,v}, such a mixed triple creates
{z,u,v}. This new triple is minimal. Its pair {u,v} is still an original face;
its pair {z,u} is a face precisely because E union {u} is an old face. That
original triple could be missing only if u=c, which would contradict uniqueness
of the pair {a,u} in both {a,b,c} and N. The same applies to v. The n-3 new
triples are distinct, since two original triples cannot share their residual
pair. They are also distinct from the q-1 unchanged triples because they
contain the fresh z. These forced triples alone give W>=q-1+n-3.

The binary systems H_r={a,b,a XOR b}, on n=2^r-1 nonzero binary labels, give
arbitrarily large required additive energy overshoots n-4. Their full
nestohedra are supplied by Section 3, not enumerated in the larger tests.
This excludes a UNIVERSALLY FIXED additive energy allowance. It does not
exclude a polynomial allowance, a relative-energy allowance, short macros,
or short original paths; the building sets themselves may be very large.

## 5. The Fano case: exact optimal peak and a nine-edge direct route

For n=7 the triples, with zero-based labels, are

    012,034,056,135,146,236,245.

B_H has71 members and its proper labels give70 genuine original facets in
dimension6. Its nested complex has1813 total minimal nonfaces, of which only
those seven triples have size>=3. The barrier proves every edge-stellar
flagification must reach W>=10, even after arbitrary auxiliary preparation.

The following word on the induced seven labels, using fresh labels7,8,...,
translates to the full nested complex by shifting fresh labels to70,71,...:

    01,37,67,03,6-10,06,13,6-13,16,36,24.

The exact energy sequence, checked with unchanged #262 accounting, is

    7,10,8,6,7,5,4,5,3,2,1,0.

Thus the MINIMUM POSSIBLE PEAK is exactly10. Eleven is the length of this
witness, not a proved minimum subdivision count. The final complex has81
vertices. Applying the global flag-size bound would give only81-6=75.

The direct route constructor uses none of these subdivisions. For the vertices

    x=(1,1,2,2,6,17,42), y=(42,17,8,1,1,1,1)

in the coordinate-sum hyperplane sum x_i=71, its endpoint transfers are

    (2,0),(3,0),(4,0),(5,0),(6,0),
    (5,1),(6,1),(5,2),(6,2).

It returns nine genuine original edges. The reference graph has1050 vertices
and3150 edges, is6-regular, and gives distance9 for this pair. Its independently
computed full graph diameter is12. The structural direct all-pairs bound is21,
not9; neither that bound nor the actual diameter is confused with the75 bound
from this particular completed refinement.

Graph completeness here comes from exhaustive coordinate orders together with
the support theorem. Edges are independently reconstructed from original-H
active ridges, and every vertex inverse and original facet witness is checked.
This is not an exhaustive scan of all binom(70,6) H-bases. The lower-dimensional
reference models DO have an independent exhaustive H-basis check.

## 6. A retained adverse family: endpoint-only choices can be costly

Take all interval subsets of [n], with unit weights. Source and target orders
are increasing and decreasing. Every pair u>v occurs as an endpoint transfer
of the interval [v,u], so the direct rule takes binom(n,2) edges.

There is, however, an explicit n-1-edge route between these endpoints. For
k=0,...,n-1 its full coordinate vectors are

    (1,2,...,n-k-1, (k+1)(n-k), k,k-1,...,1).

These are vertices: choose an order increasing on the left block, decreasing
on the right block, and put the middle coordinate last. Consecutive vertices
share n-2 original interval facets and differ along a positive coordinate
edge. Their remaining blocker gives the full next endpoint. The source and
target active sets are disjoint, so every original path must drop n-1 source
facets; this comparison route is shortest.

For n=8,12,16 the executed direct/comparison counts are28/7,66/11,120/15. No
large graph is enumerated. This is the familiar interval nestohedron class;
no new best associahedron-distance theorem is claimed. It proves that the
endpoint-only restricted optimum can be a factor n/2 longer than unrestricted
shortest distance. The direct method is a polynomial bound and an explicit
alternative to global defect repair, not a universally superior routing rule.

## 7. Exact execution and remaining scope

The complete suite is generated by

    python3 scripts/test_endpoint_transfer_routes.py

It has separate support,geometry,barrier,large,negative stages. Every assembled
stage is source-hash bound. Counts and exact certificates are in the full
ENDPOINT_TRANSFER_CHECK.json; the compact committed summary is explicitly
derived. The fixtures include the original Fano inequalities, direct route,
full nested-complex refinement word, and the adverse interval comparison.

Three small original-H reference graphs test448 endpoint pairs, with1691
returned edges versus1648 BFS edges and39 nonshortest outputs. The interval4
and permuta4 models test every unordered distinct pair and all448 possible
square H systems between them; the Fano model uses80 seeded sampled pairs
plus its distinguished pair. All1050 Fano vertex inverses and70 facet witnesses
are checked, and all-pairs BFS establishes its12-edge diameter. Reference
and refined/global graph enumeration are not used by the direct constructor.

The barrier suite checks all21 original first-pair choices,126 choices after
six independent two-step auxiliary prefixes,828 direct nested-definition
comparisons, the eleven-step sharp-peak word, and binary systems through63
labels. Only the seven-label full nestohedron is constructed; larger tests
use the induced triples and the proved realization theorem. They do not claim
an enumeration of their exponentially many building-set facets.

Two unchanged dependencies are reused: #262's stellar_defect_budget.py and
the established simple_tangent_policy_audit.py. The certificate verifier also
passes with inverse and basis production disabled, after an exact JSON round
trip. Negative tests reject altered H-data, omitted edges/factors, false mass,
false walls, invalid weights, incomplete paths, and an alleged first original
pair after one has already been subdivided. Exact code is not Lean-extracted,
and no platform theorem or new compilation/axiom verdict is asserted.

The unconditional conjecture-level issue is still obtaining a comparably
controlled route for arbitrary carriers. A common coordinate-simplex/braid
presentation is a genuine structural assumption, not something established by
this construction. The positive lesson is to count the endpoint events used
by a path instead of resolving every global incompatibility. The adverse
interval example shows a further boundary: forbidding temporary nonendpoint
summand choices is harmless for this quadratic bound but not for shortestness.

## Primary references and attribution

Alexander Postnikov, *Permutohedra, associahedra, and beyond*, arXiv:math/0507163,
Sections6--7, especially Theorem7.4, Proposition7.5 and Proposition7.10.
https://arxiv.org/html/math/0507163
The connected building-set/simple-nestohedron/nested-complex realization is
used with its actual hypotheses, not inferred from an abstract clutter.

Alexander Postnikov, Victor Reiner and Lauren Williams, *Faces of generalized
permutohedra*, arXiv:math/0609184, Section3 and Proposition3.2; Section6.
https://arxiv.org/html/math/0609184
The braid-fan coarsening and quadratic coordinate-swap diameter mechanism are
classical. The direct full-support argument here additionally records precisely
which endpoint-only summand groups move, their exact positive masses, and the
common-face preservation needed by the project.
