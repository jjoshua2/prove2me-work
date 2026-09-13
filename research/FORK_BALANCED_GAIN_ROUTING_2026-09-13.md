# Overlapping unbalanced cycles: a finite fork criterion and hereditary wide cones

## 0. Scope, provenance and the new result

This is an add-only continuation of PR #210 from
`2024394ac48ad8c3220f35e60246154c2904f057`. Earlier coherent-cycle, gain-lattice,
signed, network and Minkowski files remain unchanged. Four earlier Python
sources are reused and separately hashed. No workflow, pin, public theorem,
platform status, or other PR is changed.

The previous coherent-cycle certificate required every nonunit fundamental
cycle to be edge-disjoint from all other fundamental cycles. That condition
was sufficient but unnecessarily restrictive. The new result replaces it by
an intrinsic property of the oriented gain graph:

> Every vertex-simple cycle that is not coherently directed has gain one.

Unbalanced coherent cycles can overlap arbitrarily, provided this property
holds. There can be exponentially many such cycles in a single biconnected
block. They do not have to be listed by the certificate.

The principal new tool is an exact, polynomial-size recognition certificate
based on **forks** and **balanced corridors**. A fork consists of two edges both
entering, or both leaving, the same vertex. The checker verifies a balanced
corridor between their other endpoints after removing that vertex. Components
outside the corridor attach at most once. The paper argument below proves this
test equivalent to the stated all-cycle property, including multigraphs.

Under an independently certified bounded path/cycle transport factor Gamma,
the previous positive cone cancellation now works for every basis of this
larger class. With Gamma<=2 it gives the same derived classical ordinary-edge
bound 256h^3 inside the actual endpoint face of dimension h. Consequently the
existing actual-carrier assembly gives D+768H^2(n-d). This does NOT prove that
arbitrary carriers meet the criterion or settle Polynomial Hirsch.

The analytic diameter theorem is Dadush--Haehnle's classical wide-normal-fan
theorem, not a newly claimed classical result. The new Lean file contains
finite path/corridor algebraic cores and is UNCOMPILED. The complete recognition,
all-basis geometry, and hereditary existence theorem are mathematical proofs
and exact executable checks, not all end-to-end Lean declarations.

## 1. Gain graph and the property that actually matters

The input consists of real inequalities with at most two nonzero coefficients
per row. Every binary row has opposite signs. Orient it from its negative to
its positive coefficient. The homogeneous equality is

    x_v = g_e x_u,       g_e > 0.

Traversing an edge in reverse multiplies by 1/g_e. The gain of an oriented
traversal is the product of these factors. A cycle is balanced when its gain
is one; this is independent of which direction it is traversed. A cycle is
coherently directed when all its edges can be followed in one common direction.
An incoherent cycle has an orientation reversal at some vertex.

Positive-proportional binary normals may be represented once in this NORMAL
GRAPH. All their original inequalities and RHS values are retained in route
verification. Unary rows, either sign, and constant rows are retained too but
do not define graph edges. Oppositely oriented parallel arcs are distinct and
can form a coherent two-edge cycle. Same-direction parallel arcs of different
gains form an incoherent unbalanced two-edge cycle and fail the new criterion.

The criterion concerns every simple cycle, not just a chosen fundamental
cycle basis. A fundamental-cycle-only check can miss gain cancellation or a
bad cycle formed by combining otherwise acceptable generators.

A global positive diagonal x_i=s_i z_i changes each edge gain to

    g'_e = g_e s_u/s_v.

Closed-cycle gains and coherence are unchanged. Discovery first normalizes a
spanning forest this way. No common rational base or integer exponent lattice
is required. This forest gauge is not claimed to minimize Gamma; a failed
Gamma threshold is not a proof that no better gauge exists.

## 2. Fork corridors: proof of sufficiency

Fix a vertex v and two incident edges of the SAME local orientation: either
both point away from v or both point toward it. Let their other endpoints be
s,t. Let a and b be their gains when traversed from v toward s and t,
respectively, using reciprocals for incoming edges.

Every simple s--t path P in the graph with v removed closes these two edges
to an incoherent simple cycle. That cycle is balanced precisely when

    gain(P) = b/a.                                           (1)

If s,t are disconnected after removing v, there is no such cycle and no
condition is necessary. If s=t, a zero-length path exists and (1) is a=b,
which correctly checks parallel same-direction rows.

For a connected fork, a certificate supplies a set H containing s,t, positive
numbers p_x for its vertices, and the following finite conditions:

1. H induces a connected graph.
2. Every induced edge u->w satisfies p_w=g_e p_u.
3. a*p_t=b*p_s.
4. Every connected component of the graph outside H (and outside v) has at
   most one neighbor in H.

Condition 4 is essential. An arbitrary balanced path alone would not certify
alternative paths through an omitted, unbalanced region.

A vertex-simple s--t path cannot leave H: entering an outside component and
returning would force both crossings through its unique attachment, repeating
that vertex. Within H, multiplying condition 2 along the path telescopes to
p_t/p_s, and condition 3 gives (1). Thus EVERY simple cycle using that fork
is balanced. Every incoherent simple cycle has at least one fork, so complete
fork coverage proves the desired all-cycle property.

The verifier checks the separator condition by ordinary component search. It
does not trust the constructor's block decomposition, nor enumerate cycles.
Original row IDs, direction, all potentials, and all induced edges are checked.

## 3. Completeness: the corridor test is not just another guessed template

Suppose every incoherent simple cycle is balanced. For a fixed fork all simple
s--t paths in the vertex-deleted graph must then have the same gain b/a.
Take the block-cut tree of that graph. The minimal corridor is the union of
the blocks on its s--t path. Its outside components attach at most once, and
every simple s--t path lies inside it.

It remains to prove that this corridor is balanced, so positive vertex
potentials exist. In each block on the corridor, fix its two distinct entry
and exit vertices. Any simple path between those ports extends to a simple
s--t path by fixed paths through the other blocks. Therefore all port-to-port
paths inside the block have one common gain. A bridge is automatically balanced.
For a two-connected block, use the following lemma.

**Lemma.** If all simple a--b paths in a finite two-connected gain graph have
the same gain, every cycle in that graph is balanced.

Start with a cycle through a,b. Its two a--b arcs have the same gain, so the
cycle has gain one and admits positive vertex potentials. Extend by an open-ear
decomposition of the block. At an ear with endpoints u,w already in the old
two-connected subgraph, there are vertex-disjoint connectors between {a,b} and
{u,w}, in one of the two matchings (including trivial connectors when endpoints
coincide). This is the elementary two-path consequence of vertex connectivity.
Together with the new ear they form a simple a--b path. The old subgraph's
potentials determine both connector gains. Comparing with any old a--b path
forces the ear gain to equal the old potential ratio p_w/p_u. Extend potentials
along the ear. Induction covers every vertex and edge of the block, including
single-edge ears and parallel-edge two-cycles. This proves the lemma.

Apply the lemma block by block and rescale each block's potential at the shared
articulation. The whole corridor is balanced and has the required endpoint
ratio. Thus the fork test is NECESSARY AND SUFFICIENT for the all-incoherent-
cycles-balanced property. It is not asserted necessary for having wide cones
or short edge routes: an incoherent unbalanced cycle far from resonance may
still be well conditioned, and actual RHS feasibility may exclude bad bases.

The implementation discovers corridors with an edge-ID-aware Tarjan block
algorithm. For each fork it returns only vertex potentials and an attachment
certificate. There are at most O(m^2) forks for m binary normal rays, each with
at most d potential values. Straightforward construction and verification take
O(m^2(d+m)) rational graph operations, with polynomial encoding sizes. This
recognition step does not enumerate independent bases, vertices, or cycles.
The full route search has separate, weaker complexity guarantees below.

## 4. Why arbitrary overlap does not hurt the basis-cone argument

A nonsingular square basis of opposite-sign two-variable rows partitions into
connected support components. A component on k variables must have k rows.
Its binary edges connect the component, so it is either:

* a binary tree with one unary pin; or
* a unicyclic binary graph with no unary pin.

The cycle in a nonsingular unicyclic component cannot have gain one: that would
leave a homogeneous degree of freedom. The new all-cycle property therefore
makes it coherently directed. This conclusion holds for EVERY basis, no matter
how many cycles overlap in the complete support graph.

Conversely, when the full row rank is d, an incoherent unbalanced cycle is an
independent row collection and extends to a full basis. Such a basis has an
incoherent unicyclic component. Hence the fork criterion exactly recognizes
whether this particular all-basis cycle classification is available. It does
not infer that all basis cones must be narrow when the criterion fails.

### A compact common transport bound

In the global forest gauge, assign each distinct binary ray the distortion

    M_e = max(g'_e,1/g'_e) >= 1.

Let Gamma be the product of the d largest M_e, or all of them if fewer than d
exist. Every simple path has at most d-1 edges and every simple cycle at most
d, so both path products and cycle products, in either orientation, lie in
[1/Gamma,Gamma]. This bound is computed without listing paths or cycles.

This is a sufficient transport bound, not an optimum. In a diamond chain below,
all residual gains except one equal one, so Gamma is independent of how many
diamonds or coherent cycles exist.

### Reuse positive cone cancellation, not the old support-graph restriction

Within one basis component, a secondary diagonal makes a spanning tree's
homogeneous gains equal one. Normalize its smallest scale to one. Ratios of
its scales are simple path gains, so its condition number is at most Gamma.
In a unicyclic component the remaining cycle is coherent, and its normalized
rows satisfy

    sum_cycle a_j = (1-G)e_r.

The center sign(1-G)e_r plus the off-cycle tree rows has cycle dual margins
1/|1-G|. Corresponding dual column norms are at most Gamma*sqrt(d)/|1-G|;
off-cycle dual margins are one with norms at most sqrt(d). The cycle defect
cancels. The complete center has norm at most 2d. Returning to the SAME global
metric loses at most another factor Gamma, yielding

    tau >= 1/(2 Gamma^2 d^(3/2)).                             (2)

This is the earlier coherent positive-cone proof with a NEW all-basis
recognition theorem, not a second implementation of that proof. The code
reuses the old center constructor on the single basis only. A basis always
has the required tree/unicyclic components. It then transports the center back
and independently verifies the squared margins against the actual globally
normalized basis. The complete support graph is never offered to the old
isolated-cycle checker as if it passed that stronger condition.

## 5. Heredity in actual common faces, with the transport bound justified

Let x,y be feasible vertices and fix ALL original equalities tight at both.
A free connected equality component has positive potential ratios. An
inconsistent gain cycle or unary pin removes its free variable. Choose one
original coordinate as root for each remaining component; all its coordinates
are affine positive multiples of the root variable. This is onto the full
equality solution space.

Substituting in original rows produces opposite-sign binary rows between free
components, unary rows, or constants. Every nonconstant row is strict at the
endpoint midpoint; otherwise it would already be common tight. The quotient
therefore is the actual common face in intrinsic full-dimensional coordinates.

Take any simple binary path in this quotient. Inside each equality component,
join the incoming and outgoing attachment vertices by its tree path; at the
two endpoints use the representative root. Distinct quotient vertices are
disjoint original components, so the lifted path is simple after cancelling
immediate tree backtracking. Its original gain equals the quotient gain.
A simple quotient cycle similarly lifts to a simple original cycle.

If that quotient cycle is unbalanced, its lift is an unbalanced original cycle
and is therefore coherently directed. Contracting positive equality edges
preserves direction at the surviving binary rows, so the quotient cycle is
coherent too. Thus the all-incoherent-cycles-balanced property is hereditary.

The lifted paths and cycles also prove the SAME original Gamma bounds all
simple quotient transports. This does not assert that multiplying the largest
entries of the contracted matrix would itself return a number <=Gamma; that
coarser computation could overcount repeated internal transports. The route
wrapper retains the inherited Gamma, reconstructs the exact equality quotient,
checks its forks independently, and checks every visited cone in its root
coordinates. The graph lifting argument above supplies the all-basis
hereditary bound rather than silently assuming a new dimension calibration.

Reapply (2) with intrinsic dimension h. For Gamma<=2, tau>=1/(8h^(3/2)).
Dadush--Haehnle's CLASSICAL Theorem 3 / 11 gives

    diameter <= (8h/tau)(1+ln(1/tau)) <= 256h^3.              (3)

The point case has cost zero. The external theorem permits nonsimple vertices
and unbounded pointed polyhedra. It is not imported as a new Lean axiom here.
As before, verified sum h_i<=3(n-d) on the SAME actual selected carriers gives
D+768H^2(n-d) when all such carriers have this certified regime and h_i<=H.
The existing generic cubic-cost adapter is reused; no duplicate cost wrapper
or cosmetic root dependency is added.

## 6. One biconnected block with exponentially many unbalanced cycles

Take r diamonds in series. Diamond j has a split vertex, two internal vertices,
and a merge vertex; the merge is the next split. All four edges point forward
and have gain one. Add one return edge from the final merge to the initial
split with gain G!=1.

The graph has d=3r+1 coordinate vertices and 4r+1 binary rays. Every simple cycle
not using the return edge is the four-edge cycle inside one diamond and is
balanced. Every cycle using the return chooses one of two branches independently
at each stage. There are EXACTLY 2^r such cycles; all are coherently directed,
all have gain G, and all share the return edge. They lie in one biconnected
block. The old edge-disjoint fundamental-cycle condition rejects even r=1.

In the new certificate there are only 2r forks. Each corridor is the other two
edges of its diamond, with three vertices and unit potentials. Thus the whole
million-cycle example below uses only forty fork checks and 120 corridor
potential entries. No exponential cycle list is computed or hidden in the input.
A forward spanning forest leaves only the return gain nonunit, so
Gamma=max(G,1/G), independent of r.

### An explicit bounded original-H polytope and feasible resonant target

Add all d coordinate lower bounds x_i>=0. Give forward vertices levels 0,1,2,...,
2r; the two branch vertices at a stage have the same level. Three edges in each
diamond have upper RHS equal to the level difference, one. The fourth (lower
branch to merge) has RHS 4/3. Put RHS 1-G on the return edge, with 0<G<1.

The source is zero. Set T=1+2rG/(1-G) and target x_i=T+level_i. Every source
coordinate lower bound is tight. At the target the three tree edges per diamond
and the return edge are tight; the remaining branch edges have slack1/3.
These d target equations are independent because the spanning tree plus its
nonunit return cycle pins the free parameter. Both requested endpoints are
vertices and share no tight row.

The system is bounded: its forward rows imply x_last<=x_first+2r, while the
return gives x_first<=G*x_last+1-G, hence x_first<=T and all other coordinates
have finite upper bounds. The midpoint is strict in every nonconstant row.
There are 7r+2 ORIGINAL inequalities; this count is not needed as an irredundant
facet claim for the large examples.

At G=1-2^-240 the target basis has an inverse entry 2^240, but its positive
cone has a certificate with no inverse-gap penalty. In the executed r=20
example, d=61 and there are142 rows,1,048,576 unbalanced simple cycles,40 forks,
and120 corridor potential entries. The feasible target cone's minimum squared
margin is exactly1/2501. This large case verifies the structural and cone
certificates; it does NOT claim to have produced its full source-target route.

Complete original-edge routes are constructed separately for r=4,8,12:

| r | dimension | input rows | unbalanced cycles | constructed edges |
|---|---:|---:|---:|---:|
|4|13|30|16|13|
|8|25|58|256|25|
|12|37|86|4,096|37|

The graph and full vertex set are not enumerated. Shortestness is not claimed
for these sampled routes. Two overlapping-cycle blocks with unrelated gains
1-2^-120 and1-3^-60 are also joined at an articulation and routed. The target
is degenerate in that example. Their opposite two-adic valuation signs exclude
a common integer-power base, as in the previous argument. Three additional
cases recover unknown coordinate scales and shuffled row order.

## 7. Evidence actually executed

The exact fork criterion is compared to independent exhaustive simple-cycle
enumeration on15,756 gain graphs through four vertices (each possible edge is
absent or has either orientation and gain one or two). All4,630 accepted graphs
and all rejected graphs agree. Another216 three-parallel-edge multigraphs and
300 sampled gain graphs in dimensions five through seven agree as well.

The cone audit checks2,118 basis subsets and756 nonsingular cones with a
separate rational Gaussian inverse. The 4D and5D libraries are exhaustive;
the 6D and7D libraries sample700 and500 subsets. The all-basis theorem comes
from the graph classification, not these samples.

Seven independently reconstructed original-H graphs give184 vertices,470 edges,
and9,624 ordered graph distances. There are1,694 small route certificates and
4,712 checked edge occurrences, including30 stationary symbolic pivots counted
separately. All nonstationary steps are independently checked in those graphs.
The dense6D model checks30 selected endpoint pairs; the other six models check
all unordered pairs including stationary cases. The1,590 nonpoint endpoint
faces receive independent fork and cone checks.

The larger/scaled suite and the million-cycle cone are listed separately in
the execution receipt. Twenty-one malformed or forged cases are rejected,
including incomplete forks, a hidden corridor bypass, false separations,
unequal forward-path gains, same-direction resonant parallel arcs, omitted
cone witnesses, false widths, changed endpoints and diagonals offered as edges.
A positive attachment control confirms that an unrelated unbalanced branch
attached at one corridor vertex need not be included in that fork's proof.

All numerical arithmetic is rational. The route verifier reuses the exact
original-H gain-shadow checks and adds the global gauge, fork and cone evidence.
Stationary limiting pivots remain in the basis chain but are not edge costs.
Its finite seeded objective sampler is NOT Dadush--Haehnle's random distribution;
there is no claimed uniform polynomial pivot/runtime bound for it or the
capped degenerate endpoint-basis search. The fork recognizer is polynomial;
the route sampler's runtime is a separate assertion and is not upgraded by it.

## 8. Formalization, attribution and the remaining boundary

`PolynomialForkCorridorCertificates.lean` contains seven new axiom printouts:
path-product telescoping, endpoint ratios, closing a balanced fork cycle,
unit-cycle return, detection of an orientation reversal, interval propagation,
and impossibility of a simple outside excursion with a single attachment.
The file is an UNCOMPILED candidate. In particular, compiling these finite
cores would not by itself formalize the full block-cut/ear-decomposition
recognition theorem, gain-face lifting argument, all-basis cone theorem, or
analytic diameter theorem. Those dependencies remain explicit.

The cited analytic result is Daniel Dadush and Nicolai Haehnle, *On the Shadow
Simplex Method for Curved Polyhedra*, arXiv:1412.6705, Theorems3 and11. Its stated
bound is8h/tau(1+ln(1/tau)); its discussion explicitly distinguishes diameter
existence from efficient implementation in degenerate cases. Primary source
checked in this continuation: https://arxiv.org/html/1412.6705 .

No new best classical diameter bound is claimed. The contribution here is the
complete finite fork recognition argument, its replacement of the isolated-cycle
hypothesis, the hereditary path-lifting bound, and exact certificates on
exponentially overlapping cycles. The class still excludes incoherent
unbalanced cycles, may have an excessive Gamma in the chosen gauge, and does
not cover arbitrary signed or dense inequality systems. Failure of this
structural test is not a graph-diameter lower bound. In particular, restrictions
based only on feasible bases or direct row-retirement arguments may handle
rejected systems. General Polynomial Hirsch remains outside the conclusions
proved here; no circular root premise or new open platform child is introduced.
