# Direct H-description network routes, including degeneracy and actual-face reduction

## Contribution and verification boundary

This is a continuation of draft #210's direct-carrier work. It does not require
its Minkowski representation, a direction dictionary, or the conversation-only
selective-carrier package. It adds new files only. The originating baseline is
#210 source `af2cbabad26379425a889856b53239ddd148c4fd`; the final commit/handoff
records the actual parent if another agent advances that branch.

The diameter bound for dual network flow polyhedra is CLASSICAL. The primary
reference is Borgwardt, Finhold and Hemmecke, *Quadratic diameter bounds for dual
network flow polyhedra*, Mathematical Programming 159 (2016), 237--251,
DOI 10.1007/s10107-015-0956-4, arXiv:1408.4184. Theorem 1.1 and its proof supply
the target-insertion strategy and polynomial edge count. This continuation
makes that strategy operate directly on exact original H-data, with an explicit
zero-pivot treatment instead of a generic perturbation, and adds actual-carrier
quotient/irredundancy certificates and the repository-specific aggregate bound.
It is not a claim to a new classical network diameter theorem.

All three new Lean modules are UNCOMPILED proof candidates. The complete
algorithmic existence/termination argument below is not automatically a Lean
theorem because its scalar, forest, and budget primitives have proof bodies.
The exact Python runs and their source-hashed receipts were executed separately.
No new hosted workflow, platform submission, toolchain change, or credential
operation was performed.

## 1. The whole input is an inequality system, not a decomposition

Let G have N nodes, M directed arcs, and a distinguished node 0. Define

    P = {x : x_0=0, x_b-x_a<=c_ab for every supplied arc a->b}.

Parallel, redundant, and oppositely directed rows are permitted. Constants may
be negative. The numerical router takes TWO specified feasible vertices of
this set; it does not assume that a list of sample vertices is complete. The
main routing argument does not require boundedness or strict feasibility.
For the later Hirsch carrier application the parent is bounded, as before.

For a feasible point x, form the undirected graph of its tight arcs. Its row
kernel consists of functions constant on every connected component. Pinning
coordinate 0 removes the global constant direction. Therefore x is a vertex
exactly when this tight graph is connected. A spanning tree is a short exact
certificate of that fact. For necessity, a disconnected component can be
shifted a sufficiently small amount in both directions while all finitely
many slack inequalities remain satisfied. For sufficiency, equality on all
active tree rows uniquely determines x from x_0=0.

For two feasible vertices, their common tight graph with exactly two connected
components has a one-dimensional pinned kernel. If they are distinct, this
common-equality face is their edge: the constraints tight at opposite endpoints
bound the one remaining parameter on both sides. The implementation checks
both connected components; merely proposing a cut direction is insufficient.

The first Lean module proves constancy along tight-row graph walks, the vertex
criterion in its spanning-path form, the two-block kernel formula, and the
ordinary-edge conclusion with explicit endpoint blockers. No graph isomorphism,
diameter bound, or identification of circuits with actual edges is an input.

## 2. Target-tree insertion with zero-distance basis exchanges

Choose a spanning forest of ALL arcs tight at both requested endpoints. Extend
it to a current tight tree T and a target tight tree T*. Call the initial forest
locked. All its equalities remain fixed. This already confines the entire
construction to the endpoints' smallest common face, including nonsimple
endpoints and lower-dimensional input descriptions.

Consider an as-yet unlocked target arc r->s. Contract the locked forest
conceptually. The current quotient tree still spans the quotient nodes.
If the target arc is already tight, exchange any unlocked tree edge on its
cycle for that arc and lock it. This changes only the basis, not the point.
Otherwise the unique r-to-s tree path has a backward arc: if every unlocked
arc pointed forward, summing their tight inequalities and using feasibility
of the target would imply that r->s was already tight. Locked differences are
equal at the current and target points and cancel regardless of orientation.

Delete the LAST backward unlocked arc along the r-to-s traversal. Let R,S be
the two tree components, with r in R and s in S. The removed arc points from
S to R. Increase all coordinates in S by theta, subtracting theta from every
coordinate as well when 0 is in S so the gauge stays zero. The maximal feasible
step is

    theta = min_{a in R,b in S} [c_ab-(x_b-x_a)].

The target arc occurs among these blockers, so the minimum exists and is
finite, even for unbounded P. Every other row is unchanged or becomes looser.
Insert one attaining R-to-S arc, breaking ties deterministically. The new
basis is again a spanning tree and every basis row is tight.

If theta>0, the common tight graph contains the two connected components of
T minus the deleted arc. No common tight arc can cross them, because its
value changed by theta or -theta. Consequently the two vertices are joined
by an ORDINARY EDGE. If theta=0, this is a stationary basis exchange: it is
recorded and checked but never counted or advertised as a graph edge.

This explicit handling covers multiple simultaneously tight blockers and
nonsimple vertices without moving to a perturbed polyhedron and then claiming
that a perturbed edge projects to an original edge. The original inequalities
are checked after EVERY exchange. A terminal zero exchange can insert the
chosen target arc if it became tight together with a different blocker.

### Why the insertion phase terminates, also when theta=0

In the quotient tree, consider nodes with a directed tree path toward s. In
the original tree, locked arcs can be traversed in either direction; all other
arcs must be forward. This protected rooted subgraph never loses an edge
during the phase: the selected deleted edge is backward, and the directed
suffix beyond it is protected. Its tail is protected and is in S at every
future cut of this phase.

An arc once deleted therefore cannot be reinserted: entering arcs go R-to-S,
whereas that arc's tail is permanently on the S side. This statement depends
only on the evolving tree, not on strict coordinate movement, and so applies
to zero steps too. Every pivot deletes a previously undeleted original arc;
there are at most M pivots before the target equality is acquired.

More sharply, no unordered quotient-node pair is deleted twice. A parallel
same-direction arc cannot be reinserted for the reason above. If the reverse
arc is ever inserted, it and its tail acquire a permanent directed path to s,
so that reverse arc cannot later be deleted. With q quotient nodes, there are
at most binom(q,2) deletions. The independent verifier tracks BOTH deleted arc
IDs and unordered quotient pairs, and rechecks the protected-node invariant
at each step.

After acquisition, lock the target arc. This decreases the number of quotient
nodes. If h=N-1 minus the rank of the initial common forest, there are at most
h phases. Let M0 be the number of original arcs not constant after the initial
common contraction. The positive edge count is bounded by

    L <= min(h*M0, sum_{q=2}^{h+1} binom(q,2))
      = min(h*M0, h(h+1)(h+2)/6).                  (1)

The same bound includes the nonterminal zero pivots. Terminal basis-only
exchanges add at most h operations, not edges. The published diameter estimate
is consistent with (1); our contribution is the exact degenerate replay and
its integration, not a stronger classical asymptotic bound.

The proof does not imply shortestness or monotonicity in an arbitrary objective.
Initial common facets remain fixed, which can exclude a globally shorter route
that leaves the smallest common face. Both properties are stated explicitly.

## 3. Recover the intrinsic common face and its actual facet count

The aggregate Hirsch bound needs the number of INTRINSIC facets, not all rows
of a padded ambient description. This can be recovered without vertex
enumeration in the difference-constraint class.

Let rho(i) label the connected components of the original common tight graph.
Choose a representative r_C of each component, with r_{rho(0)}=0. Using the
TARGET t, set offsets o_i=t_i-t_{r_{rho(i)}}. Every point of the actual common
face has the unique form

    x_i = z_{rho(i)} + o_i.

For an original arc a->b, the quotient constraint is

    z_{rho(b)}-z_{rho(a)} <= c_ab-o_b+o_a.          (2)

A loop after contraction is a constant valid inequality. Every other original
row is retained initially. The equations from a spanning forest prove both
inclusion and surjectivity of the lift, not just containment in some convenient
larger network polytope. The quotient has h+1 nodes, so intrinsic dimension h.

The midpoint of the requested vertices is strictly feasible for every
nonconstant quotient row: a row tight at both endpoints would already have
been contracted. This gives exact positive reduced arc lengths.

A remaining arc a->b is redundant precisely when another directed path from
a to b has total bound at most its own. Sufficiency is telescoping addition
of the inequalities with multipliers one. Necessity is the standard shortest-
path potential characterization: with positive reduced lengths, the shortest
path bound is the strongest implied difference; if none is short enough, a
feasible potential violates the removed arc. No negative cycle is possible
because an explicitly feasible midpoint is available.

The normalizer removes rows sequentially and records a directed path for each
removal. The verifier replays those implications on the then-current row set;
references to later removed rows are safe because equality of feasible sets
is preserved inductively. It separately checks that no retained row is
redundant. A full-dimensional irredundant nonconstant H-description has one
row per facet, so the retained M is the ACTUAL intrinsic facet count.

Running (1) on this normalized model and lifting each step therefore gives

    local edge cost <= h*M.                       (3)

Every lifted step is independently rechecked in the ORIGINAL H-system:
feasibility, vertex connectivity, preservation of the original common rows,
and two-component common connectivity. The quotient and redundancy checker
never enumerates the full polytope graph.

### Positive diagonal recognition rather than a supplied chart

The optional H-input front end accepts one- or two-variable inequalities.
For a two-variable row, the nonzero coefficients must have opposite signs.
It solves positive scale equations

    a_i*s_i = -a_j*s_j

by a graph traversal. Every cycle is checked for consistency. The recovered
change x_i=s_i*y_i, followed by positive row normalization, converts ALL rows
to differences or coordinate bounds. No rows are silently dropped by this
recognizer. Single-coordinate rows use node 0.

This handles unknown positive diagonal scalings, arbitrary positive row scales,
and row permutations. It is not recognition under an arbitrary unknown dense
affine map. An inconsistent gain cycle or a three-term row is an unsupported
model, not evidence of large diameter. Three scaled examples in dimensions
4,8,16 pass; a forged scale and an inconsistent multiplicative cycle are
rejected. The verifier binds the whole original H-input and endpoints by hash
and rechecks the original inequalities after lifting.

## 4. A case where the previous direction-count budget is exponential

For r>=2 consider

    0 <= z <= y_i <= 1, i=1,...,r.

This is an (r+1)-dimensional pyramid over an r-cube. It has 2r+1 genuine facets:
z>=0, y_i>=z, and y_i<=1. Its network has root0, central node z, and r leaf
nodes, so it is immediately recognized by the new method.

Every point can be written as z times the apex (1,1,...,1) plus (1-z) times a
base point (0,w), w in [0,1]^r. Thus its complete vertex set consists of the
apex and all 2^r base cube vertices. Each base vertex is adjacent to the apex;
a zero base bit retains the equality z=y_i at both endpoints, while a one
base bit retains y_i=1. Equivalently, the shared tight graph has two
components. Their direction vectors (1,1-w) are pairwise nonparallel because
their first coordinate is one. Hence there are at least 2^r TRUE edge directions
in only 2r+1 H-rows.

Any complete direction dictionary for #210's sweep bound must include these
actual directions. Replacing a poor Minkowski representation cannot make that
particular full-direction-count upper bound polynomial here. The network
method instead has the classical bound (1), directly from O(r) input rows.
The actual pyramid has diameter two, not a hard graph; the purpose is to
separate the CERTIFICATE REGIMES rather than claim a new difficult polytope.
For d=24 the example has47 facets and8,388,608 apex edge directions. The
constructor certifies an apex edge directly, without listing those directions.

The common-face-preservation limitation is visible here too: opposite base
vertices have a two-edge route via the apex, but a route preserving their
initial common base facet takes r steps. The algorithm does not claim to find
a globally shortest route. The direct method remains polynomial either way.

## 5. Actual selected carriers give a quadratic aggregate bound

Verified #206/#209 provide a full-availability certificate with e=n-d and

    sum_i M_i <= 6e,

for the actual selected portal-pair carriers' minimum intrinsic row counts.
If those carriers admit exact network coordinates recognized as above,
normalization and (3) give L_i<=h_i*M_i. Therefore, for h_i<=H,

    sum_i L_i <= H*sum_i M_i <= 6H e.

The SAME deferred callback assembles those routes, so its ordinary-edge cost
is at most

    D+6H(n-d).                                      (4)

At D=1,H=d this is quadratic, without a supplied Minkowski model, low-excess
cutoff, chosen small detour slack, or additive sibling-spill assumption.
A carrier-coordinate equality is still required; arbitrary matrices are not
asserted to be network matrices. This is a hereditary structural sufficient
class, since common-face contraction preserves difference inequalities.

The Lean aggregate module proves (4) from actual selected-pair routes and
their h_i*M_i bounds. The network algorithm supplies these mathematically and
numerically, but the WHOLE algorithm-to-affine-carrier bridge is not yet an
end-to-end Lean existence theorem. The same warning applies to positive
scaling recognition and the all-input termination proof. Generic rank/kernel
and list-budget primitives do not secretly discharge those larger interfaces.

## 6. What actually ran

The core suite completely enumerates nine small rational H-models and their
graphs:145 vertices,244 edges,2,745 ordered distances. It checks1,300 requested
vertex pairs,3,428 ordinary-edge occurrences,362 zero pivots, and189 terminal
basis exchanges.546 pairs have a nonsimple endpoint. Independent enumeration
is TEST-ONLY; the router does not call it.

Large unenumerated tests include:

| Input | H rows | Actual edges | Zero pivots |
|---|---:|---:|---:|
| unperturbed24D spread box |600|25|22|
| perturbed24D spread box |600|86|1|
| perturbed50D spread box |2550|227|2|
| dense16D rational network |272|11|0|
| dense32D integer-reweighted network |1056|16|20|

The last case has65 tight rows at the source and72 at the target, directly
exercising degenerate endpoints. The perturbed cases do not rely on any
zonotope representation or on preserving the unperturbed graph. Their route
lengths are not claimed optimal.

The normalization suite cross-checks178 actual endpoint-face facet counts
against independently enumerated H-faces,492 lifted route edges, and750 row
removals. A24D,600-row example contracts to dimension17 and removes488
redundant nonconstant rows, leaving78 intrinsic facets; an11-edge route is
verified in the original600 inequalities. Positive diagonal recognition works
on three additional H-models. Cube-pyramid controls check180 apex edges;
small complete H-enumeration also confirms the vertex and degree formulas.
The suite checks39,442 aggregate arithmetic cases. The two suites reject
25 forged/malformed inputs in total, with separate cube-diagonal and gain-cycle
controls distinguishing circuits/unsupported matrices from actual edges.

The runtime is polynomial in this network H-description and rational bit size.
Current vertices are determined by a spanning tree and therefore by sums of
at most N-1 original bounds; their bit complexity does not accumulate
exponentially through repeated pivots. Redundancy testing uses exact Dijkstra
searches on positive reduced lengths. This is not a general strongly
polynomial linear-programming algorithm: its matrix class is restricted.

## 7. Lean and publication status

The packet adds three Lean candidates: forest/kernel ordinary-edge criteria,
affine quotient and path-implication identities, and counted-pivot/aggregate
budget primitives. There are435 lines and15 axiom printouts. No Lean/Lake
executable was available in the originating container, and GitHub DNS access
from that container failed. No speculative hosted compile was substituted.

The exact tests are not a kernel verdict, and no new theorem is claimed
accepted on Prove2Me. The next formal work is a finite tree invariant and
termination proof binding the target-phase deletion stamps to the ordinary
edge count, followed by the affine network-image wrapper. The current files
contain complete candidate proofs of their stated cores, not placeholders for
those missing larger theorems. The verification handoff lists the exact gates.

The general Polynomial Hirsch question remains outside this sufficient class.
The next structural boundary is explicit: inconsistent multiplicative gain
cycles or genuinely multi-coordinate rows cannot be handled by this network
recognizer. Small direction dictionaries and network normal matrices are now
two distinct direct-routing criteria rather than one required representation.

## Primary reference

Borgwardt, Finhold, Hemmecke, arXiv:1408.4184, Theorem1.1, Sections2--3:
https://arxiv.org/html/1408.4184
DOI:10.1007/s10107-015-0956-4. The classical proof and its combinatorial/circuit
bounds are kept distinct; no circuit-diameter result is used as an edge bound.
