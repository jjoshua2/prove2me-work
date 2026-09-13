# Controlled portal detours and bounded-additive-spill accounting

## Contribution, provenance, and verification boundary

This continues the all-available-row mass argument in draft #206 without
modifying that branch. The baseline read from main is
`321f473d871aad2d692595acd97a667d6a648d06`. A concurrent #207 appeared before this handoff. The final near-geodesic bridge
reuses its positional-window proof and #206's geometric interfaces rather than
duplicating the shared file name. Both prerequisites must be integrated. The two
cross-level accounting modules depend only on each other and the established
`PolynomialRegionRouting` module on main. No workflow, pin, credential or
platform record is changed.

There are three substantive results:

1. Allowing k extra region transitions changes the all-row incidence factor
   from three to k+3, even when the walk revisits labels. The count is over
   actual occurrences, so repeated charges are not hidden by deduplication.
2. Exact rational examples show that forcing a shortest region walk can
   obstruct resource-conserving portal choices. One extra transition repairs
   the obstruction in a 4D, 12-facet example, with all portals optimized.
3. Cross-level accounting tolerates a FIXED ADDITIVE sibling excess allowance
   b at every split. It is not necessary to conserve unshifted excess exactly:
   shifting each large child's excess by b yields a conserved quantity and an
   explicit polynomial route bound.

The four Lean files (375 lines, 11 axiom printouts) are new proof candidates,
not locally compiled or accepted platform theorems. The written mathematical
arguments and the exact finite tests have the scope stated below. Neither a
universal bounded-spill decomposition nor Polynomial Hirsch is claimed.

## 1. Near-geodesic contact windows count occurrences

Let p_0,...,p_L be a walk in a simple undirected graph G, with

    L <= dist(p_0,p_L)+k.

A vertex z contacts position j when z=p_j or z is adjacent to p_j. If z
contacts r<=s, replace the subwalk between those positions by the walk through
z, of length at most two. The resulting endpoint walk has length at most
r+2+L-s. Comparing with the endpoint distance gives

    s-r <= k+2.

All contact POSITIONS therefore lie in one window of at most k+3 indices.
No simplicity or no-revisit assumption on p is necessary. This remains true
when z appears on p several times: each occurrence costs index length.

The bound is sharp for every integer k>=0. Take vertices 0,1,2,3 and edges
01,12,03,13,23. The endpoints 0 and 2 have distance two. Between them insert
an alternating string 1,3,1,3,... of length k+1. The walk has k+2 edges and
vertex 3 contacts all k+3 positions, counting its own repeated appearances.

This is the correct extension of #206's factor three. A proof that counts
only distinct visited cut labels would lose the costs of repeated portal
pairs and would not justify the next theorem.

### The geometric resource bound survives controlled detours

Use the same mixed-region graph as the preceding clipping work. Available
original cut rows are indexed injectively by a set A of cardinality s. Let r
be the number of selected cut OCCURRENCES on the walk. At occurrence i, let
C_i be the smallest face containing its actual entry/exit parent vertices,
let delta_i be C_i's minimum intrinsic presentation excess, and let t_i count
all available labels equal or adjacent to its current label.

The strict-row saving proof is pointwise and never needed geodesicity:
noncontact row faces are disjoint from the current face, hence their rows are
strict throughout C_i. With parent excess e=n-d it gives

    delta_i+s <= e+t_i.

Every available label contributes to at most k+3 occurrence positions. Thus

    sum_i t_i <= (k+3)s,
    sum_i delta_i+r*s <= r*e+(k+3)s.                 (1)

At full availability s=e,

    sum_i delta_i <= (k+3)e.                        (2)

An available row can be charged again at a repeated occurrence, but there can
be at most k+3 such contacts at this level. The near-geodesic Lean module
expresses contacts as a finite set of natural-number POSITIONS. The bridge reuses the independently developed graph theorem in #207.
The geometric module allows a position set and separate actual vertex pair at each position.
It does not presume that one label has only one pair.

Routes along an arbitrary finite region walk still concatenate. The existing
private walk-level deferred assembler already uses this fact before the public
theorem chooses a geodesic. New walks can be represented directly by their
occurrence list; one must not pretend that a nongeodesic walk inhabits the old
`DeferredClipCertificate` record with its shortestness field unchanged.

For actual carrier dimensions h_i<=H, the established inequalities
h_i<=delta_i and M_i<=2delta_i, plus intrinsic Larman, give

    ordinary-edge cost <= D+2(k+3)e*2^max(H-3,0).    (3)

Equation (3) is a mathematical consequence, not a new full clipping-adapter
Lean declaration in this packet. The existing closed/extreme-face and
injective-row hypotheses are retained in the formal pointwise mass theorem.

## 2. A precise finite repair family and what the counterexamples refute

The experiments use bounded full-dimensional SIMPLE rational polytopes with
irredundant facet descriptions. Inside the smallest face F of the requested
endpoints u,v, take an actual edge u--w. Exactly one facet of F not containing
u is entered at w. Its label is the first available region. Available labels
are ALL facets of F not containing u, exactly e_F of them. The final label is
any available facet containing v. Two labels are adjacent when they share a
vertex of F. Each overlap portal can be ANY such vertex.

The walk horizon is the shortest label distance from the chosen first region
to a target-containing region, plus k. Optimization considers all choices of
actual first edge, all walks within that horizon, and all overlap portals.
Every consecutive pair charged inside one available facet has smallest common
face of dimension strictly less than dim F. These are actual proper-face
subproblems, not circuit moves.

This is an explicit and natural first-edge/facet-cover family, NOT a claim to
enumerate every radial trace, cap, center and endpoint lift allowed by #206.
The negative results below refute resource-conservation assertions for shortest
walks in this family. They do not prove that every possible #206 certificate
on the same polytope has the same failure.

### Exact defining inequalities

For n=10 or 12, put v_i=(i,i^2,i^3,i^4), 0<=i<n, and let mu be their mean.
The examples are

    P_n = {x in R^4 : (v_i-mu) dot x <= 1 for every i}.

The origin is strictly feasible. All-ones positive normal balance and full
normal rank certify boundedness. The checker exhausts all choices of four
active rows using rational Gaussian elimination, checks every inequality, and
checks all vertices are simple and every row is a genuine facet. No remembered
combinatorics of cyclic polytopes is used as enumeration evidence.

For P_10 choose endpoints by active sets {4,5,6,7} and {0,1,2,9}.
For P_12 use {7,8,9,10} and {1,2,3,4}. These row sets identify unique vertices.

| Exact minimum over the specified repair family | k=0 | k=1 | k=2 |
|---|---:|---:|---:|
| P_10, sum of child excesses, parent e=6 | 7 | 5 | 4 |
| P_10, sum of child dimension*excess | 19 | 9 | 4 |
| P_12, sum of child excesses, parent e=8 | 16 | 10 | 7 |
| P_12, sum of child dimension*excess | 32 | 26 | 13 |

The mass and potential rows optimize different objectives; they are not
claimed to be attained simultaneously by the same portal choices. Each
strict-geodesic first-edge/final-facet combination (16 in each example) has
the corresponding displayed k=0 minima. These results are checked by a
separate exhaustive LABEL-WALK enumeration with a separate portal-chain DP,
not merely by trusting the optimizing routine's returned value.

P_10 has 35 vertices; P_12 has 54. Their endpoint graph distances, computed
independently, are five and six. On P_12, unshifted sibling mass conservation
fails for k=0 and k=1, and fixed allowance b=2 or b=3 fails at k=0. The potential
h*e=32 is also insufficient for the k=0 node: one first edge plus minimum child
potential is 33. One extra label transition admits an entire ZERO-CHARGE
recursive certificate with six actual edges. Two extra transitions can
conserve even the unshifted root excess, but are not needed for the new
additive-allowance certificate.

**Crucial distinction:** strict-region lookahead can ALSO assemble six actual
edges, but its resulting potential certificate has positive total charge nine.
The detour is necessary for these local accounting conditions, not necessary
for a six-edge route. Likewise greedy minimum local potential gives actual
lengths 7,7,8 at k=0,1,2 on P_12. More freedom cannot worsen the optimum of the
SAME objective; it can change a greedy plan in a way that worsens a different
objective. The implementation therefore includes whole-recursion lookahead,
not a claim that locally minimizing h*e minimizes graph distance.

## 3. First cross-level certificate: exact potential charges

For a parent of intrinsic dimension h and excess e, set Phi=h*e. A finite
repair node carries one actual first edge and a sequence of child routes,
each in a proper face, with parameters h_i,e_i. Define its local charge by

    q = max(0, 1+sum_i h_i*e_i-h*e).

Terminal leaves are stationary or actual edges. Induction and concatenation
prove both a genuine ordinary-edge walk and

    route length <= h_root*e_root + sum_nodes q.    (4)

This never credits a repeated child for free. Memoization avoids recomputing
its certificate, but every occurrence is included again in cost and charge.
The generic `PortalRepair` inductive predicate contains actual edges and child
certificates, not an unproved high-dimensional distance premise.

If all charges vanish, (4) gives h*e. Exact sibling mass conservation is one
sufficient condition: with h_i<h, e>=1 and sum e_i<=e,

    1+sum h_i*e_i <= 1+(h-1)e <= he.

But some conserving potential nodes may have sum e_i>e. Conversely #206's
factor-three mass bound alone does not bound the cumulative charge in (4).
A universal existence claim for zero-charge trees is not made here.

## 4. Stronger accounting: fixed additive spill is affordable at EVERY level

The next theorem does not require zero charge for h*e or exact unshifted mass
conservation. Fix a nonnegative allowance b and a small-leaf rate C. Assume a
finite geometric repair tree has the following properties:

- At every internal node e>b, one ordinary first edge is charged.
- Every child has h_i<h and e_i<=e, with sum e_i<=e+b.
- At e<=b stop, using an actual leaf route of length at most C*e.

The dimension drop is automatic when actual child pairs lie in proper facets.
Minimum intrinsic excess is nonincreasing on faces: a codimension-c face lies
in at least c independent parent facets, so its minimum number of describing
facets is at most M-c; subtracting its dimension h-c gives e_child<=M-h=e.
This argument applies to intrinsic irredundant presentations, not arbitrary
padded row counts chosen independently at different nodes.

The nontrivial condition remains **finding portals with sibling sum<=e+b**.
It is checked on each generated example but is NOT established for arbitrary
polytopes or for arbitrary geometrically possible repairs.

### Shifted mass conservation

Write mu(e)=(e-b)_+. Then

    sum_i mu(e_i) <= mu(e).                         (5)

If no child exceeds b, the left side is zero. If exactly one does, use that
child's e_i<=e. If at least two do, subtract b for EACH large child:

    sum_large (e_i-b) <= (e+b)-2b = e-b.

This is why fixed additive spill behaves differently from a fixed
multiplicative factor. The allowance is paid when branching occurs. A unary
chain may retain e unchanged, but its dimension must strictly decrease.

### Count internal nodes, then actual edges

The positive integer mass on the large-node skeleton is conserved. At each
level there are at most mu(e_root) internal nodes, and strict dimension drops
allow at most h_root levels. Hence

    N_internal <= h_root*(e_root-b)_+.

Summing all local sibling inequalities and canceling internal masses gives

    total small-leaf excess <= e_root+b*N_internal.

One first edge per internal node and C times the leaf excess now give

    length <= N_internal+C*(e_root+b*N_internal),
    length <= C*e_root+(1+b*C)*h_root*(e_root-b)_+.  (6)

A direct recurrence proof of (6), rather than an informal tree count, is in
`PolynomialAdditiveAllowanceRouting.lean`. The inductive certificate records
actual leaf routes, actual first edges and all local numerical conditions.
It returns BOTH the assembled route and its polynomial bound.

For b=1,2,3, the established small-excess theorem permits C=1. For example,

    b=2:  length <= e+3h*(e-2)_+,
    b=3:  length <= e+4h*(e-3)_+.

For fixed b>=4 a safe rate is C=2*2^(b-3), by h_leaf<=e_leaf,
M_leaf<=2e_leaf and intrinsic Larman. Formula (6) is quadratic in h,e for
fixed b,C. It handles repeated additive spill and nondecreasing excess along
unary chains; it does not merely repackage a requested GLOBAL cost bound.

Both local conditions in (5) matter. A single child of excess e+b violates
shifted conservation without child monotonicity. Two almost-parent-excess
children violate it when the sibling allowance is removed. The regression
checks these negative cases explicitly.

### The six-edge example really uses the new rule

With b=2 and k=1, the P_12 certificate has root parameters (h,e)=(4,8), child
mass total ten, three internal nodes, and total small-leaf excess three. It
contains large descendants with (h,e)=(3,8) and (2,8): excess does not decrease,
but dimension does. Every node's sibling budget and every supplied ordinary
edge is independently checked. Its actual length is six; the general safe
bound (6) is 80. No optimality of that constant is claimed.

Ten additive-allowance certificates pass on the test suite, including a
six-dimensional, 12-facet polytope with 112 vertices and an actual six-edge
route. This is not restricted to cube graphs. The examples also include a
product of hexagons, a truncated-octahedron/permutahedron model, and generic
rational polar systems. Finite success does not establish a uniform b.

## 5. Exact algorithms and independent verification

The main optimizer first validates exact rational H-data, a strict point,
a strictly positive normal balance and full rank. It then COMPLETELY enumerates
active bases. A cap is checked before enumeration; an oversized problem is
rejected rather than treating partial enumeration as the full vertex set.
The CLI requires a simple irredundant facet description. Nonsimple inputs are
rejected, not silently perturbed. The graph/arithmetical theorems are broader
than this numerical implementation.

For a fixed first region, the basic DP state is

    (remaining occurrence slots, current cut label, entry vertex).

Transitions choose the next label and a real overlap portal. Repeated labels
are allowed; the remaining horizon strictly decreases. Objectives are total
carrier excess, total h*e, or recursively computed actual cost. A second DP
adds remaining potential budget for zero-charge lookahead. The additive-spill
solver instead adds remaining sibling excess budget e+b and terminates small
leaves with explicit intrinsic-face walks.

All recursive calls decrease ACTUAL common-face dimension. The memoized
subproblem includes ordered endpoints, permitted slack, and policy/allowance
where appropriate. Reuse is computational only: concatenation charges the
returned walk separately at every occurrence. The independent verifiers do
not invoke optimization. They reconstruct the parent/child faces from all
original inequalities, validate every portal, recompute ranks and local mass,
and check the entire returned edge walk.

This is an exact finite search and proof-producing diagnostic in the explicit
vertex/incidence model. The H-to-vertex conversion is exponential in general.
DP complexity is polynomial in the explicit state-space sizes and integer
horizon/budget, not a strongly polynomial LP or a polynomial H-description
routing algorithm. Once the complete graph is given, ordinary BFS already
finds its distances; the point here is to test recursive geometric CONDITIONS
and emit independently checkable cross-level certificates, not beat BFS.

## 6. Tests actually executed and formalization boundary

The executable suite checked ten complete rational descriptions: 4,538 active
bases, 460 vertices, 1,020 ordinary edges and 27,458 ordered graph-pair distances.
The separate label-walk optimality audit checks 2,880 walks for the two focused
examples. The primary tree suite verifies 79 routes, 293 actual-edge occurrences
and 163 internal-node occurrences. Ten additional additive-spill routes add 55
edges and 30 internal-node occurrences. Thus there are 89 verified route
certificates and 348 charged edge occurrences across the two suites.

Graph-window checks cover all 75 simple labeled graphs through four vertices,
14,137 finite walks of at most five edges, 12,854 of them with repeated labels,
and 56,139 vertex/position windows. Sharpness examples cover k=0,...,12.
Numerical arithmetic regression covers 42,095 shifted-mass cases and 487,908
polynomial recurrence cases. Twenty-five malformed or forged inputs are
rejected. Separate valid-input failures record the lack of an admitted
zero-charge/additive certificate at k=0 for P_12; these are not invalid-input
or diameter claims.

Four new Lean modules supply 11 printed declarations: near-geodesic positional
windows, geometric occurrence-mass bounds, finite charge-telescoping route
certificates, and the shifted-excess additive-allowance polynomial theorem.
They have not been compiled here. The complete polytope-to-JSON extraction,
optimality audit, and construction of a geometric tree satisfying the new
local conditions are NOT a fully formalized end-to-end Lean existence theorem.
The generic Lean route trees are numerical/relational certificate structures;
the exact Python verifier and this argument bind their labels to actual
intrinsic faces in the examples. Do not confuse an arbitrary mass tag with a
certified geometric excess.

No result is newly accepted on Prove2Me. Keep the existing small-excess/Larman
inputs explicit when building public wrappers; no open ancestor is imported
as an axiom. The source hashes and actual execution counts are in the committed
compact receipt. The full receipt and generated input/optimality/route fixtures
are in the conversation package and are regenerated by the test script.

## 7. The remaining question

#206 now has a controlled-detour extension, but (k+3)e at a node still need not
be e+b with fixed b. What is missing is a geometric selection theorem that
chooses portals and proper-face repairs with bounded additive spill (or another
explicitly amortizable local rule). This work establishes why that weaker-than-
exact-conservation local target is sufficient, and why insisting on shortest
region paths can block it even when short actual routes exist.

It is not established that k=1 and b=2 work for all simple polytopes. It is not
established that universal near-geodesic bounded-spill trees exist at all.
The next research should test and prove the portal-selection rule, not add a
cosmetic root dependency or claim that the conditional polynomial recurrence
already proves Polynomial Hirsch.
