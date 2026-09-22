# Three exceptional target rows: a quadratic original-row route bound

## Statement and what is not assumed

Let P be both conv(C), for a finite real family C in ambient dimension d, and
its ORIGINAL m linear halfspaces. The endpoints u,v are actual extreme points.
Let B contain at most three original row labels. Every row tight at v outside
B takes its boundary value and at most one other value on all actual vertices.
Exceptional and non-target rows may take arbitrarily many values.

The theorem constructs an original ordinary-edge route with

    L <= (m-d)+m*m.

Every visited point is an actual original vertex. Each successive pair is
nondegenerate and its WHOLE segment is an IsExtreme subset of the original P.
Every target row already acquired remains tight, including exceptional rows.
Residual steps are not required to acquire a new target label.

The public hypotheses contain no supplied graph, active basis, residual rank,
small vertex catalogue, incidence bound or cheap finishing route. Exact H/hull
equality, endpoint extremality, at most three exceptional labels and the other
target rows' two-level structure remain explicit structural premises. Redundant
rows and generators, nonsimple/lower-dimensional bodies, empty B, non-target
exceptions, dimension zero and equal endpoints are included. Natural subtraction
is the same m-d used in the accepted prefix theorem; actual vertex extremality
implies d<=m. m counts displayed original inequalities, not a separately proved
irredundant facet lattice.

## 1. The accepted prefix and residual geometry

Reuse accepted #325/#327 geometry. The good-row entry walk acquires every missing
two-level target row with a genuine original edge. A chosen good row cannot
improve to an intermediate vertex value because it has only two levels. All
previously acquired target rows remain locked. The prefix costs at most m-d.

Let N be the common kernel of all good target equations. Evaluation on B is
injective on N, because a motion vanishing on both good and exceptional target
rows vanishes on every row active at the actual target. The accepted active-kernel
theorem makes it zero. Therefore dim(N)<=|B|<=3 is DERIVED, not a public premise.
All differences of residual vertices lie in N.

## 2. Transfer an original row slice to an ambient planar subspace

Fix an original row whose restriction f to N is nonzero. Its kernel inside N is
proper and hence has dimension at most two. The ambient subspace

    M = N intersect ker(A_i)

injects linearly into ker(f), by the explicit nested-subtype identity map. This
proves dim(M)<=2 without assuming a chosen coordinate chart, basis or rank.
Differences of residual vertices satisfying A_i(x)=b_i belong to M. They remain
actual extreme points of ORIGINAL P, rather than new vertices of a projection.

Apply the accepted planar_vertex_card theorem to that finite slice, the SAME
original inequalities A,b, and M. The slice contains at most m+1 actual vertices.
This is the critical change from #327: a three-dimensional row slice need not
have at most two vertices, but it does have the proved planar original-row bound.
No two-per-row cap is silently reused in dimension three.

## 3. Spatial incidence count

If dim(N)<=2, the accepted planar theorem already gives |V|<=m+1. Since m<=m*m
for natural m, this implies |V|<=m*m+1, including m=0.

Otherwise dim(N)=3. Keep only original rows whose restrictions to N are NONZERO.
At every actual residual vertex, evaluation on its active nonzero restrictions
is injective on N, by the accepted active-kernel theorem. Thus at least three
such original labels are incident. Double-count the actual pairs (vertex,row):

    3 |V| <= sum of row-slice vertex counts
           <= (# nonzero original rows)(m+1)
           <= m(m+1).

The elementary natural-number estimate gives |V|<=m*m+1. Both incidence tables
use the same nonzero-restriction condition, so rows that are identically zero on
N and may contain the entire residual face do not invalidate the upper count.
No possible-basis enumeration or optional-label encoding is used.

## 4. Construct the suffix and assemble the route

Strictly expose the actual target using the already accepted finite-hull
separator. The accepted improving-edge construction operates inside each current
target-lock face, improving that same objective and preserving all acquired rows.
Induction on the number of residual vertices with larger objective produces the
ENTIRE suffix, with length+1<=|V|. The new count bounds its length by m*m. Append
it to the proved good-row prefix to obtain (m-d)+m*m.

The route need not be shortest or all-facet nonrevisiting. Only the residual
suffix uses one strictly improving objective; no global monotonicity assertion
for the prefix-plus-suffix is added. The concrete rational test producer uses a
sum of target rows as its residual objective, not an executable-identical copy
of the formal noncomputable strict separator.

## Relation to the mission and prior results

For |B|=3, accepted #325 gives (m-d)+((m+1)^3-1). This packet gives a QUADRATIC
bound in the same original row count. #327 and #324 remain sharper for at most
two and at most one exception, respectively. This is not a best-known classical
three-dimensional diameter claim or a historical-priority claim. It formalizes
a compositional bound from the currently accepted incidence tools, without
introducing a boundary graph or Euler-characteristic theorem as an assumption.

The exception count is still bounded by three. This does NOT establish uniform
Polynomial Hirsch for arbitrary carriers. A recursive slice argument in larger
dimensions still raises the degree; merely repeating it is not a uniform-degree
solution. The independently owned affine-roof work #326 is not used or modified.

## Source and verification boundaries

The first 1218 lines / 51946 bytes copy the accepted #327 namespace prefix
BYTE-FOR-BYTE. Its old public solution and old axiom-print requests are omitted,
not resubmitted. New code supplies the spatial slice transport, incidence bound,
residual bound and route assembly. The new public solution matches problem.json
exactly and uses only Mathlib types in the target statement. Seven final axiom
reports are requested, including the accepted planar helper and full new root.
A requested report is not itself a passing audit.

Local Lean/Lake/Elan and checked cached installations are unavailable; release
and raw-host DNS lookups returned no addresses. No local Lean compile is claimed.
The complete candidate is prepared for one ordinary pinned compiler/axiom gate
and publication only after that gate passes. Preserve any failed source and
actual diagnostics; do not use repeated speculative Actions runs as a compiler.
Keep Lean4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.7,
all duplicate guards, and verifier/publisher credential isolation unchanged.

## Executed supporting computations

The new exact-rational suite checks complete motion kernels, active-restriction
rank, full vertex/row incidence tables, and a second planar table for every
nonzero residual row slice. It reconstructs these against an exhaustive SMALL
hull reference. Every delivered edge is checked as a whole supporting slice in
the current locked face and as an original edge. The route producer does not
read the reference edge table. Serialized JSON certificates and routes replay
with certificate, edge and route construction disabled.

The full suite covers 23 hulls, 163 vertices and 175 displayed original rows.
150 targets qualify, including 16 targets with three intrinsically exceptional
rows, and 13 targets are rejected. Its 271 certificates have dimensions 0/1/2/3
in counts 106/11/65/89. There are 542 checked nonzero row slices containing MORE
than two residual vertices. All 2411 routes and 3810 original-edge occurrences
pass; total shortest distance is 3736, and all 42 nonshortest routes and 124
nonacquiring steps are retained. Eleven malformed controls are rejected.

These are supporting computations, not Lean-extracted code, a verified JSON
parser, a large-graph enumeration, an H-to-V complexity bound, or an all-real
proof by finite sampling. The exact full report, fixtures and reproducible script
accompany the evidence; conclusions are not inferred from summary counts alone.
