# One charge per original target row

## Exact public result

Let P be both the convex hull of a finite real family C in ambient dimension d
and the set defined by the ORIGINAL m inequalities A_i x <= b_i. Let u,v be
actual extreme points. Let V be the actual extreme points selected from C, and
T the original labels tight at v but not at u. For each original label i, write
S_i = {A_i x : x in V} for its set of DISTINCT actual vertex values.

The theorem constructs a route through actual original vertices with

    L <= sum_(i in T) (|S_i|-1).

Each consecutive pair is distinct and its ENTIRE segment is an IsExtreme subset
of original P. Every target row already acquired remains tight at every step.
For the SAME constructed length and path, it also proves

    (all target-tight i satisfy |S_i| <= K+1)  =>  L <= K*(m-d)

for every natural K. No limit is imposed on the number of target rows having
more than two levels. Non-target row inventories are unrestricted.

The public vertex filter is derived from C using Mathlib extremality. Every
actual vertex of a finite hull belongs to C; the proof neither takes a complete
vertex catalogue as an extra premise nor counts redundant/interior generators
as vertices. Exact H/hull equality and endpoint extremality are explicit.
Redundant inequalities, nonsimple/lower-dimensional bodies, dimension zero,
equal endpoints, K=0 and constant target rows are not discarded.

This is not a uniform Polynomial Hirsch theorem. The first inequality is a
weighted LEVEL bound whose numerical value can be exponential in original m.
The second has a bounded-level structural antecedent; it does not assert that
all polytope carriers have small K. The result bounds original edges rather
than auxiliary graph steps, but does not prove efficient vertex enumeration,
shortestness, all-facet nonrevisiting or one global monotone objective.

## 1. Construct a full acquisition phase

Fix any original row j tight at target v. At an actual vertex x not on that
boundary, feasibility gives A_j x < A_j v. The accepted improving-edge geometry
constructs an ORIGINAL edge to a better actual vertex y while retaining all
currently acquired target rows. This is actual whole-face geometry, not a
supplied neighbor graph, improving-edge witness or one-step-acquisition oracle.

Unlike the two-level argument, improvement may stop at an intermediate value.
Define above(x) = {a in S_j : A_j x < a}. The new actual value A_j y belongs to
above(x) but not above(y), and strict improvement gives above(y) strictly inside
above(x). Strong induction on this finite cardinality constructs the ENTIRE
phase until the row boundary is attained. The number of phase edges is at most
|above(x)| <= |S_j|-1. No lower bound on numerical progress is used. Arbitrarily
small positive gaps, many vertices at one value and intermediate steps acquiring
no target row are all permitted.

Route operations and the one-step lock property prove that every target row
locked before the phase remains locked at its endpoint. This preservation is
proved along all intermediate steps, not merely asserted for phase endpoints.

## 2. Charge each original label once

Let M(x) be the original target labels missing at x, and let

    B(x) = sum_(i in M(x)) (|S_i|-1).

If j is selected from M(x) and its constructed phase ends at y, then
M(y) is contained in M(x) with j erased: no previously tight target row becomes
missing, and j has just been acquired. Because all weights are nonnegative,

    B(y) + (|S_j|-1) <= B(x).

Other labels incidentally acquired by the phase disappear for free. The argument
therefore prevents repeated charging even when different rows have different
level counts. It does not assume that the sum of all row ranks decreases on each
individual edge; other unfinished row values may move in either direction.

If x differs from v, at least one target label is missing. Otherwise the accepted
active-kernel theorem forces x=v from equality on all target-active rows. Strong
induction on |M(x)| selects j, constructs the full phase, recursively constructs
the remaining route, and appends them. The two length bounds and budget inequality
give L <= B(u). No already-short phase or path is used as a premise.

## 3. Original input-size corollary

When every target-tight row has at most K+1 actual values, each weight is at most
K, so B(u) <= K*|T|. Missing target labels are disjoint from all source-active
labels. The accepted finite opposite-perturbation argument makes active-row
evaluation injective at the actual source vertex; hence at least d ORIGINAL
rows are active there, even in the nonsimple/lower-dimensional cases. Therefore
|T| <= m-d and L <= K*(m-d).

At K=1 this recovers the earlier two-level length bound, but the new public
result allows any number of genuinely multilevel target rows when K>=2. It
also gives heterogeneous weights without choosing one common K. It does not
supersede #324's arbitrary-inventory one-exception bound, #327/#328's incidence
bounds or the independent-roof construction; those use different structure.

## 4. A growing multilevel class, not a fixed exception count

The supporting application uses products of the rational hexagon with vertices
(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1). Take source (0,0) and target (2,2) in each
factor. Both target rows have exactly three vertex values, so K=2. In r factors,
there are 2r dimensions, 6r displayed original inequalities and 2r target rows
with more than two levels. Thus the number of multilevel rows grows with the
ambient dimension instead of being bounded by one, two or three.

The written Cartesian-product argument gives the full H/hull equality, vertex
product classification and retained local row-value sets. The weighted budget
is 4r, and the generic input-size corollary is 8r. The explicit tested block route
has 3r original edges. In dimension64 this is 192 original inequalities,
64 multilevel target rows, weighted budget128, corollary bound256, and a checked
96-edge route. This example is not a best-diameter or historical novelty claim.
Its product classification/application is written mathematics supported by exact
certificates, NOT an additional Lean instance theorem in this packet. The entire
large product graph and vertex set are not enumerated.

## Formal source, reuse and scope of execution

The retained 778-line/31854-byte prefix comes from accepted #328: Route operations,
original finite-hull improving-edge geometry, original active-row facts, Edge,
and improve_locked. Their proof bodies are BYTE-IDENTICAL. Unused later accepted
blocks and public roots are omitted, and the retained namespace is closed before
new TargetLevels code. No accepted target is resubmitted or imported as its own
proof. The new top-level solution has exactly the target's Mathlib-only public
type, with explicit classical finite filters and an imports/open/options preamble.
Seven transitive reports are requested. Requested reports are not passing audits.

Local lean/lake/elan and checked installations/caches were unavailable; fresh
release/raw-host DNS lookups returned no addresses. No local Lean compilation is
claimed. This complete packet is prepared for ONE normal final pinned compiler,
transitive-axiom and publication gate. Preserve any failure and further repair
separately instead of speculative repeated hosted editing or weaker assumptions.
Lean4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.7 and all
verifier/publisher credential-isolation and duplicate safeguards remain unchanged.

The mathematics composes classical finite objective ascent with target-face
locking; no historical-priority or new best general diameter claim is made.
The mission's arbitrary-carrier original-input polynomial bound remains separate.

## Executed tests and reproducibility

The new exact-rational small suite independently reconstructs original H hulls,
actual vertices, row levels and edge support slices. Every phase's strict values,
endpoint, target locks and unique charged label are checked. Serialized records
replay with route and edge production disabled. The route producer never reads
the independent reference edge graph. The 17-model suite has 601 routes and685
original-edge occurrences, versus684 shortest-edge total; its one nonshortest
route remains recorded. It retains37 multi-edge phases and18 steps acquiring no
new target row. Thirteen targets have more than three multilevel target rows,
with a maximum of eight in small cases. Eight malformed controls are rejected.

Four product cases in dimensions8/16/32/64 check180 further original edges. The
product consumer verifies that one changing block has the complete exposed edge
slice, every stationary block has a singleton slice, and the total common-row
rank is d-1. Full product graphs are not enumerated. A clean FOUR-script workspace
reproduces all FIVE complete reports/fixtures/control outputs byte-for-byte.

These are supporting computations, not Lean-extracted Python, a verified JSON
parser, a polynomial-time H-to-V algorithm or an all-real proof by finite sampling.
Full raw outputs accompany the export and regenerate; any repository summaries
are labelled derived rather than substituted for the complete fixtures.
