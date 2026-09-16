# Cut-stable direction covers and certified original-edge routes

## 1. Scope and connection to the current frontier

This continuation starts from main `dbfd755ef4b6b2eb272c0cb70f888bf78741b5ec`
after #269. It preserves the full-stellar-size obstruction in #267, the general
fixed-budget search in #268, and the positive endpoint-transfer class in #269.
No prior source, accepted theorem, pin, workflow, secret, or pending submission
is changed. This is written mathematical research and exact software, **not**
a Lean/Prove2Me verdict or a solution of Polynomial Hirsch.

The distinct step is stability under **arbitrary added halfspaces**. A cut can
create directions not present in the coordinate-simplex sum and invalidate
#269's direct summand-transfer description. We prove an explicit cover for
these new directions. More strongly, the exponent can depend on certified
LOCAL CUT OVERLAP, rather than the total number of added inequalities.

The classical input is the edge-direction/zonotope-refinement diameter theorem
of Blanchard--De Loera--Louveaux, Theorem 1.3, with the Gritzmann--Sturmfels
normal-fan observation recalled as Lemma 2.5. That theorem and the elementary
hyperplane-arrangement path are attributed, not claimed new. Here the specific
cut-closure count, independently checked overlap interface, and actual original-H
path implementation are developed explicitly. No historical-priority claim is
made for every equivalent form of the cut corollary.

## 2. General cut-direction closure

Let P be a nonempty compact polytope in a finite-dimensional affine space. Let
D be a finite collection of N nonzero, pairwise nonparallel vectors containing
the direction of EVERY edge of P. This is a genuine hypothesis, not a conclusion
from a few observed edges. Let

    Q = P intersect {x : a_i(x) <= b_i, i=1,...,s}

be nonempty. Cuts can be nongeneric, redundant, parallel, or meet at nonsimple
vertices. Q may be lower-dimensional. Let k be the number of distinct NONZERO
cut-normal lines. Opposite normals count as the same line for this calculation.

For each independent r-element subset J of D and each (r-1)-element subset I
of the cut-normal lines, retain

    span(D_J) intersect intersection_{i in I} ker(a_i)

whenever it is one-dimensional. Choose a normalized generator of each resulting
line and remove duplicate lines. For r=1 and I empty this includes the old D.
Only 1 <= r <= min(dim P,N,k+1) need be considered. Call the resulting set E.

**Cut-closure theorem.** E contains every edge direction of Q. Consequently

    |E| <= sum_r binom(N,r) binom(k,r-1) <= binom(N+k,k+1).       (2.1)

The last equality for the untruncated sum is Vandermonde's identity. This is a
COVER: some candidates need not be realized by any edge of Q. It is not an
assertion that all candidate directions actually occur.

### Proof, including degeneracies

Take a relative-interior point x of an edge e of Q. Let F be the unique minimal
face of P containing x, of dimension r. Since x lies in the relative interior
of F, all constraints of P not defining F are locally strict. In a neighborhood
of x the direction space of the minimal face of Q is therefore

    lin(F) intersect intersection_{i active at x} ker(a_i).

It is exactly the one-dimensional direction of e. Thus the active cut normals
restricted to lin(F) have rank r-1. In particular r-1 <= k. Choose r-1 of them
with independent restrictions; parallel normals cannot both be needed.

Edges of a polytope span its affine direction space, so r independent edge
directions of F can be chosen from D. Their span is lin(F). Together with the
chosen cut normals they generate exactly the direction of e in the construction
of E. This proves coverage. No simple basis at x, transversal cut, or assumed
edge of a higher-dimensional extension is used.

The r<=k+1 cutoff is necessary for this argument. In [0,1]^(k+1), add
x_i+x_(i+1)<=1, i=1,...,k. The segment between the two alternating zero/one
vertices has the k independent new rows in common, so it is an original edge
of Q. Its midpoint is strictly interior to the whole base cube, and its direction
has all k+1 coordinates nonzero. No span of just k coordinate directions covers
it. This proves necessity of the allowance in all k, not merely at one test size.

### Why simultaneous closure matters

Applying a one-cut quadratic direction estimate repeatedly can produce a crude
N^(2^k) expression. Looking at the ORIGINAL base face instead gives exponent
k+1. This is a direct simultaneous rank calculation, not an iterative genericity
assumption. For fixed k it remains polynomial in N, independently of the cut
coefficients or offsets. It is not polynomial for unrestricted k.

## 3. Local overlap replaces the total-cut exponent

Suppose every point of Q is on at most q of the added boundary rows. Equivalently,
for every subset I of q+1 added rows,

    Q intersect {a_i(x)=b_i for all i in I} = empty.             (3.1)

Then the same proof has r-1<=q. Keeping k distinct cut-normal lines gives

    |E_q| <= B_q(N,k)
           := sum_{r=1}^{min(dim P,N,k+1,q+1)}
                  binom(N,r) binom(k,r-1).                     (3.2)

In particular, if the added boundary faces are pairwise disjoint,

    |E_1| <= N + k*binom(N,2),                                 (3.3)

even when k grows with dimension or the number of facets. A pointwise overlap
bound is sufficient, not necessary: a stronger implementation could certify
only positive-dimensional intersections. That refinement is NOT implemented.

### The supplied q is verified from the actual original inequalities

The constructor does not assume (3.1). For each required I it finds a
nonnegative combination of the FINAL original H-rows certifying

    sum_{i in I} a_i(x) <= c_I < sum_{i in I} b_i,  x in Q.      (3.4)

All slacks b_i-a_i(x) are nonnegative. Their sum vanishes exactly when all
selected boundaries are tight, so (3.4) excludes precisely the needed joint
equality. The positive multipliers and strict gap are checked independently.
Missing one required subset rejects the alleged overlap certificate. If a
selected intersection is nonempty, the requested q is rejected; no low-overlap
bound or negative routing result is reported.

There are binom(s,q+1) such tests, polynomial in s for FIXED q. In the box case,
the support of the base box often supplies a direct dual; otherwise discovery
solves the objective over Q with the existing exact LP. Redundant parallel rows
can make (3.1) fail unnecessarily; the unconditional k-normal-line mode still
works. No empty overlap list is accepted as proof of a nontrivial bound.

The proof (3.4) concerns the actual intersection polytope, not an uncut base
facet graph, a random vertex sample, or an assumed list of original facets.

## 4. From the finite cover to actual short paths

Classically a polytope with an N-direction edge cover has monotone diameter at
most N: the zonotope generated by the cover refines its normal fan. For this
project we use the following direct objective-line construction and original-H
audit rather than projecting an arbitrary extension edge.

For requested vertices u,v of Q, first retain their minimal common face F.
For a complete H-description this is obtained by taking the rows tight at BOTH
endpoints and adding their reversed inequalities. Equivalently these are the
rows tight at the midpoint, because all endpoint slacks are nonnegative. This
is a face of Q; its edges are original Q-edges and create no new directions.
Thus the extra equality rows used internally are NOT charged as new cuts in
(2.1) or (3.2). All common original faces are preserved by the resulting route.

Choose objectives f,h strictly exposing u,v in F, with nonzero evaluation on
all E_q, and such that distinct lines have distinct zeros along (1-t)f+t*h in
0<t<1. These conditions can be met inside the open endpoint normal cones.
Here is a finite deterministic construction rather than an assumed oracle:
choose d independent tight rows at each endpoint of the ambient H-description
of F, and use their positive combination with coefficients 1,T,...,T^(d-1).
Each forbidden linear evaluation is a nonzero polynomial in T. For the second
objective the pairwise zero-collision conditions are also nonzero linear
functionals of h, once f avoids every direction kernel. Integer T therefore
avoids their finitely many roots. Source T<=1+(d-1)|E_q| and target
T<=1+(d-1)(|E_q|+binom(|E_q|,2)) are sufficient theoretical search bounds.
The implementation has a smaller explicit try cap; exhaustion is failure to
produce a certificate, not nonexistence of a route.

Every direction hyperplane crosses that objective segment at most once. Between
successive crossing parameters the maximizing point is unique: a positive-
dimensional maximizing face would have an edge with zero objective evaluation,
contradicting the cover. At a crossing at most one nonparallel direction is
orthogonal. All edges of the maximizing face lie in that line, so the entire
face is either a point or a segment. Neighboring unique optimizers are therefore
equal or actual adjacent vertices. Delete stationary changes.

This constructs a path with

    L <= number of separating cover lines <= |E_q| <= B_q.      (4.1)

Every retained edge strictly increases h. This h is the constructed target
objective; the input is not asserted to preserve an unrelated user objective.
The path need not be globally shortest. No previously supplied crossing list,
neighbor graph, route, or general-path existence for a guessed L is an input.

### Exact implementation and independent positive certificate

The code builds the entire candidate cover from the recognized base and cut
normals, with exact rational rank/nullspace calculations. A preflight cap rejects
an excessive enumeration BEFORE any partial cover is returned as complete.

At rational sample parameters it uses the unchanged `exact_farkas_lp.py`.
A fixed vertex's optimizer interval on a line is convex; it cannot disappear
and later reappear. Binary search can therefore skip ranges of stationary
sample cells. Caching bounds the sample LP calls by the total number of cells,
no matter how many binary-search probes are attempted. One additional LP at
each real edge wall records its full supporting dual. At most 2|E_q|+1 such
path LP calls are needed; overlap certification is a separate count.

The returned certificate independently checks:

* each vertex's original feasibility and d independent tight rows, by a rational
  right-inverse identity;
* each pair's d-1 independent COMMON original tight rows, again by a right
  inverse, together with distinct feasible vertex endpoints;
* the exact supporting functional and nonnegative dual at each crossing;
* the corresponding direction line, its unique crossing time and increasing
  order, plus all common original rows along the whole path.

A common rank-(d-1) face containing two distinct vertices is an entire ordinary
edge; no count-only test can certify a diagonal. This argument works at nonsimple
vertices and in lower-dimensional final H-presentations, with all affine equality
ranks counted in the ambient system. The final audit calls no LP. It DOES
recompute the finite cover elimination, endpoint-row independence and an optional
affine-chart inverse; those computations are not falsely described as absent.
Python, JSON parsing and rational elimination are not Lean-extracted code.

The number of LP oracle calls and the rational query sizes are polynomial for
fixed k, or fixed q with certified overlap. This is not a polynomial pivot bound
for the bundled Bland simplex implementation, which retains its per-call cap.
The experiment is not a newly invented general polynomial-time LP algorithm.

## 5. Recognized bases and the original-facet parameter

The executable accepts two sources of a PROVED complete base direction cover:

* a nondegenerate box: N=d coordinate lines;
* the positive connected-building-set simplex presentation from #269, with
  the complete canonical H-system: N<=binom(d+1,2) coordinate-root lines.

An optional SUPPLIED nonsingular affine chart is checked and applied to both
the inequalities and directions. Unknown hidden charts are not discovered.
An arbitrary H-system accompanied by an asserted direction list is refused.
The abstract theorem applies to any genuinely known complete base cover, but
the executable does not infer such a certificate for arbitrary polytopes.

The final original A,b is the base's H-system plus the actual cut rows; when A,b
is explicitly provided it must match exactly. No high-dimensional extension or
noninjective projection is used. Cuts can remove old facets or make input rows
redundant. Reports therefore say ORIGINAL H ROWS, not automatically facets.
Small references separately compute the actual number of genuine facets.

For a full-dimensional final Q, redundant added cuts can be discarded
mathematically, leaving at most m genuinely facet-defining cuts if Q has m
facets. The overlap condition survives deletion. Also d<m. Thus (3.2) is a
polynomial in the FINAL original facet count for fixed q when the base is a
box or generalized permutahedron. For example the crude degrees are 2q+1
and 3q+2, respectively. This is a class result, not an unrestricted assertion
that every m-facet polytope has such a low-overlap presentation. The code does
not globally perform that redundant-row pruning; it reports the actual supplied
row/line counts. For lower-dimensional Q the stated bound is in the supplied
ambient presentation, not falsely in its potentially much smaller intrinsic
facet count.

A cut may really leave the old root-direction class: the small building-set
examples have actual final edges outside the uncut root cover. The new closure
and original-H checks, not #269's once-only summand transfer, certify those steps.

## 6. Many cuts with overlap one: explicit family and an adverse comparison

In [0,1]^d choose s distinct binary vertices v. Assign each v positive integer
weights w_vi>=1, and add

    sum_i (2v_i-1) w_vi x_i <= sum_{v_i=1}w_vi - epsilon,
    epsilon=1/5.                                             (6.1)

This removes a shallow weighted corner neighborhood: its boundary satisfies
sum_i w_vi |x_i-v_i|=epsilon. Two distinct removed corners have L1 distance
at least one, whereas a point on both new boundaries would have total L1
distance at most 2epsilon<1. Hence their new facets are pairwise disjoint.
The executable also checks this with actual original-row dual inequalities.
For two cut rows their summed-box-support gap is at least
sum_{i:v_i!=v'_i}min(w_vi,w_v'i)-2epsilon > 0.

Every old facet survives, every cut creates a simplex facet, and exactly its
one old cube vertex is removed. The polytope is simple, with

    m=2d+s genuine facets,  f0=2^d+s(d-1).

This follows from disjoint shallow vertex truncations; the large counts are
formulas, not enumeration. The four-dimensional case is independently checked
against all 1001 square H systems and its full graph.

The tests use s=2d-2, varying weights, and produce:

| d | s | direction candidate bound with q=1 | without overlap | returned edges |
|---|---:|---:|---:|---:|
|4|6|40|120|9|
|8|14|400|170544|21|
|16|30|3616|511738760544|45|

The last completed cover has 2660 distinct lines after deduplication; all 435
pairwise cut exclusions have exact duals, requiring no LP in this box case.
This is a useful reduction in the certificate/search inventory, not a new best
diameter theorem for truncated cubes. An elementary cube-chain detour gives
an independently audited 2d-1-edge comparison route for the SAME endpoints:
7,15,31 in these tests. All intermediate truncated cube corners are bypassed
along edges of their simplex cap. The new method is explicitly NOT a benchmark
winner on this family. No shortestness claim is made for that comparison.

## 7. Actually executed tests

The eight complete small-H reference models contain 86 vertices and 137 edges,
from all 1076 square original systems. Every edge's direction lies in the new
cover; 56 are outside the base cover. They include a genuinely nonsimple input,
a two-dimensional section in three-dimensional coordinates, a point, an
interval, and cut building-set sums. All endpoint pairs are tested on models
with at most 36 distinct pairs; larger models use 36 seeded pairs plus a
stationary pair. The 173 routes have 420 edges versus 372 BFS edges, with
38 nonshortest routes retained. There is no claim of average improvement.

The full small-route suite makes 1519 path LP calls, 3041 simplex pivots and
1099 sample queries; auditing checks 534 retained common-row occurrences.
These are implementation counts, not a worst-case pivot bound.

Five larger cut-box runs use dimensions/cut counts 8/1,16/1,32/1,12/2,24/2.
Their actual routes have 4,7,14,10,20 edges. The 32D one-cut cover has528 lines;
the 24D two-cut cover has2470 against a2600 candidate count. No final graph or
final vertex count is enumerated/claimed for these inputs. The numbers 2^d in
the report refer ONLY to their uncut cube, not the cut polytope.

The three many-cut cases above add541 exact pair-separation certificates and
75 delivered edges, versus53 explicit comparison edges. Only the smallest
gets an independent full graph. Four affine re-encodings reproduce the exact
transformed path. Three further epsilon=2^-20,2^-80,2^-160 cases check tiny cuts
with exact fractions. The k+1 support requirement is tested at k=2,3,5, with
one-edge routes along the corresponding common face. Twenty invalid/forged
cases fail, including a falsely asserted overlap bound, omitted overlap tests,
an unproved base cover, false rank/dual data, a square diagonal, and caps.
A serialized positive certificate replays with all LP execution disabled.

All five stages and their source/dependency hashes are saved. The final summary
and clean replay are derived records, not platform receipts. Full fixtures,
raw reports and the patch are bundled. No Actions trigger is appropriate for
this research-only contribution.

## 8. What remains toward Polynomial Hirsch

This gives actual routes after structure-breaking cuts, and many cuts are
allowed when their boundary overlap is independently small. It does not assume
that short paths come from a small global flag refinement. It also does not
assume a uniform numerical slack contraction; the count is combinatorial.

The unrestricted step is still missing. An arbitrary polytope can indeed be
written as a large bounding box intersected with its facet halfspaces, but if
the box is strictly outside it, at least d independent added facets meet at
every vertex. Then q>=d, and the fixed-q polynomial conclusion is unavailable.
Similarly, taking the original polytope itself as the base may require an
exponentially large direction cover. These are not inexpensive representations
proved by the current result. The bound is exponential when these parameters
grow without control.

A stronger result would bound the directions actually encountered along a
route without a small global direction cover, or rigorously supply low-overlap
structural descriptions of the actual remaining carriers. Neither premise is
introduced as a solved child. The current result is a precise cut-stability
extension and a verified construction in its stated class.

## Primary references

Moise Blanchard, Jesus A. De Loera, Quentin Louveaux, *On the Length of Monotone
Paths in Polyhedra*, SIAM J. Discrete Math. (2021), Theorem1.3 and Lemma2.5;
https://arxiv.org/abs/2001.09575 ; DOI10.1137/20M1315646.
The edge-direction normal-fan refinement and monotone-diameter mechanism are
classical. We give the direct objective-line proof needed for the actual code.

Alexander Postnikov, *Permutohedra, associahedra, and beyond*,
https://arxiv.org/abs/math/0507163 . The recognized positive connected-building-
set base and its canonical H binding are reused from #269; no signed-simplex
extension or recognition for arbitrary H-inputs is asserted.
