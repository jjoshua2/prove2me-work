# Recompute original-row charges on a shrinking target flag

## Exact statement and what is derived

Let P equal both conv(C), for a finite real family C in ambient dimension d,
and its ORIGINAL m halfspaces A_i x <= b_i. Let u,v be actual extreme points.
Derive the actual vertex set V by filtering C for Mathlib extremality. Let G
contain original rows tight at both endpoints, and let T contain original rows
tight at v but not u.

An eligible ordered list J contains distinct labels from T, has length at most
min(d,m-d), and, together with G, has trivial homogeneous kernel. Existence of
such a list is PROVED using accepted original target-active injectivity and
small-completion geometry. No list, rank, basis, graph or determining property
is supplied as a public premise.

For a list J=(j_1,...,j_r), set H_0=G and H_t=H_(t-1) union {j_t}. Define

    V_t = {x in V : A_i x=b_i for every i in H_t},
    c_t = |{A_(j_t) x : x in V_(t-1)}|-1.

These are DISTINCT values on actual ORIGINAL vertices in the planned prefix
face, not on the whole polytope and not a nonlinear change of coordinates.
The public List.rec expression computes exactly this list of charges.

The theorem derives an eligible J minimizing sum_t c_t over ALL eligible lists,
and constructs an original-edge route from u to v of length L satisfying

    L <= sum_t c_t.

The SAME route also satisfies

    (every computed local charge c_t <= K) => L <= K*min(d,m-d).

The only initial geometric hypotheses are exact finite H/hull equality and actual
endpoint extremality. The minimum charge, local spectra and complete route are
outputs. Every route point is an actual original extreme point. Every consecutive
segment is whole, nondegenerate and IsExtreme in ORIGINAL P, and every already
acquired target row remains tight, including unselected target rows.

## 1. Complete acquisition inside a prefix face

Suppose the current actual vertex x satisfies all equations H, every row in H
is tight at the target, and j is another target-tight original row. If A_j x is
already b_j, the phase may have zero edges. Otherwise feasibility gives
A_j x < A_j v. The accepted improving-edge construction operates inside the
current target-lock face and supplies a better actual ORIGINAL neighbor y.
Every target equation currently satisfied remains satisfied, hence all of H.

Use only S={A_j z : z an actual original vertex satisfying H}. Let above(x)
contain the distinct values in S greater than A_j x. Strict improvement implies
above(y) is a subset of above(x); the new value A_j y is in above(x), not in
above(y). Induction on this strictly decreasing finite cardinality constructs
the ENTIRE phase ending on A_j=b_j. Its length is at most |above(x)|<=|S|-1.
No positive lower bound on a numerical objective gap, bounded phase, selected
neighbor, or pre-existing short route is assumed.

This construction preserves all currently acquired target equations at every
edge. Their propagation through the complete phase is inherited from #329.
The planned prefix H may omit incidental target equations acquired en route;
the actual lock face can therefore be smaller. Charges are safe upper bounds
computed on the planned prefix face, NOT claimed to be the exact cheapest
current-state phase costs. An already-acquired row can use zero edges even when
its planned-face charge is positive.

## 2. Assemble an ordered flag without paying global levels

Induct on the remaining selected list. Acquire its head using the phase above,
then insert that row into H BEFORE computing and paying for the tail. All shared
and previously selected equations remain locked. When the list is empty, the
derived homogeneous kernel property forces the current point to equal v.
Appending the phase routes proves L<=sum(c_t). No independent face-drop count
is substituted for the number of edges within a phase.

The new charges_le_global helper separately proves that every ordered local sum
is at most the sum of GLOBAL row-level weights for the SAME list: each prefix
vertex set is a subset of V. Thus ordering and restriction do not worsen that
particular global budget. Combining this with the eligible-list minimum gives
comparison with any eligible global determining completion. This does not say
that the output path is a shortest path or that every ordering has the same cost.

## 3. Derive a nonempty small family and optimize its cost

Accepted #330's small_completion selects at most d initially missing original
labels completing the shared equations. Its selected cardinality is also at most
|T|<=m-d, the latter derived from original source-active injectivity. Converting
the finite set to a duplicate-free list supplies a candidate of length at most
min(d,m-d). The bound does not assume full-dimensionality or simplicity.

Natural-number well-ordering selects the smallest attained conditional sum over
eligible lists. The complete route construction is applied to a list attaining
that value. This is mathematical existence/minimization, not a claim of efficient
flag enumeration. If all returned charges are at most K, their sum is at most
K times the derived list length, proving the same-route corollary.

Redundant original rows and generators, nonsimple and lower-dimensional bodies,
constant rows, dimension zero, K=0, and coincident endpoints remain included.
No global target-row level bound is needed. No unrestricted small local-cost
bound is concluded either: this theorem alone does NOT prove Polynomial Hirsch.
The conditional minimum might still be large, and selecting a flag efficiently
is a separate question. Neither global monotonicity, all-facet nonrevisiting,
shortestness, a facet-lattice theorem nor efficient H-to-V is asserted.

## 4. Known triangular stress test: local versus global budgets

This is a written/exact application of the new generic interface, NOT a new Lean
instance/classification theorem for the triangular family. #282 owns the separate
all-actual-vertices route/classification proof; that PR is not modified. The
adaptive two-level phenomenon was already explained in #276, so it is not claimed
as a new discovery or a new best diameter bound.

Use the ORIGINAL 2d inequalities

    0 <= x_(d-1) <= 1,
    e*x_(j+1) <= x_j <= 1-e*x_(j+1),  j<d-1,

with 0<e<1/2. Each Boolean corner chooses a lower or upper endpoint recursively
from the last coordinate backwards. Finite-hull equality follows by induction:
interpolate within the head interval, then distribute a convex combination of
tail corners through the affine lower/upper lifts. Every corner is extreme by
its triangular independent tight rows. Conversely an extreme point must be at
one of the two fiber endpoints and have extreme tail, by the same affine lifting
and convex-decomposition argument. This gives all 2^d corners.

Choose the all-upper corner as source and the zero corner as target. The only
target-tight rows are the d lower rows, all initially missing, with no shared
equations. They are independent, so any determining completion must select all d.
The lower functional -x_j+e*x_(j+1) takes value zero at a lower choice, and value
-1+2e*x_(j+1) at an upper choice. The possible tail-coordinate values have exactly
2^(d-j-1) members: the maps t -> e*t and t -> 1-e*t are injective and have disjoint
ranges, with the empty-tail base case a singleton. All nonzero lower-functional
values are negative and distinct. Thus its GLOBAL weight is 2^(d-j-1), and every
global determining completion costs exactly

    2^d-1.

Choose the ordered lower rows d-1,d-2,...,0. At stage j, the previously fixed
lower suffix forces x_(j+1)=...=x_(d-1)=0. Among actual vertices in this face,
x_j is either zero or one, so the selected lower functional has exactly the two
values {-1,0}. Each local charge is one. Every eligible order has d labels and
each new row has two distinct values somewhere in its prefix face (choose its
upper bit and all other bits lower), so d is also the minimum local sum.

Flip the source's upper bits to lower in that reverse order. Adjacent points have
d-1 independent common ORIGINAL tight rows; their common supporting slice is a
line. The released upper row and newly acquired lower row bound that line at
exactly the two endpoints. Convexity then identifies the whole supporting slice
with their nondegenerate segment. All acquired target rows stay tight.

Executed e=1/4 cases have dimensions4/8/16/32/64, with124 original edges in total.
The64D input has128 original rows, global determining budget18446744073709551615,
local budget64 and a checked64-edge route. All16/256 corners and their spectra
are enumerated only in dimensions4/8. Larger counts use the written recurrence,
NOT enumeration of2^64 vertices or a full large graph. There is no extra expensive
redundant row in this example. It is still a known-family stress test, not a
uniform statement about arbitrary polytopes or a duplicate formal #282 result.

## Source reuse, verification boundary and executed tests

The retained932-line/38243-byte block consists of exact accepted #330 proof
segments plus namespace closures. All retained bodies are byte-identical: Route
operations, original finite-hull edge geometry, original active/kernel/locking
facts, Edge/improve_locked, route-wide preservation, directions/small_active_rows
and small_completion. Unused later blocks and old public roots/prints are omitted.
The dependency's complete source blob and all five frozen manifest hashes were
checked. No accepted target is resubmitted or used to prove itself.

The new public solution matches problem.json exactly with Mathlib-only public
types and an imports/open/options-only preamble. Eight final transitive reports
are requested. Requested reports and source checks are not passing compilation.
No local lean/lake/elan or checked caches were available; toolchain-host DNS
failed. The complete candidate is prepared for ONE ordinary pinned final
compiler/axiom/publication gate, not repeated speculative hosted editing. Preserve
any actual failure. Keep Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f,
strict protocol0.10.8, duplicate guards and verifier/publisher isolation unchanged.

The18-model exact small suite checks650 endpoint routes/733 original edges versus
726 total shortest edges. ALL7 nonshortest routes,36 multiedge phases and18
nonacquiring steps are retained.184 cases improve strictly on the OPTIMAL GLOBAL
determining-row budget, not just an arbitrary old list. The consumer independently
checks30238 eligible orders using exact rational row rank and reconstructs all
prefix faces/level sets; the producer uses subset dynamic programming. Every
whole original edge is checked by the unchanged geometric consumer. Serialized
replay disables selection, route and improving-edge production. Nine malformed
small controls and four large-family controls are rejected.

A clean FOUR-script workspace reproduces all FIVE complete JSON reports, fixtures
and controls byte-for-byte. These computations are supporting tests, not
Lean-extracted Python, a verified parser, extra formal family instances, or an
all-real proof by sampling. Complete outputs accompany the export and regenerate;
repository summaries, when present, are explicitly labelled derived.
