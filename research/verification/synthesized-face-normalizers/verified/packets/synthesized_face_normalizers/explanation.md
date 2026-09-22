# Synthesized affine normalizers on shrinking original target faces

## Exact public result

Let P equal both the convex hull of a finite real set C in ambient dimension d
and the ORIGINAL m halfspaces A_i x <= b_i. Let u,v be actual extreme points.
These are the only geometric input hypotheses. In particular, no affine
denominator, positivity certificate, independent basis, selected row order,
short phase, graph, or route is an input premise.

Filter C for actual extremality to obtain the COMPLETE original vertex set V.
For a finite set H of original row labels, let

    F(H) = {x in V : A_i x=b_i for every i in H}.

For every H consisting of rows tight at v, and every original row j, the theorem
DERIVES a slope E(H,j) and the anchored affine denominator

    q_(H,j)(x) = 1 + E(H,j)(x-v).

It is positive at every vertex of F(H). It minimizes the number of distinct
normalized slack values on F(H), against EVERY affine denominator a+D(x) with
arbitrary real coefficients that is positive on that same finite face. The
competitor is not restricted to an input guess list or a common projective chart.
No claim of positivity outside that face is needed or made.

Let G be the original rows tight at both u and v, and T the original target
rows tight at v but missing at u. An eligible list J is a duplicate-free list
of labels from T, of length at most min(d,m-d), whose homogeneous equations
together with G have trivial kernel. The existence of an eligible list is proved.

For J=(j_1,...,j_r), start H_0=G and put H_t=H_(t-1) union {j_t}. Define

    c_t(J) = |{(b_(j_t)-A_(j_t)x)/q_(H_(t-1),j_t)(x)
                   : x in F(H_(t-1))}| - 1.

The public List.rec expression computes precisely these conditional charges.
The theorem derives an eligible list minimizing their sum, constructs an
original-edge route of length L, and proves

    L <= sum_t c_t(J) <= sum_t c_t(R)

for every eligible competing order R. For the SAME route it also proves

    (every returned local charge <= K) => L <= K*min(d,m-d).

Every visited point is an actual extreme point of ORIGINAL P. Every consecutive
segment is whole, nondegenerate, and IsExtreme in ORIGINAL P. Every acquired
target equation remains tight at every edge, including unselected target rows.
The theorem does not assume a bound on the computed charges; the final K clause
is an implication about the returned route, not a small-cost input oracle.

## 1. Synthesize all local normalizers from finite data

For target-tight H, the target vertex v belongs to F(H), including degenerate
and lower-dimensional cases. Apply accepted #334's complete finite-normalizer
catalogue with C=F(H), numerator s(x)=b_j-A_j x, and anchor v.

Its catalogue consists of at-most-d subsets of original pair-coincidence tests.
Anchoring a positive affine denominator at v preserves ratio coincidences.
Each desired coincidence is affine-linear in the slope coefficients. The proof
selects at most d original contrast equations spanning all ties of any positive
denominator. Every positive solution of those selected equations preserves all
old ties, and additional mergers can only lower the spectrum cardinality.

The finite catalogue therefore contains an optimum over all positive REAL
affine denominators. Select that optimum for each (H,j). On non-target-tight H,
use a harmless zero slope; those entries have no asserted optimality and are
never used by an eligible target flag. Classical choice assembles the family.
No new feasibility/LP oracle is introduced into the public statement.

This is finite existence and completeness, not extraction of a Lean program.
The separate exact rational implementation provides feasible witnesses or dual
exclusions, with explicit completeness checks. Its Python and JSON parser are
not kernel-verified.

## 2. A complete original-edge phase with only local positivity

Suppose the current actual vertex x satisfies H, and target row j is still
missing. Set r=(b_j-A_j x)/(1+E(x-v)). Feasibility and denominator positivity
give r>0. The current ratio identity is

    r*(1+E(x-v)) = b_j-A_j x.

Use the LINEAR objective f=A_j+r*E. Since A_j v=b_j and the denominator at v
is exactly one, f(v)-f(x)=r>0. The accepted original-hull improving-edge theorem
inside the current target-lock face gives a genuine original edge from x to a
better actual vertex y. It preserves every target equation already tight at x,
so y still satisfies H. The denominator is therefore positive at y, even if it
is zero or negative at vertices outside F(H). The objective improvement then
implies strict normalized-slack decrease at y.

The objective is recomputed at every step; no globally fixed objective or
uniform numerical improvement is assumed. Among the finite distinct values on
F(H), the set strictly below the current ratio loses at least one element at
each step. Strong induction constructs the ENTIRE acquisition phase and bounds
its length by the local spectrum cardinality minus one. A row already acquired
incidentally uses a zero-edge phase.

## 3. Assemble the synthesized phases and choose the order

Accepted active-row injectivity and small-completion arguments derive at most d
initially missing target labels completing the equations G. Their number is also
at most |T|<=m-d. Turning the selected finite set into a duplicate-free list gives
a nonempty family of eligible orders.

For any eligible order, acquire its head with the denominator synthesized on its
entry face; then insert that row into H BEFORE using the next synthesized slope
and spectrum. Induction constructs and appends all actual phases. All shared
and selected equations remain tight. At the end, their trivial homogeneous
kernel forces the endpoint to equal v. Thus L<=sum(c_t), not merely a bound on
the number of face changes. Natural-number well-ordering selects the minimum
attained budget, and summing local charges bounded by K gives the same-route
K*min(d,m-d) clause.

The helper charges_le_competitor additionally proves the ordered sum no larger
than that for ANY other anchored affine family positive on the target faces.
The public local-optimality clause also compares with unanchored affine
competitors. Consequently the construction combines the two earlier methods:
constant-one denominators recover raw face-local charging; restricting any
globally positive row normalizer to the successive faces cannot increase its
number of values. The new optimized budget is therefore no worse than either
optimized raw face-local or optimized global normalized charging. This compares
BUDGETS, not the lengths of independently chosen routes or their shortestness.

Planned prefix faces can be larger than the actual lock faces, since incidental
acquisitions are not inserted into the planned charge definition. Positive
planned charges may accompany zero-edge phases. The result does not claim that
the synthesized order is an optimal policy depending on each reached vertex.

## Concrete exact example

Use the pentagon with vertices (-1,2),(0,0),(2,4),(3,0),(4,2), and ORIGINAL rows

    -2x-y<=0, -2x+3y<=8, -y<=0, x+y<=6, 2x-y<=6.

Take u=(0,0), v=(2,4). The target rows are -2x+3y<=8 and x+y<=6, with no shared
target row initially. Their independent equations both have to be selected.
The exact consumer finds minimum raw face-local budget4 and minimum GLOBAL
normalized determining budget4. The new synthesized local budget is3, with an
explicit two-edge route (0,0),(-1,2),(2,4).

For the first selected row, the synthesized slope anchored at v is (2/3,-3/4),
and the exact global normalized values are {0,60/23,3}, costing2. On its acquired
edge-face, the second slope is (0,-1/2), with normalized values {0,5/2}, costing1.
This is an executed rational instance and independently audited finite search,
not a separate concrete Lean instance theorem or a historical-priority claim.

## Scope and remaining mission obligation

All normalizers, local positivity, local spectral optima, an eligible determining
order, complete phases, and the original-edge route are outputs of the geometric
input. Arbitrary redundant rows/generators, nonsimple and lower-dimensional
bodies, zero dimensions, constant rows, and coincident endpoints remain included.

This closes the previously written-only synthesis-to-original-route bridge and
allows re-synthesis after each planned face restriction. It is not merely a
renaming of #333 with supplied denominators. It also does NOT establish a uniform
polynomial upper bound on these optimal conditional costs. Complete actual
vertex sets and finite catalogue/order searches may have exponential size in
original input parameters. There is no efficient H-to-V algorithm, polynomial-
time optimizer, shortest-path claim, all-facet nonrevisiting theorem, or proof of
unrestricted Polynomial Hirsch. Samples or visited vertices cannot replace F(H).

The remaining conjecture-facing problem is to bound useful optimized local
costs in original parameters, or find a different original-edge argument. The
known raw-cost projective-cube barrier remains valid and is not resubmitted.

## Source reuse and verification boundary

The 932-line/38243-byte original-edge/active-row prefix is reused byte-for-byte
from accepted #333 (also identical to #332's prefix). The entire 226-line/
10107-byte NormalizerSearch namespace is reused unchanged from accepted #334;
its old public solution/print requests are omitted. Both dependency source blobs
and their five frozen manifest hashes were checked. No accepted target is
republished, and no target is imported as its own proof.

New code adapts the original normalized-edge argument to positivity only on the
prefix face, derives a complete normalized phase there, synthesizes the local
slopes, and composes both inductions. The public statement uses only Mathlib
symbols and explicit let formulas, with an imports/open/options-only preamble.
It matches top-level theorem solution exactly. Eight final transitive axiom
reports are requested; requests are not a successful audit.

No local lean/lake/elan or checked installation/cache was available. Both release
and raw toolchain hosts failed DNS. Text, hashes and rational checks are NOT
Lean compilation. The complete prepared packet is intended for ONE pinned final
compiler/axiom/publication gate. Any actual failure must be retained, not replaced
by a claim of complete verification or a weakened hypothesis. Keep Lean4.30.0,
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict protocol0.10.8 and the
existing verifier/publisher secret isolation unchanged.

## Executed supporting tests

The 21-model exact suite checks770 endpoint routes containing936 original-edge
occurrences, compared with922 total shortest-path edges. All11 nonshortest
routes,41 multiedge phases,25 nonacquiring steps,46 within-phase objective
changes and72 zero-edge phases are retained. The consumer checks26566 eligible
orders independently of the producer's subset dynamic program.

It audits10066 face/row/target normalizer certificates comprising15840 tested
linear systems:12322 positive witnesses and3518 certified exclusions. There are
83 chosen denominators positive on their planned face but not globally positive.
The optimized budget improves raw face-local charging in81 endpoint cases and
global normalized charging in154;13 improve both. No solver cap is treated as an
exclusion or optimum. Ten malformed controls are rejected.

Saved replay disables synthesis, equality solving, strict feasibility, flag
selection, route construction and improving-edge production. The consumer
reconstructs full original prefix faces, audits optimum certificates, enumerates
all eligible competing orders, and checks every whole original support edge.
A clean six-script workspace reproduces BOTH complete JSON outputs byte-for-byte.
Full fixtures are exported and regenerate; repository summaries are labelled
derived. These arithmetic checks are not all-real proofs by sampling or kernel
verification of the Python implementation and parser.
