# Forced original edges survive target-slack row deletion

## What this adds after the charging optimizer

Accepted PR343 characterizes the best integral row assignment for an input
family of original exposed-edge occurrences. For target-slack rows I, each edge
e has eligible set S_e consisting of the original rows slack at the target and
tight along the whole edge. Its Hall bottleneck F(J) consists of occurrences
with S_e contained in J. This packet gives that exact condition a geometric
interpretation, not another equivalent matching theorem.

Retain every row tight at an actual target vertex v and every row in J. Write

    P = {x : A_i x <= b_i for every original i},
    Q_J = {x : A_i x <= b_i whenever A_i v=b_i or i belongs to J}.

For every genuine nondegenerate original exposed edge e=[u,w] avoiding v with
S_e contained in J, define its canonical extended carrier

    E_J(e) = Q_J intersect {u+t(w-u) : t is real}.

The complete candidate proves that E_J(e) is an exposed subset of Q_J, contains
the old edge, and is contained in its original affine line. The parameterization
of that line is injective, so the carrier is nondegenerate and one-dimensional
in the explicit affine-line sense. Most importantly,

    P intersect E_J(e) = e.

Thus different original geometric edges cannot become the same relaxed carrier.
For an input finite family, equality of carriers implies equality of original
edge sets, and an injective family of geometric edge sets has injective lifts.
Repeated OCCURRENCES of the same edge are not made distinct by this operation.

This is a geometric survival/recovery theorem, not a polynomial bound on the
number of carriers, a route constructor, or a proof of Polynomial Hirsch. It
removes the need to assume that all surviving original endpoints remain relaxed
vertices. That assumption is false, including for very small original polytopes.

## Public hypotheses and precise limitations

The inputs are finite original real halfspaces in arbitrary ambient dimension,
a feasible actual extreme target v, a chosen row subset J, and a finite family
of distinct-endpoint exposed original segments avoiding v. The endpoints need
only be supplied as feasible; their whole original exposed-segment property is
explicit. There is no finite-hull identity, boundedness, full-dimensionality,
simplicity, active-rank oracle, vertex catalogue or supplied exposing functional.
The target can be degenerate and rows can be repeated, rescaled, redundant or zero.
Empty edge families are included, also when ambient dimension is zero.

The condition S_e subset J is an INPUT specifying which Hall-forced edges are
under consideration. It does not assume a small row load or bound on their
number. J need not itself exclude target-tight labels; retaining those labels
again makes no difference. The theorem is sufficient, not an if-and-only-if
criterion for survival: deleting a redundant copy of a common active row may
leave enough other rows to expose the same carrier even when S_e is not contained
in J. No converse is silently asserted.

The carrier may be a longer bounded segment or an unbounded ray. Its original
endpoints need not remain extreme points of Q_J. Accordingly this does NOT
identify original edges with edges between the old vertices of the relaxed
vertex graph. It preserves the entire exposed line section, with exact recovery
on reinstating all original inequalities. No auxiliary cap is introduced.

## 1. Feasible two-sided perturbations from the original active equations

Reuse the exact accepted finite_margin helper. At any feasible point x, suppose
z annihilates every original row active at x. Active rows are unchanged by
x+epsilon*z and x-epsilon*z. Every other row has strictly positive slack. The
finite-margin construction supplies one epsilon>0 making both perturbations
feasible simultaneously. This is a derived local feasibility result, not an
assumed tangent-space characterization or a perturbation oracle.

## 2. Derive the supporting line from the exposed segment

Let x=(u+w)/2 and take an exposing linear functional f for the original segment.
If z annihilates every original row active at x, the previous lemma gives two
feasible points x+epsilon*z and x-epsilon*z. Since x maximizes f, the two
inequalities imply f(z)=0. Consequently both perturbed points also maximize f
and lie in the WHOLE original segment, not just in its supporting hyperplane.
Writing x+epsilon*z as a convex combination of u,w yields

    z = t*(w-u)

for a derived real t. Thus the common-active kernel has only the edge direction.
Conversely the edge direction annihilates all rows tight at both endpoints.

For feasible u,w, a row is tight at the midpoint exactly when it is tight at
both endpoints: two nonnegative endpoint slacks average to zero only if both
are zero. If an arbitrary ambient point y satisfies all common-active equations,
y-x is in the kernel above and therefore y lies on the affine line through u,w.
Every point of that line satisfies the common equations by linearity. This proves

    {y : A_i y=b_i for all rows tight at u and w} = affline(u,w).

No full-dimensionality or numerical rank is assumed in this argument. In the
formal statement the line is parameterized explicitly rather than invoking an
additional face-lattice structure or relying on a separately supplied finrank.

## 3. Expose the relaxed carrier with retained ORIGINAL rows

Every row tight at both endpoints is either tight at v or slack at v. In the
second case it belongs to S_e and hence to J by the forced condition. Therefore
all common-active rows are retained in Q_J.

Sum those common-active original linear forms to obtain f_e. Each retained row
is bounded above by its original right-hand side throughout Q_J. Equality in
the sum holds exactly when equality holds in every common-active row: the sum
of their nonnegative slacks is zero only when each slack vanishes. The pinned
Mathlib Finset.sum_eq_zero_iff_of_nonneg supplies this finite-sum implication.
Thus the maximizing set of f_e on Q_J is precisely

    Q_J intersect {all common-active equations}
      = Q_J intersect affline(u,w) = E_J(e).

This constructs the exposing functional from original rows. No arbitrary
exposed carrier, row basis or retained-edge oracle is a public hypothesis.

## 4. Recover the exact old edge and prevent merging

The original exposing functional for e is constant on affline(u,w), because
it has equal value at u,w. Any point of P on this line therefore maximizes that
functional and belongs to e. This proves P intersect affline(u,w)=e.
Since P is contained in Q_J, it follows that P intersect E_J(e)=e.

The target v is outside e by its actual extremality and the distinct non-target
endpoints, so it is outside E_J(e) as well. If E_J(e)=E_J(e'), intersecting both
with the original P gives e=e'. The injection is proved, not assumed. When the
input repeats an edge, its repeated carriers are equal, exactly as required
for a charging ledger that counts occurrences separately from edge types.

## Relation to earlier deletion and clipping work

PR165 preserves the target and pointedness when deleting target-slack rows;
PR168 supplies batch reinsertion routes conditional on parent-face budgets.
This packet does not reprove those public results or turn their budget assumptions
into conclusions. It proves precise preservation and recovery of the subset of
original edges selected by PR343's forced-row condition. Their old endpoints
can disappear, which is why the carrier cannot simply be replaced with an
old-vertex adjacency assertion.

The geometric mission gap is still a quantitative bound along a well-chosen
original-edge route. Injectivity does not bound the number of relaxed carriers.
For example, a pyramid over a high-dimensional cube has a single target-slack
base row at its apex; every base edge is forced into that one row, while every
base vertex is directly adjacent to the apex. An arbitrary large edge family
is not a large shortest target route. This classical family is a written warning,
not a new formal theorem or a Polynomial Hirsch counterexample.

## Executed exact supporting tests

A new standalone test imports the unchanged committed PR343 arithmetic/reference
script; it does not depend on or retry the earlier blocked radial-envelope script.
It independently computes the original supporting-line interval from every row,
the relaxed interval from retained rows, common-active rank, summed supporting
functional, endpoint survival, and equality/recovery identities.

Nine small original-H models include cubes through dimension four, a clipped
square, a nonsimple octahedron and pyramid, a square embedded in R^3, a segment
and an unbounded planar body. Complete small vertex enumeration solves 946
original square systems. All target choices and all subsets of target-slack
rows are checked for their forced edges. The suite audits 7638 edge/row-subset
carriers, 62212 line probes and 7638 distinct-carrier comparisons. It finds 3268
ray carriers, 3285 strict enlargements and 3290 lost-endpoint occurrences.
Eight malformed-certificate controls are rejected. The segment case has no edge
avoiding an extreme target and is correctly vacuous; the embedded square supplies
nonvacuous lower-dimensional tests.

Four genuinely high-dimensional selected cube routes in dimensions 8,16,32,64
add 116 carrier checks and 812 probes. All 116 carriers are rays and lose one old
endpoint as a relaxed vertex. No full high-dimensional vertex/graph enumeration
or global spectrum calculation is claimed. These are selected original edges,
not a formal route construction or a new route-length estimate.

For the clipped square 0<=x,y<=2, x+y<=3 and target(0,0), keeping x+y<=3 and the
target-tight rows turns the old diagonal edge[(1,2),(2,1)] into[(0,3),(3,0)].
Both old endpoints lie inside the new edge. Keeping only y<=2 and the target-
tight rows turns[(0,2),(1,2)] into the ray{(t,2):t>=0}. These cases are retained,
not hidden by endpoint-preservation assumptions.

A clean two-script workspace reproduces all FOUR complete report/fixture files
byte-for-byte. The consumer recomputes intervals and original-row identities,
but shares exact arithmetic utilities with the producer. Python/JSON, elimination
and serialized fixture parsing are not kernel-verified or Lean-extracted.

## Verification boundary

The candidate imports Mathlib only, contains a top-level solution matching the
metadata exactly, and writes no admission or new axiom. Five transitive reports
are requested. The accepted finite-margin and target-extremality helper bodies
are copied without alteration from the verified PR343 source. No accepted
public target is imported as its own proof or submitted again.

No local lean/lake/elan executable or checked installation/cache was found;
release/raw toolchain hosts failed DNS. Static type/hash checks and rational
execution are not Lean compilation. Use one prepared complete pinned hosted
gate, preserve any failure and keep a precise uncompiled repair separately.
Do not change Lean4.30.0, Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f,
reviewed strict protocol0.10.9, other ownership or verifier/publisher separation.
