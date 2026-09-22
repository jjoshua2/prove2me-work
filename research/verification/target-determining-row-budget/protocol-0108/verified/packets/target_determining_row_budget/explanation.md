# Pay only for a minimum-weight original target completion

## Exact public result

Let P be both the convex hull of a finite real family C in ambient dimension d
and the ORIGINAL m halfspaces A_i x <= b_i. Let u,v be actual extreme points.
The actual vertex set V is obtained by filtering C for Mathlib extremality.
Let G be the original rows tight at BOTH u and v, and T the original rows tight
at v but missing at u. Write w_i=|{A_i x : x in V}|-1.

The theorem DERIVES a finite set S contained in T such that |S|<=d and

    A_i z=0 for i in G and A_i z=0 for i in S  =>  z=0.

This is an output determining property, not a supplied rank/basis premise.
Among all subsets R of T with at most d labels and that same determining
property, the returned S has minimum weight sum_(i in S) w_i. The theorem then
constructs a route through actual original vertices, with whole nondegenerate
IsExtreme segments of ORIGINAL P, preserving every target row already acquired,
and

    L <= sum_(i in S) w_i <= sum_(i in R) w_i

for every such competing R. Minimum WEIGHT does not mean shortest path.
For the SAME route it proves

    (each SELECTED row has at most K+1 actual vertex values)
        => L <= K * min(d,m-d).

Only selected rows enter this antecedent. Unselected target rows can have
arbitrarily large level inventories. No graph, supplied determining set, active
basis, residual rank, small catalogue, short phase or route is assumed.

Exact finite H/hull equality and actual endpoint extremality remain explicit.
The general minimum weight need not be polynomial in original input size, and
the bounded-level implication retains its structural antecedent. This is not
unrestricted Polynomial Hirsch. It does not claim shortestness, all-facet
nonrevisiting, global monotonicity, a facet-lattice theorem, or polynomial-time
H-to-V or subset optimization. Redundancies, nonsimple/lower-dimensional bodies,
zero dimensions, constant rows and coincident endpoints are retained.

## 1. Derive a small determining completion

Let N be the common kernel of the equations in G. Restrict all original rows
active at v to N. Their joint evaluation is injective: a motion in N vanishing
on all those rows vanishes by the accepted actual-vertex active-kernel theorem.

Reuse the accepted small_active_rows proof. It selects a basis of the span of
these restricted original row functionals and returns at most dim(N) ORIGINAL
labels with the same joint kernel. No basis or rank assumption is introduced.
Delete returned rows already satisfied by u. Their restrictions vanish on N
because those labels belong to G. The remaining set S is contained in T and
still determines every motion in N. Since dim(N)<=d, |S|<=d.

This establishes a NONEMPTY finite family of eligible completions. Minimize the
nonnegative integer weight on its finite powerset filter. The proof uses finite
mathematical minimization, not a claim that enumerating the candidates is fast.
The initial existence construction gives <=dim(N); the public optimized-set
claim is deliberately the stated <=d bound, not a separately proved assertion
that the returned minimizer has exactly the common-rank deficit.

## 2. Route using only selected acquisition phases

Fix any derived completion S. Initially all common target rows G are tight.
Suppose the current vertex differs from v. If all selected rows were already
tight, then the displacement from v would vanish on both G and S; the derived
determining property would force equality. Thus some selected row is missing.

Apply the accepted #329 acquisition theorem to that selected row. It constructs
genuine improving original edges inside the current target-lock face until the
selected boundary is reached. The phase costs at most the number of DISTINCT
actual row values minus one, not a numerical gap-dependent estimate. All target
rows already tight remain tight throughout; in particular all of G remain fixed.

Define due(x) as the still-missing labels within S. A completed phase removes
its chosen label and cannot restore any earlier one. Nonnegative weights give

    cost(due_after) + weight(chosen label) <= cost(due_before).

Other selected labels incidentally acquired are removed for free. Strong
induction on |due(x)| constructs and appends all actual phases. The result
reaches v and costs at most the selected sum. Unselected target rows never need
a separately charged phase: they become tight automatically once G and S hold.
Their already-acquired equalities are nevertheless preserved by every edge.

## 3. Optimize the budget and derive the dimension cap

Run this construction on the minimum-weight derived completion. Its selected
weight is no larger than that of every eligible competing completion of size
at most d. The path length is bounded by this minimum weight, but its actual
length is not asserted minimal among all paths.

The selected cardinality is bounded both by d and by |T|. The accepted
source-active-row argument gives |T|<=m-d: missing target labels are disjoint
from the at-least-d original labels active at the actual source. Consequently
|S|<=min(d,m-d). If every selected row has at most K+1 values, its weight is at
most K, giving the same-route inequality K*min(d,m-d).

The optimized budget cannot exceed #329's all-missing-row budget because
S is contained in T and all weights are nonnegative. Unlike #329's uniform
corollary, this one only tests level counts on the returned selected rows.
Neither fact asserts a universal upper bound on the optimized weight.

## 4. A controlled example eliminating exponential overcharging

Use the unit cube in R^d with its 2d coordinate inequalities and add the ORIGINAL,
but redundant, displayed inequality

    sum_(j=0..d-1) 2^j x_j <= 2^d-1.

It is redundant because 0<=x_j<=1 and every coefficient is positive. The original
H-system still equals the convex hull of all 0/1 vertices. Choose u=0 and v=1.
The initially missing target labels are d coordinate upper bounds plus the extra
row. Every coordinate upper row has two actual vertex values. The extra row has
2^d distinct values, by uniqueness and completeness of binary expansion.

The old all-missing sum is d+2^d-1. Selecting the d coordinate upper rows yields
an identity matrix, hence a determining set of cost d. Any determining set has
at least d labels since the initially shared set is empty. Every missing label
has weight at least one, so d is the minimum possible weight. A coordinate-flip
route has d genuine original edges, preserving every acquired target row.
The extra row, despite its exponential inventory, is not charged.

The explicit large checks use dimensions 8,16,32,64 and all 2d+1 displayed rows.
In dimension64 the selected weight and constructed route are64, whereas the
all-missing sum is18446744073709551679. The level count is a binary-expansion
formula, not enumeration of 2^64 vertices. Whole edges are certified by fixing
all coordinates except the one changing coordinate with ORIGINAL supporting
rows. The full product H/hull and level interpretation is a WRITTEN application,
not an additional Lean instance theorem. The extra inequality is explicitly
REDUNDANT; this is not an irredundant-facet exponential lower-bound example.
Small nonsimple nonredundant examples, including the octahedron, separately
exercise reductions in the number of selected target labels.

## Source reuse, verification and provenance

The #329 namespace prefix (972 lines/41010 bytes) is reused byte-for-byte,
omitting its public root and old print requests. The directions helper and
small_active_rows proof are copied byte-for-byte from accepted #325 (458 and
2219 bytes). They are not new assumptions and their accepted targets are not
resubmitted. Both sets of five frozen manifest-file hashes were checked.
The new public target has Mathlib-only types, explicit classical finite filters
and an imports/open/options-only preamble. It matches the top-level solution
exactly. Eight requested transitive reports cover the retained selector and
new selection, accounting, route, bound and public-root proofs.

Local lean/lake/elan and checked home/workspace/opt locations were unavailable;
current toolchain-host DNS returned no addresses. Static source matching and
exact tests are NOT Lean compilation. The complete candidate is prepared for
one ordinary pinned compiler/axiom/publication gate. Preserve an actual failure
and any uncompiled repair rather than using repeated speculative hosted edits.
Keep Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.7,
all duplicate guards and verifier/publisher credential isolation unchanged.

The mathematics is classical finite-dimensional row-space selection and finite
minimization composed with the accepted original-edge geometry. No historical
priority or best-known general diameter bound is claimed. The mission still
requires uniform original-input control beyond potentially large level weights.

## Executed exact supporting checks

The small suite covers19 original-H hulls and701 endpoint routes, with4171 valid
determining candidates checked. The independent consumer enumerates all candidate
bitmasks, reconstructs original row ranks and actual vertex-value sets, checks
minimum weight, and verifies every selected phase and whole original edge slice.
Serialized certificates replay with selection, route and edge producers disabled.

The suite constructs817 original-edge occurrences versus816 total shortest edges;
the one nonshortest result,37 multi-edge phases and18 nonacquiring steps remain.
351 endpoint cases have strictly smaller budgets than the all-missing sum.
Ten malformed controls are rejected. Four larger cube-family cases certify120
further original edges without full graph or vertex enumeration and reject four
additional malformed controls. These are supporting arithmetic checks, not
Lean-extracted Python, a verified parser or an all-real proof by sampling.
