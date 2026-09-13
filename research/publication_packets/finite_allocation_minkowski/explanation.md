# Finite null tests imply whole-set Minkowski allocation

## Exact statement and purpose

Let E be a real normed vector space, let a_1,...,a_m be continuous linear
functionals, and let G:R^k -> E be continuous linear. The theorem chooses one
finite family of nonnegative null multipliers c_s, depending ONLY on a and G,
before any right-hand side b, support bound h, scale t, or original point x.
The index type has m+k+1 elements and the family is indexed by its subsets.

For t>=0 let Delta_t={theta>=0:sum theta<=t}, Q_t=G(Delta_t),
R={x:a_i(x)<=b_i}, and P={p:a_i(p)<=b_i-h_i}. Assume h bounds each row on Q_t:
a_i(G theta)<=h_i for theta in Delta_t. Then

    R=P+Q_t

if and only if, for every original x in R and every chosen multiplier c_s,

    sum_i lambda_si (b_i-a_i(x)-h_i) + nu_s t >= 0.

Here c_s=(lambda_s,mu_s,nu_s) is nonnegative and satisfies

    -sum_i lambda_si a_i(G e_j)-mu_sj+nu_s=0  for every j.

The existence of the allocation theta is CONCLUDED from the finite tests; no
Farkas, feasible-allocation, circuit-generation, or diameter premise is assumed.
The displayed set on the right of the formal equality spells out p+G theta
and the allocation bounds, avoiding statement-preamble custom definitions.

The support bound h already concerns the scaled candidate. For the usual
unscaled support vector h0, substitute h=t*h0. The map G need not be injective:
dependent, duplicate, or zero generators are included. Empty original sets,
zero constraints, zero allocation coordinates, and t=0 are included. Neither
boundedness, full dimensionality, strict feasibility, nor simplicity of R is
required. The conclusion does not assert a new ordinary-edge diameter bound.

## 1. The compact feasibility lemma reused from accepted #216

The source inlines the exact compact separation helper used in the accepted
compact-dual packet. For compact convex Q and finitely many continuous linear
functions, simultaneous feasibility is equivalent to satisfying all nonnegative
weighted tests, with a possibly different point of Q for each test.

The proof maps Q to its vector of slacks. If this compact convex image misses
the closed nonnegative orthant, Mathlib's geometric separation theorem supplies
a separating linear functional. Nonnegativity on the orthant makes every
coordinate weight nonnegative, contradicting the weighted tests. This is a
classical compact separation consequence, not a new unexplained axiom.

Reference proof: PR #216; theorem a6e2a38d-00e3-46d6-b232-7cddee5e30e1;
accepted submission 2976ce68-c33c-4cab-b48e-8a7f46be211a, source commit
115b3ede788bca52bcac568d1aa05e62a0d92559. The helper is included verbatim;
no duplicate publication of that theorem is requested.

## 2. NEW: derive the full bounded allocation alternative

For arbitrary B:R^k->R^m and rhs d, the primal statement is

    theta>=0, sum theta<=t, B theta<=d.

Necessity of the dual test follows by summing inequalities with multipliers
lambda>=0, mu>=0, nu>=0 and B^T lambda-mu+nu*1=0.

For sufficiency, fix lambda>=0 and write r=B^T lambda. Set

    nu=max(0, max_j(-r_j)),   mu_j=r_j+nu.

The smallest weighted objective on Delta_t is exactly -nu*t. A minimizer is
0 if nu=0, or t*e_j at a coordinate attaining r_j=-nu. The proof uses an Option
index, with none representing 0, so k=0 needs no hidden nonemptiness assumption.
The full dual hypothesis gives lambda.d+nu*t>=0, so this explicit point passes
the corresponding compact-feasibility weighted test. The compact helper then
returns ONE theta satisfying every inequality simultaneously.

This proves the complete alternative, including its sufficiency direction,
without proving closedness of an arbitrary finitely generated cone. Compactness
is provided by the built-in nonnegative simplex budget, not assumed for R.

## 3. The finite family reused from accepted #218

Apply the accepted finite-test construction to the linear map

    (lambda,mu,nu) |-> B^T lambda-mu+nu*1.

Its circuit family is chosen before d or t. Nonnegativity of the linear test
(lambda,mu,nu) |-> lambda.d+nu*t on that finite family is equivalent to its
nonnegativity on the entire nonnegative kernel. Combining this with Section 2
proves actual primal feasibility from finitely many tests.

Reference proof: PR #218; theorem 8f3c4cc7-be73-4ecf-9e17-816c710e20d7;
accepted submission 3fd7936c-8271-4a24-b342-d60bfd29529f. The source generalizes
only its finite coordinate index from Fin n to an arbitrary finite type, so
Fin m plus Option(Fin k) can be used without cumbersome reindexing. Its minimum
ratio, support descent, same-support-ray, and finite-family proof steps are
otherwise unchanged. This is self-contained reuse with explicit provenance,
not an axiom importing an open theorem or a new submission of #218.

## 4. NEW: the full original-polyhedron equality

Use B_i(theta)=-a_i(G theta), d_i(x)=b_i-a_i(x)-h_i. Then

    B theta<=d(x), theta in Delta_t

is exactly the assertion x-G theta in P. The preceding finite criterion gives
R subset P+Q_t. Conversely, for p in P and theta in Delta_t, add the two original
row inequalities for p and G theta to get p+G theta in R. This proves equality
of complete sets, not reconstruction only at sampled vertices.

## What remains outside this result

The family is finite because it has one slot per support, at most 2^(m+k+1).
The sharper rank-plus-one cutoff and correctness of the executable circuit
enumerator remain separate formalization tasks. No polynomial enumeration
claim is made. The remaining universal x in R still needs certified primal/dual
support optimization to become the numerical packing budgets of the extractor.
Useful candidate discovery and arbitrary residual edge routing remain separate.
This is not a proof of Polynomial Hirsch or a cosmetic root-graph dependency.

## Verification status

At preparation time no local Lean executable is available in this container;
no local compile or axiom result is claimed. The packet is prepared for one
isolated compile/audit/publication gate, not a repeated hosted edit loop.
The independent rational regression checks 280 bounded-allocation instances
using Fourier--Motzkin elimination versus separately generated positive null
rays, 1,127 circuit tests, 280 explicit weighted minima, and five rejected
malformed witnesses. Those are arithmetic regressions, NOT Lean verification.
Only an authenticated workflow/platform verdict can change this status.
