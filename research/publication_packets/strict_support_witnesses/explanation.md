# Exact original-H support witnesses exist under strict feasibility

## Result and relation to the current project

Let P={x in R^d : a_i(x)<=b_i} be compact and let the supplied point o satisfy
ALL original inequalities strictly. For any real linear objective f, the
new theorem returns a feasible maximizer xstar and nonnegative original-row
weights alpha with

    f(x) = sum_i alpha_i*a_i(x)   for every x,
    f(xstar) = sum_i alpha_i*b_i,
    alpha_i*(b_i-a_i(xstar)) = 0  for every original row i.

The optimizer, dual weights, their exact objective value, and complementary
slackness are conclusions. They are not supplied hypotheses. This addresses
an existence assumption in the accepted primal/dual support-budget interfaces
#221/#227 and the distinct checked-covering composition in #236. It neither
reproves catalogue completeness nor duplicates that composition.

This is classical linear programming, not a historical novelty claim. The
project contribution is an explicit proof using the already-accepted covering
allocation alternative in a new role: allocation variables are now DUAL ROW
WEIGHTS. No general strong-duality or Farkas oracle is introduced.

## 1. A valid upper bound yields an original-row certificate

The main helper is stronger in a different direction than the public compact
statement. Suppose only that o is strictly feasible and f(x)<=M for every x in
P. P need not be bounded or compact. The helper constructs alpha>=0 such that
sum alpha_i*a_i=f and sum alpha_i*b_i<=M.

Write delta_i=b_i-a_i(o)>0 and R=sum_i 1/delta_i. For each i, R*delta_i>=1.
To obtain alpha, form the following finite inequality system in alpha:

    alpha>=0,
    sum_i alpha_i*a_i(e_j) <= f(e_j),
    -sum_i alpha_i*a_i(e_j) <= -f(e_j),
    sum_i alpha_i*b_i <= M,
    sum_i alpha_i*delta_i <= M-f(o).

The final inequality is the resource row for the accepted covering alternative
#234. The weight R gives its required coordinate coverage. The two opposite
coordinate rows enforce equality of the full linear objective. The explicit
Fin d + (Fin d + Fin 1) indexing and its bijection to Fin are handled in Lean;
no row-sum transport is assumed.

## 2. Every nonnegative null test of that system is valid

Let p,q be the nonnegative multipliers of the two coordinate-equality halves,
lambda the nonnegative multiplier of the cost row, nu the nonnegative resource
multiplier, and mu>=0 the nonnegativity multiplier. Put

    y=q-p,   eta=lambda+nu>=0.

The null equation in each alpha coordinate is

    -a_i(y)+lambda*b_i+nu*delta_i-mu_i=0.

Consequently a_i(y+nu*o)<=eta*b_i for every ORIGINAL row.

If eta>0, the point x=(y+nu*o)/eta is feasible. The assumed valid upper bound
f(x)<=M, multiplied by eta, gives

    eta*M-f(y)-nu*f(o)>=0.

This is exactly the right-hand-side pairing of the dual test.

If eta=0, nonnegativity gives lambda=nu=0 and a_i(y)<=0. The ray o+t*y is
feasible for every t>=0. A finite valid upper bound forces f(y)<=0: otherwise
choose t=(M-f(o)+1)/f(y) to exceed M. Hence the dual pairing -f(y) is again
nonnegative. This zero-scale case is proved separately; there is no division
by eta at zero and no tacit compactness assumption in the helper.

The accepted covering alternative now gives one actual feasible alpha. Its
coordinate equations extend to every x by finite linear expansion. Its cost
row supplies the stated upper certificate.

## 3. Compact attainment makes the certificate sharp

Strict feasibility makes P nonempty. Mathlib's extreme-value theorem
IsCompact.exists_isMaxOn gives xstar in P maximizing f. Apply the valid-bound
helper with M=f(xstar). Summing the ORIGINAL inequalities with alpha>=0 gives

    f(xstar)<=sum_i alpha_i*b_i<=f(xstar).

Thus equality holds. Every weighted slack alpha_i*(b_i-a_i(xstar)) is
nonnegative, and their finite sum is zero. Each weighted slack is therefore
zero. No active basis, simplicity, nondegeneracy, independent normals, rational
coefficients, or LP-solver correctness premise is needed.

## Boundaries and edge cases

Strict feasibility is an explicit sufficient condition on the full original
row presentation. It is NOT proved necessary for duality. The theorem does not
silently apply to lower-dimensional original presentations with no strict
point. Even a redundant row 0<=0 prevents this premise, whereas a zero row
0<b is allowed. Any later deletion or intrinsic-coordinate reduction must be
justified and its witnesses transported back to the original rows.

Empty coordinate and row types and the zero objective are retained. When d=0,
all linear objectives vanish. When m=0, the valid-bound helper forces f=0; the
compact public theorem excludes a positive-dimensional whole space through
its compactness hypothesis, not through an extra dimension restriction.

For a finite catalogue, apply this result to each row-combination objective to
obtain the support witnesses consumed by the allocation-budget adapter. This
is an existence theorem, not a verified rational optimization implementation
or a simultaneous noncomputable-family wrapper. It gives neither useful
summand discovery nor an ordinary-edge routing/Polynomial Hirsch bound.

## Source provenance and verification boundary

The standalone file incorporates the helper prefix of accepted #234, source
fb182322048816ba626cb6f1c821d4cb332224d3, original lines1-402. The transferred
copy joins one let declaration and inserts an explicit zero term in one row
expression, discharging that equality by simp. The original accepted packet
is not modified; helper statements and the mathematical argument are unchanged.
The new core has235 lines; the complete standalone file has659 lines. The public
statement uses only Mathlib symbols and an import/open-only preamble. Five
final transitive axiom printouts cover the new proof chain and solution.

The original dependency artifact10328760255 from run34790733652 was downloaded
and its archive digest and all frozen manifest hashes were recomputed. That
historical evidence proves the dependency compiled; it does NOT certify this
new file. The local environment has no Lean/Lake executable, so no local Lean
compilation is claimed. A prepared exact-head PR-comment gate must establish
compilation, axiom audit and authenticated publication as separate stages.

The standard-library rational regression checks48 bounded systems,1860 active
bases,180 independently matched vertices,336 optimal support certificates,
336 nonsharp valid bounds,1008 positive-eta transport cases,27 zero-eta recession
cases,9 unbounded support certificates and675 rejected controls. These executed
finite tests are NOT Lean verification. Reproducer:

    python scripts/check_strict_support_witnesses.py

Pinned dependency: Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f.
