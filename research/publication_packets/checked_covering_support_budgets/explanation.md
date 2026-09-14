# Actual checked output to exact covering-allocation Minkowski budgets

## Result and scope

Let R={x:a_i(x)<=b_i}. Let G map k nonnegative allocation coordinates into the
original d-dimensional space. Keep ALL budget rows B_q(theta)<=t_q, and define
Q(t)={G(theta):theta>=0,B(theta)<=t}. The candidate can represent several
independently scaled finite hulls; overlapping or signed budgets are also
allowed, but those more general candidates are not automatically sums of
independent shapes.

The theorem binds the actual rational checked matrix to (-aG,-I,B), proves
that its emitted catalogue tests simultaneous allocation, constructs the
whole-set decomposition, and eliminates the universal original-point test
using exact original-H support witnesses. Its conclusion is

    R = {p:a_i(p)<=b_i-h_i} + Q(t)
      iff
    for every ACTUAL emitted c,
      lambda_c.h - nu_c.t <= lambda_c.b - alpha_c.b.

Here lambda_c and nu_c are the original-row and budget-row coordinates of c.
The public theorem assumes a passing finite Boolean check and finite witness
identities, NOT catalogue completeness, a Farkas theorem, or the desired
pointwise allocation/decomposition equivalence. It derives those implications
from the accepted #233 and #234 proof bodies. This is a formal composition of
classical duality, not a claim of a new classical theorem or Polynomial Hirsch.

## Exact inputs

1. An explicit bijection e between original/nonnegative/budget row indices and
   Fin n, and finite coordinate identities identifying the rational matrix M
   with the transpose of (-aG,-I,B). Every row and its sign is retained.
2. The same rational tag, left-inverse and zero-mass-null-witness table as
   accepted #229. Its Boolean checks every support through cardinality k+1;
   its output is the actual rational Finset in the public statement.
3. Nonnegative coverage rho with sum_q rho_q B_q(e_j)>=1 for each allocation
   coordinate j. This bounds allocation mass and permits accepted #234's
   covering alternative. No strict feasibility or full-rank assumption.
4. Nonnegative envelope weights eta_iq satisfying the FINITE inequalities

       a_i(G(e_j)) <= sum_q eta_iq B_q(e_j),
       sum_q eta_iq t_q <= h_i.

   These imply a_i(G(theta))<=h_i for EVERY feasible allocation. That universal
   candidate-support assertion is proved internally, not supplied publicly.
5. For each emitted c, a nonnegative original-row multiplier alpha_c and an
   original-feasible point xstar_c, with coordinate objective identities

       sum_i lambda_ci a_i(e_j) = sum_i alpha_ci a_i(e_j)

   and complementary slackness alpha_ci*(b_i-a_i(xstar_c))=0.
   These prove an EXACT support value, not a possibly loose dual upper bound.

The original polyhedron need not be bounded or full-dimensional. Generators
may be dependent. Budgets and right sides can have either sign whenever the
explicit coverage/envelope hypotheses hold. Degenerate and zero-coordinate
cases are retained. Supplied maximizing witnesses are an actual limitation:
the proof does not discover them or claim they exist for every input.

## Proof chain

### Binding and transport

`encoded_kernel` uses the explicit row bijection to split a real matrix-null
vector into (lambda,mu,nu) and establish

    (-aG)^T lambda - mu + B^T nu = 0.

`testForm` transports the RHS pairing to lambda.b+nu.t. Conversely the same
bijection combines ANY actual multiplier triple into a real vector tested by
M. Thus no null vector or budget coordinate is silently omitted during
reindexing. The rational coefficient identities are used over arbitrary real
weights, not just over rational samples.

### Checked output implies actual allocation

Accepted #233 proves that passing every emitted-circuit test is equivalent to
passing all nonnegative real null-vector tests. Accepted #234 converts those
actual-row tests to existence of one nonnegative allocation satisfying all
original and budget constraints at once. The new `checked_allocation` composes
those results without an additional semantic completeness or feasibility input.
Its catalogue is fixed by M,tag,L; right sides may vary without rerunning the
catalogue construction.

### From an allocation to whole-set equality

For an original point x, use RHS b-a(x)-h in the original allocation block.
The actual allocation theta gives p=x-G(theta) with a(p)<=b-h. Conversely the
finite eta certificate proves support on Q(t), so p+G(theta) satisfies all
original inequalities. `checked_minkowski` proves the whole equality, not a
sampled-point criterion. Its internal support premise is discharged by
`support_from_budget` in the public result.

### Exact scalar budgets

The finite coordinate identities extend to objective equality on every real
original point. Nonnegative alpha bounds that objective above by alpha.b;
feasibility and complementarity at xstar attain the same bound. Applying the
pointwise criterion there gives necessity of the scalar budget. The same
upper bound proves sufficiency for EVERY original point. No universal x
quantifier remains in the final test, and a merely sufficient support bound
is never called an exact maximum.

## Reuse and provenance

The standalone source reuses the accepted helper bodies from downloaded
verified artifacts for #233 (run34790147221) and #234 (run34790733652).
Their archive digests and all frozen hashes were independently checked. The
source retains their definitions and proof bodies, removes their former root
solution wrappers, and adds the new namespace Hirsch.CheckedCovering and one
fully inlined top-level theorem solution. The public preamble is imports/opens
only; the statement introduces no locally redeclared custom type identities.

This replaces the old uncompiled 1170-line single-simplex composition as the
next verification target; that earlier candidate is NOT also submitted.
#235's independent sign/zero-pattern theorem is a different obligation and
is neither changed nor assumed. Accepted #233/#234 are not resubmitted.

## Independent exact regression

The new test reuses the #229 rational catalogue auditor unchanged. Seven
models cover independent segments, the competing triangle/square hexagon,
an empty allocation block, dependent generators, overlapping resource caps,
a signed-budget trapezoid and zero allocation coordinates. Original vertices
and support multipliers are recovered independently with exact rational
linear algebra. Allocation feasibility uses independent Fourier--Motzkin.

The executed suite checks 14 row permutations, 200 whole-set/scalar-region
comparisons, 720 original-vertex allocations, 720 candidate-support row
certificates, 114 sharp original support certificates, and 7472 null/RHS
transport identities. Ten negative controls reject omitted obstructions,
wrong row bindings, a false bijection, forgotten RHS permutation, negative
or inadequate envelope weights, false candidate bounds, and incorrect
original support witnesses. A full hexagon instance and its table/witnesses
are in the downloadable fixture. These are Python tests, NOT Lean verification
of the generic theorem or individually kernel-evaluated geometric instances.

The existing helper test_covering_allocation.py remains a bundled test
dependency. This packet does not claim that all companion scripts are already
on main. The new regression and its executed receipt are preserved separately
from the public proof's frozen bytes.

## Verification boundary and remaining mathematical work

The originating container has no Lean/Lake and cannot resolve the toolchain
host. Source-integrity checks and the successful Python regression are not
compilation. Six final axiom printouts target the new helpers and root proof;
only the actual pinned gate and authenticated publication receipt can establish
verification/acceptance. No proof admission, native_decide or new axiom occurs.

This theorem does not verify a Python/JSON parser or find a short original-edge
route. A generic checker theorem also does not certify arbitrary JSON without
instantiating its finite data and proving the check passes. Enumeration remains
polynomial only at fixed allocation dimension, not for unrestricted k. Useful
universal candidate selection and arbitrary residual ordinary-edge routing
remain separate. A full joint packing theorem may additionally use #235's
coefficient-sign result; this criterion does not assume those signs.
