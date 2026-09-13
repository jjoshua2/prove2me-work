# Finite allocation is accepted; remaining support and enumeration bridges

## Completed in PR #219

The exact bounded-allocation sufficiency target previously stated in this file
is now proved in `research/publication_packets/finite_allocation_minkowski/`.
Theorem `Hirsch.finite_allocation_minkowski_criterion`:
`09c33216-ba2f-4c9f-b75e-e9d8279e8358`.
Submission `f5304244-5800-46f7-b0c5-98cdf4c6d71a` is ACCEPTED; the trusted
publisher's authenticated live readback is Proved. Run34781016108 verified
proof head9d3aea2f4120f44a6c43b882d79c9f6f7fcb00c6.
Do not resubmit it, or accepted #216/#218.

For the original continuous row map a and generator map G, the proof chooses a
fixed finite family c_s in the nonnegative kernel of

    (lambda,mu,nu) |-> -G^T a^T lambda-mu+nu*1.

The family is chosen BEFORE the original RHS, scale, support bound and point.
For Delta_t={theta>=0:sum(theta)<=t}, Q_t=G(Delta_t), support bounds h on Q_t,
R={a(x)<=b}, and P={a(p)<=b-h}, the proved statement is

    R=P+Q_t iff for every x in R and every s,
    lambda_s.(b-a(x)-h)+nu_s*t >= 0.

Its full primal sufficiency is derived using compact separation from #216 and
an explicit weighted minimum on Delta_t, then composed with #218's finite
nonnegative-kernel tests. No Farkas sufficiency or allocation hypothesis is
inserted. Original R may be unbounded or lower-dimensional, and G need not be
injective. The support bounds h concern the SCALED candidate; for unscaled h0
substitute h=t*h0.

## Remaining original-H support-optimality bridge

For each chosen lambda, put f(x)=lambda.a(x). A feasible point x_star and
nonnegative original-row weights rho prove an exact maximum if

    sum rho_i*a_i = f,
    sum rho_i*b_i = f(x_star).

For any x in R, summing original inequalities proves f(x)<=sum rho_i*b_i.
Feasibility of x_star gives equality is attained, so a universal inequality
f(x)<=M on R is equivalent to f(x_star)<=M. Applying this to each chosen dual
multiplier removes the remaining universal x quantifier in #219 and yields
exact numerical packing budgets. Merely sufficient upper bounds must not be
labeled exact maxima. No original row may be dropped without a proved implication.

This is a focused next theorem, not an existing axiom or an already-formalized
optimizer. Inspect newer PRs before claiming it; another agent may be working
on the support-optimality step.

## Separate rank cutoff and enumerator correspondence

The accepted finite family is indexed by all supports, at most2^(m+k+1) slots.
It does not yet prove the executable rank-plus-one support cutoff. The explicit
injectivity proof in `FINITE_CIRCUIT_RANK_NEXT.md` is a mathematical next-step
note, not a Lean verification result. After the cutoff, connect rational
row-reduction output and normalized ray choices to the actual Circuit predicate.
Do not weaken support minimality or define circuits to include the desired bound.

Joint shapes require one allocation block each and the SAME shared scale vector.
Candidate discovery, residual route recognition, polynomial-size enumeration,
and uniform ordinary-edge cost on arbitrary carriers remain separate. Nothing
in this completed allocation result proves Polynomial Hirsch.
