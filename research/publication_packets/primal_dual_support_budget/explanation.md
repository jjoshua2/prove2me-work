# Exact support budgets from primal/dual witnesses

## Purpose

The accepted `Hirsch.finite_allocation_minkowski_criterion` reduces whole-set
Minkowski reconstruction to finitely many inequalities that still quantify over
every original feasible point `x`. For one circuit multiplier `lambda`, the
remaining term has the form

    K <= lambda·b - lambda·a(x)    for every x with a(x)<=b.

The present theorem removes that universal `x` once an exact support optimum is
certified by an ordinary primal/dual witness.

## Statement

Let `alpha` be nonnegative, let `xstar` satisfy every original row, and assume
`alpha` represents the same linear objective as `lambda`:

    sum_i lambda_i a_i(x) = sum_i alpha_i a_i(x)   for every x.

Assume complementary slackness at the feasible point `xstar`:

    alpha_i * (b_i - a_i(xstar)) = 0   for every i.

Then

    [forall feasible x, K <= lambda·b - lambda·a(x)]

is equivalent to the single scalar inequality

    K <= lambda·b - alpha·b.

Thus the exact support value of the `lambda` objective is `alpha·b`, witnessed
attainably by `xstar`.

## Proof

Complementary slackness gives termwise

    alpha_i a_i(xstar) = alpha_i b_i,

so the objective value at `xstar` is exactly `alpha·b`. For any other feasible
`x`, nonnegativity of `alpha` lets us multiply each row inequality
`a_i(x)<=b_i` and sum, giving

    alpha·a(x) <= alpha·b.

The pointwise objective identity transfers this to the `lambda` objective, so
`xstar` is a true maximizer. The forward budget implication specializes the
universal inequality to `xstar`; the reverse implication combines the scalar
budget with the summed row bound.

No compactness, boundedness, full dimensionality, strict feasibility, simplex
assumption, Farkas theorem, LP duality theorem, or optimization oracle is used.
The dual certificate is explicit input.

## Relation to the Polynomial Hirsch work

For the finite allocation criterion, a positive circuit supplies `lambda` and
an objective `v=lambda*A`. An independently certified support optimum may use a
different nonnegative multiplier `alpha` satisfying `alpha*A=v`. A feasible
sharp point plus complementary slackness then turns the circuit's remaining
universal test into the exact numerical budget

    lambda·b - alpha·b.

This is the formal bridge needed before the extractor's circuit inequalities
can become finite packing constraints with certified RHS values. It does not
choose the witness `alpha`, prove an LP algorithm, certify the executable
circuit enumerator, prove a rank-plus-one circuit cutoff, or route arbitrary
residual carriers.

## Verification status

This environment has no local Lean executable. The proof is intentionally
small and Mathlib-only, but no compile or axiom claim is made yet. Do not
publish until a targeted Lean compile and standard-axiom audit are observed.
