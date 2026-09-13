# Exact finite allocation budgets from original-H primal/dual witnesses

This theorem isolates the final algebraic adapter between the already-Proved finite-allocation criterion and exact original-H support certificates.

Its premise `hpointwise` is exactly the form supplied by `Hirsch.finite_allocation_minkowski_criterion`: for a fixed finite multiplier family `c_s=(lambda_s,mu_s,nu_s)`, whole-set Minkowski reconstruction is equivalent to

`0 <= sum_i lambda_s,i * (b_i - a_i(x) - h_i) + nu_s*t`

for every original feasible `x` and every multiplier `s`.

Rearranging gives

`sum_i lambda_s,i*h_i - nu_s*t <= sum_i lambda_s,i*b_i - sum_i lambda_s,i*a_i(x)`.

For each `s`, this theorem additionally assumes nonnegative original-row weights `alpha_s` and an original feasible point `xstar_s`. The weights represent the same linear objective as `lambda_s`, and complementary slackness holds at `xstar_s`. Finite-row weak duality then bounds that objective at every feasible `x` by `sum_i alpha_s,i*b_i`; complementary slackness and feasibility show the bound is attained at `xstar_s`. Thus the universal pointwise inequality is equivalent to the single exact scalar budget

`sum_i lambda_s,i*h_i - nu_s*t <= sum_i lambda_s,i*b_i - sum_i alpha_s,i*b_i`.

The proof performs this argument independently for every member of the already-fixed finite family and rewrites through `hpointwise`. It is self-contained Mathlib code, so the repository axiom gate does not rely on `sorry`-bearing local stand-ins for platform theorems. Mathematically it is the direct adapter for the conclusions of accepted #219 and #221; neither accepted theorem is resubmitted or modified.

No boundedness, full dimensionality, simplicity, strict feasibility, Farkas sufficiency, or LP-solver correctness premise is introduced. The theorem does not construct the multiplier family, choose the primal/dual witnesses, prove an optimizer correct, establish executable circuit enumeration, discover a useful summand, route a residual polyhedron, or prove Polynomial Hirsch.

Applied to #219's fixed multiplier family, this theorem removes the remaining universal original-point quantifier whenever the #221-style support witnesses are available, leaving one explicit numerical packing inequality per multiplier.
