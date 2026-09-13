# Exact finite allocation budgets from original-H primal/dual witnesses

This theorem composes two already-Proved interfaces without weakening either one.

`Hirsch.finite_allocation_minkowski_criterion` chooses a fixed finite family of nonnegative null multipliers for the allocation system associated to the original row family and generator map. For each multiplier `s`, write its original-row coordinates as `lambda_s` and its allocation-total coordinate as `nu_s`. Its accepted criterion says that whole-set Minkowski reconstruction is equivalent to the pointwise tests

`0 <= sum_i lambda_s,i * (b_i - a_i(x) - h_i) + nu_s*t`

for every original feasible `x` and every fixed multiplier `s`.

Rearranging gives

`sum_i lambda_s,i*h_i - nu_s*t <= sum_i lambda_s,i*b_i - sum_i lambda_s,i*a_i(x)`.

For each `s`, the hypotheses of this theorem supply nonnegative original-row weights `alpha_s` and an original feasible point `xstar_s`. The weights represent the same linear objective as `lambda_s`, and complementary slackness holds at `xstar_s`. The accepted theorem `Hirsch.primal_dual_support_budget_exact` therefore turns the universal inequality over every feasible `x` into the exact scalar inequality

`sum_i lambda_s,i*h_i - nu_s*t <= sum_i lambda_s,i*b_i - sum_i alpha_s,i*b_i`.

Applying that equivalence independently to every member of the already-fixed finite allocation family yields the displayed finite scalar criterion for whole-set Minkowski reconstruction.

No boundedness, full dimensionality, simplicity, strict feasibility, Farkas sufficiency, or LP-solver correctness premise is introduced. The original H-polyhedron may be unbounded or lower-dimensional and `G` need not be injective. The support bounds `h` concern the scaled candidate at scale `t`, exactly as in the accepted finite-allocation theorem.

The theorem deliberately does not choose the primal/dual support witnesses, prove that an external optimizer computed them correctly, establish executable circuit enumeration, discover a useful summand, route a residual polyhedron, or prove Polynomial Hirsch. Its role is narrower: once exact support witnesses are available, the remaining universal original-point quantifier is eliminated and the finite allocation criterion becomes a finite family of explicit scalar packing budgets.

The submitted proof imports the two accepted Prove2Me theorems as platform dependencies. Local repository stubs reproduce their frozen formal statements solely so the same source can be compiled by the repository's pinned Lean environment before publication. Neither accepted dependency is resubmitted or modified.
