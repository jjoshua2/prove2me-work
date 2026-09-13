# Proof idea

For each packing row `j` and coordinate `i`, nonnegativity of `Γ j i` together with `s i ≤ t i` gives

`Γ j i * s i ≤ Γ j i * t i`.

Summing these inequalities over `i` shows that the left-hand side for `s` is no larger than the already-feasible left-hand side for `t`. The assumed nonnegativity of `s` supplies the remaining part of feasibility.

The theorem is intentionally general. In the PR #210 application, the coordinates are candidate-summand scales and the rows are exact simultaneous extraction budgets. Thus the feasible scale set is a down-closed packing region.
