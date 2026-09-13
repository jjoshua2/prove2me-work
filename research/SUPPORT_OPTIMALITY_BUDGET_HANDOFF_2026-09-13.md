# Support-optimality budget handoff — 2026-09-13

The finite allocation/Minkowski sufficiency theorem from PR #219 is accepted and merged on `main` as `Hirsch.finite_allocation_minkowski_criterion` (theorem `09c33216-ba2f-4c9f-b75e-e9d8279e8358`, submission `f5304244-5800-46f7-b0c5-98cdf4c6d71a`). Do not resubmit it.

The next exact formal interface is now isolated in `research/publication_packets/primal_dual_support_budget/`.

For original rows `a_i(x)<=b_i`, a circuit coefficient family `lambda`, an explicit nonnegative support-dual family `alpha`, and a feasible point `xstar`, assume:

1. `alpha_i>=0`;
2. `xstar` satisfies all original rows;
3. the `lambda` and `alpha` row combinations define the same linear functional on every `x`;
4. complementary slackness: `alpha_i*(b_i-a_i(xstar))=0` for every row.

Then the remaining universal circuit budget

```
forall x in R,
  K <= sum_i lambda_i*b_i - sum_i lambda_i*a_i(x)
```

is equivalent to the single exact scalar budget

```
K <= sum_i lambda_i*b_i - sum_i alpha_i*b_i.
```

Mathematically this is just finite-row weak duality plus an attained complementary-slackness witness, but it is exactly the missing bridge between the accepted finite allocation theorem and the extractor's numerical packing inequalities.

The prepared proof packet is Mathlib-only and contains no custom statement definitions. This environment has no local Lean/Lake, so **no compilation claim is made**. The next agent with Lean should run the narrowest standalone compile/audit first. If it is green and the theorem name is still unused, publish once through the durable comment gate. If Lean rejects the proof, repair locally; do not use repeated speculative Actions runs.

This theorem deliberately does **not** choose or compute `alpha`/`xstar`, certify LP solver output, prove the rank-plus-one circuit support cutoff, certify executable circuit enumeration, discover useful finite summands, or route arbitrary residual carriers. Those remain separate obligations.

#210 is reserved to the other agent and should not be modified or triggered from this line without explicit reassignment. #208's existing pending/publication state should not be duplicated.
