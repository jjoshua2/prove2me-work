# Intrinsic excess-two whole-walk routing verification — 2026-09-11

## Kernel evidence

Frozen source commit: `dc6fea94d21e8cb62db0a1cd066b21696a88f4b9`.
GitHub Actions run: `34629982502`; job: `103364150810`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The gate ran

```text
lake build Solutions.PolynomialIntrinsicExcessTwoWholeWalkRouting
```

and completed all 8,514 jobs successfully. The axiom checker inspected 123 transitive `#print axioms` reports and found only `propext`, `Classical.choice`, and `Quot.sound`.

Required checked declarations:

1. `HirschCircuitLocalization.commonFace_has_subpresentation_dim_add_two_of_minCount_le`;
2. `HirschCircuitLocalization.feasible_sequence_edge_route_two_mul_of_minCounts`;
3. `HirschCircuitLocalization.rowCircuitWalk_edge_route_two_mul_of_uniform_minCount`.

## Mathematical content

This removes the global ambient assumption `n <= d+2` from the preceding whole-walk theorem.

For a bounded parent `Hpoly a b`, let

```text
M_i = commonFaceMinSubpresentationCount a b (w i) (w (i+1))
h_i = commonFaceDim a b (w i) (w (i+1)).
```

If a feasible checkpoint sequence `w 0,...,w L` has parent-vertex endpoints and every selected consecutive carrier satisfies

```text
M_i <= h_i + 2,
```

then there is a parent edge/stay route from `w 0` to `w L` with budget `2*L`. Intermediate checkpoints need not be vertices and the parent itself may have arbitrarily large row excess.

A second checked corollary states that if **every feasible common carrier** in a bounded parent satisfies the same intrinsic minimum-presentation bound, then every `RowCircuitWalk a b L u v` between parent vertices has a parent edge/stay refinement of length at most `2*L`.

The proof is a short composition:

- `commonFaceMinSubpresentation_spec` supplies an exact minimum-row witness;
- the inequality `M_i <= h_i+2` enlarges that witness to an `h_i+2` allowance;
- `commonFace_diamLE_two_of_subpresentation_at_most` gives intrinsic diameter at most two for each selected carrier;
- `route_of_feasible_commonFace_carrier_budgets` composes those local routes through nonvertex checkpoints.

The local theorem retains `SmallExcessHpolyBound` as an explicit logical premise. The corresponding small-excess diameter theorem is separately live Prove2Me `Proved`; this source does not conceal a theorem stub in its kernel closure.

## Frontier consequence

The routing/composition wrapper is no longer the bottleneck. The remaining mathematical problem is to prove or amortize intrinsic carrier bounds `M_i-h_i` for the actual circuit-walk checkpoints. The current minimum-subpresentation excess/defect theorem still assumes a vertex source; removing or correctly replacing that hypothesis is therefore the next structural target.
