# Hosted verification trigger: high-excess row-block routing

Verification-only branch for the already-merged `Solutions/PolynomialRowBlockRouting.lean` result from PR #132.

The source itself is unchanged. This branch exists only to run the repository's shared pinned Lean gate against current `main`, with a normal `lake build`, direct Lean execution, and transitive axiom audit of:

- `HirschRowBlocks.image_hpoly_eq_pi_of_row_blocks`
- `HirschRowBlocks.factors_bounded_of_row_blocks`
- `HirschRowBlocks.row_block_excess_sum`
- `HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks`

No credentials or Prove2Me mutation are part of this verification PR. Close unmerged after the hosted receipt is durable.
