# High-excess independent-row-block routing: hosted verification receipt

Date: 2026-09-11.

The theorem package merged through PR #132 has now passed a normal hosted repository verification under the pinned environment.

## Frozen theorem source

- Source PR: #132, `Formalize high-excess independent-row-block routing`.
- Source commit: `4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b`.
- Main theorem module: `Solutions/PolynomialRowBlockRouting.lean`.
- Source blob: `f410f77d854bf2853372492965d35561695f885b`.
- Product-walk dependency blob: `64e5977f9cd5fd9617b67e82f504550236d49b83`.
- Affine-transport dependency blob: `ada90a58fe876f5e0b31ec20a0f8c22b1c408dd1`.

The main theorem is

```text
HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
```

It gives an ordinary vertex-edge diameter bound `n-d` for a bounded nonempty `n`-row H-polyhedron in dimension `d` whenever an explicit invertible linear row-block certificate identifies the full presentation with independent factors and every factor has row excess at most three. Total excess and the number of factors are unrestricted.

## Hosted gate

- Verification PR: #134, `Verify high-excess independent-row-block routing on hosted Lean`.
- Verification head: `70155f1a9ba8676b189b3ecea6a036f47e1d2c72`.
- Actions run: `34642959632`.
- Job: `103406870271`.
- Lean: `v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- `lake build Solutions.PolynomialRowBlockRouting`: **success**.
- Direct Lean execution of `Solutions/PolynomialRowBlockRouting.lean`: **success**.
- Repository transitive axiom checker: **passed** for all four declarations.

Audited declarations:

```text
HirschRowBlocks.image_hpoly_eq_pi_of_row_blocks
HirschRowBlocks.factors_bounded_of_row_blocks
HirschRowBlocks.row_block_excess_sum
HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
```

Each reported only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axiom occurred.

Artifact:

- ID `10281280114`.
- Name `circuit-deletion-savings-hosted-verification`.
- Digest `sha256:c0a69c892d863bee8bb37bca0e17f6b02356e350db0d8cf7e3d3a9238f3b35d4`.
- Retention through 2026-09-25.

The hosted run also revalidated the shared deletion-savings and saturation layers present on that checkout; this receipt claims the row-block declarations above, not a new theorem about arbitrary carriers.

## Evidence boundary

This is now repository-grade Lean/kernel evidence. It is not by itself a Prove2Me ACCEPTED/Proved receipt. Publication should use a dependency-aware standalone theorem whose only Prove2Me theorem dependency is the already-Proved small-excess result `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` (`12426807-9602-4014-bd5e-c69fb43f4cb6`).

The result is a sufficient large-excess routing criterion. It does not assert that every saturated circuit carrier splits into such blocks. The remaining general Polynomial Hirsch edge-refinement frontier is therefore unchanged until a factorization/bypass theorem handles genuinely coupled residual blocks.
