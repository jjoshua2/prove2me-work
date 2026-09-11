# Maximal circuit-step carrier progress — verification receipt

Date: 2026-09-10/11 (America/New_York).

Exact source commit: `4ce691860d983c164f3088f6e69bd875d25d2d55`.
Source file: `Solutions/PolynomialCircuitStepProgress.lean`, Git blob `b812fa0aa253ab36daa4c20dd1a0f31c8a85c276`.

GitHub Actions verification:
- run `34551429080`
- job `103114973158`
- result: completed / success
- environment: Lean 4.30.0, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- artifact: `10180991168`
- artifact digest: `sha256:a41327a570b8f4f0c0d75c811bf06ba5a8f40d3c86a76cd776df9809e51f8aa2`

The gate compiled `Solutions.PolynomialCircuitStepProgress` and explicitly audited these five declarations:

1. `HirschCircuitLocalization.rowCircuitStep_exists_target_blocking_row`
2. `HirschCircuitLocalization.commonDirection_target_self_lt_of_rowCircuitStep`
3. `HirschCircuitLocalization.rowCircuitStep_target_commonFaceDim_lt`
4. `HirschCircuitLocalization.rowCircuitStep_commonFaceDim_source_bound`
5. `HirschCircuitLocalization.rowCircuitStep_target_commonFaceDim_progress`

Every reported transitive axiom set is contained in `{propext, Classical.choice, Quot.sound}`. No `sorryAx` or other nonstandard axiom was reported.

Mathematical content: maximality forces a destination-tight row increasing along the step; consequently the destination self-carrier is a strict subspace of the step carrier. Combining this with the already-verified nonvertex checkpoint localization gives

`commonFaceDim a b x y + d <= n + commonFaceDim a b x x`

and

`commonFaceDim a b y y + d + 1 <= n + commonFaceDim a b x x`.

Neither endpoint of the maximal circuit step is assumed to be a vertex. A separate reference extreme vertex of the same H-polyhedron is used for the circuit-neutral-rank input.

This receipt records source/kernel evidence only. It is not a Prove2Me publication receipt unless a later authenticated server verdict is appended separately.
