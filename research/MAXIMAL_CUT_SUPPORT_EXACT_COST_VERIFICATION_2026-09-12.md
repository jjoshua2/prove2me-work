# Exact-cost maximum-support composition

[PR #199](https://github.com/jjoshua2/prove2me-work/pull/199) preserves the abstract
companion to the target-cone assembly integrated in #200. It returns an actual
route of cost `D + sum(local minimum-presentation excesses)` and proves that
this cost is at most `D + 3*(n-d)` when the selected chordless cut support has
cardinality `n-d`. Its inputs include the same selected face geometry, actual
cut pairs, and deferred route callback; `SmallExcessHpolyBound` remains the
explicit already-Proved classical input.

Frozen corrected source: `fe48faeec207416fdaa15eca7f5170d84ce1eff8`.
Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The original hosted run [34705928992](https://github.com/jjoshua2/prove2me-work/actions/runs/34705928992)
failed because line 76 used the undefined name `ClipRepairCutLeg`.
The correction uses the existing `RegionLeg` type. This fixes the theorem's
elaboration; it introduces no new mathematical assumption.

The corrected source passed `lake env lean Solutions/PolynomialMaximalCutSupportRouting.lean`
and the complete axiom audit for
`HirschMaxSupport.route_of_maximal_chordless_cut_support`, using only
`propext`, `Classical.choice`, and `Quot.sound`. The final targeted Lake build
and exact source hashes are recorded in
[the verification directory](verification/2026-09-12-maximal-exact-cost/).
The failed hosted run is not represented as a successful verification.
Its one-shot workflow is excluded from the integration.

This is local verification, not a new Prove2me acceptance. The target-rooted
linear/quadratic regimes and remaining joint high-carrier cost problem are
recorded in [the authoritative frontier](../STATUS.md).
