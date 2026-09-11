# Circuit deletion savings: hosted verification receipt — 2026-09-11

The exact carrier-deletion savings module, already merged through PR #122, has now also passed an ordinary hosted repository build and axiom audit.

## Hosted verification

- Verification branch head: `9aab12d1fdcbfa8479ecf232fc9e8b0adfa9fe71`.
- Actions run: `34637525943`.
- Job: `103388953563`.
- Lean: `v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Artifact: `10278162997`, `circuit-deletion-savings-hosted-verification`.
- Artifact SHA-256: `b7363521e507c02d840ce211f09bafaffe268224b8eca0baf28f52e3340af3fd`.
- Result: **success**.

The job ran a normal

`lake build Solutions.PolynomialCircuitDeletionSavings`

followed by direct Lean execution of the source file and the repository axiom checker.

All four audited declarations compiled and reported only `propext`, `Classical.choice`, and `Quot.sound`:

1. `HirschCircuitLocalization.rowCircuit_selected_defect_le_discarded_neutral_of_bounded`
2. `HirschCircuitLocalization.rowCircuit_selected_excess_defect_savings_identity_of_bounded`
3. `HirschCircuitLocalization.rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded`
4. `HirschCircuitLocalization.rowCircuit_selected_budget_saturated_iff_of_bounded`

This complements the earlier source-faithful offline standalone verification recorded in `research/CIRCUIT_DELETION_SAVINGS_VERIFICATION_2026-09-11.md`; the theorem source is now supported by both verification routes.

## Mathematical content

For a bounded parent, feasible source checkpoint, ambient row-circuit displacement, and selected effective row set `F` with carrier dimension `h ≤ |F|`, the strongest theorem gives the exact decomposition

`e + delta + kappa + s + tau = n - d`,

where `e=|F|-h`, `delta` is selected neutral-rank defect, `kappa` is surplus row disappearance, `s` is the number of omitted nonneutral effective rows, and `tau` is omitted neutral-row redundancy beyond actual rank loss.

This remains a static one-carrier accounting theorem. The exact regression families in the longer research note show that positive savings need not telescope across a walk, so this receipt does not claim a whole-walk ordinary-edge bound.
