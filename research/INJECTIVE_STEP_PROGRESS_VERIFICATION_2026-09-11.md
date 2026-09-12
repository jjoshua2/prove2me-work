# Hosted verification: injective checkpoint localization and maximal-step progress

Date: 2026-09-11 (America/New_York)

## Frozen proof source

- branch: `formal/injective-step-progress`
- proof source commit: `3e9caa7861098c7e967cd2d49c9b194cb0c0616e`
- workflow run: `34667346123`
- job: `103481841580`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

Artifact:

- id: `10289079777`
- name: `injective-step-progress-verification`
- digest: `sha256:483278e5205b9bfbf778faaf03b76635c01f8b638041e691864e972bd93bfc69`

## Result

All three candidate modules built successfully:

- `Solutions.PolynomialCircuitInjectiveCheckpointLocalization`
- `Solutions.PolynomialCircuitInjectiveStepProgress`
- `Solutions.PolynomialOneRowDeletionStepProgress`

The focused axiom audit checked all six public declarations and found only the accepted logical axioms `propext`, `Classical.choice`, and `Quot.sound`:

1. `HirschCircuitLocalization.directionNeutralDefect_eq_zero_of_rowCircuit_of_injective`
2. `HirschCircuitLocalization.rowCircuit_commonFaceDim_checkpoint_localization_of_injective`
3. `HirschCircuitLocalization.rowCircuitStep_commonFaceDim_source_bound_of_injective`
4. `HirschCircuitLocalization.rowCircuitStep_target_commonFaceDim_progress_of_injective`
5. `HirschDeletion.rowCircuitStep_commonFaceDim_source_bound_of_one_row_deletion`
6. `HirschDeletion.rowCircuitStep_target_commonFaceDim_progress_of_one_row_deletion`

The audit script reported:

`Axiom audit passed: 6 required declarations; 6 reports checked; only standard logical axioms.`

## Mathematical result

For any finite row presentation with injective row-evaluation map, a row circuit has zero all-neutral defect and satisfies the sharp nonvertex checkpoint-localization inequality

`2 * commonFaceDim(x,y) + d <= n + commonFaceDim(x,x) + commonFaceDim(y,y) + 1`.

For a maximal feasible row-circuit step, the already-verified strict destination-self-face drop yields

`commonFaceDim(x,y) + d <= n + commonFaceDim(x,x)`

and

`commonFaceDim(y,y) + d + 1 <= n + commonFaceDim(x,x)`.

The canonical one-row deletion presentation inherits row-map injectivity from its bounded parent, so both maximal-step inequalities apply directly in that potentially unbounded deletion outer.

Together with the cubic deletion-outer circuit walk and injective defect accounting, boundedness is no longer needed for the circuit localization/progress layer. Ordinary edge refinement remains the substantive unresolved dynamic step.

No Prove2Me publication or mutation was performed by this verification run.
