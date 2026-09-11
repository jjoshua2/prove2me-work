# Saturated carrier blocker verification — 2026-09-11

## Kernel evidence

Integrated source commit: `c924702dd71cbc128f1f5b2542c70e99ae471988`.
Frozen proof source: `32acb19398a788152f9376314678986cd1def65b`.
GitHub Actions run: `34639305341`; job `103394807951`.
Artifact: `10279990359`, digest
`sha256:ca738893d59a0a00acda2c712ffbd6d6aad9cf6134357108681459933c5126ed`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The normal repository gate built
`Solutions.PolynomialCircuitSaturatedBlocker` successfully and axiom-audited:

1. `HirschCircuitLocalization.rowCircuit_saturated_selected_contains_effective_nonneutral`;
2. `HirschCircuitLocalization.rowCircuitStep_saturated_selected_target_blocker`;
3. `HirschCircuitLocalization.rowCircuitStep_saturated_selected_targetOnlyRow`.

Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; no
`sorryAx` or additional axiom occurs.

## Mathematical content

Let `F` be selected effective rows for a bounded-parent row-circuit carrier.
If

```text
(F.card-h) + selectedNeutralDefect = n-d,
```

then the exact deletion-savings inequality forces the omitted-nonneutral-row
saving to be zero. Hence **every effective row nonneutral on the circuit
displacement belongs to `F`**.

For a maximal `RowCircuitStep`, the existing step-progress theorem supplies a
nonzero row newly tight at the destination with positive displacement
evaluation. That row is effective and nonneutral, so saturation forces it into
`F`. Equivalently every saturated maximal step has a selected row in
`targetOnlyRows`.

This is a direct bridge from exact one-carrier accounting to ordered blocker
progress. It does not yet prove that the selected blocker persists into later
carrier presentations, is independently rank-increasing there, or gives a
polynomial ordinary-edge cost for the saturated block. Those are the next
routing questions.