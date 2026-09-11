# Circuit-step savings dichotomy verification — 2026-09-11

Frozen source commit: `cf04e739529cce939dd8bbd1016a4e5fd7737dfd`.
Hosted run: `34641254896`; job `103401169922`.
Artifact: `10280232630`, digest
`sha256:5d9ced4804855fd096154a419a9d58358c383591de5fd3c9c58eadbf90078d80`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The normal repository gate built
`Solutions.PolynomialCircuitStepSavingsDichotomy` successfully and axiom-audited:

1. `HirschCircuitLocalization.rowCircuitStep_selected_strict_budget_or_targetOnlyRow`;
2. `HirschCircuitLocalization.rowCircuitStep_minPresentation_strict_budget_or_selected_targetOnlyRow`.

Both transitive axiom closures contain only `propext`, `Classical.choice`, and
`Quot.sound`.

## Mathematical content

For any selected effective row set `F` on a maximal row-circuit step, with at
least the common-carrier dimension many rows, one of two alternatives holds:

```text
selected presentation excess + selected neutral-rank defect < n-d,
```

or some selected row is in `targetOnlyRows` for the step.

The proof combines the exact deletion-savings inequality with the saturated
selected-blocker theorem: if the scalar resource is not strict, the resource
inequality forces equality, and saturation supplies the selected target-only
row.

The second declaration specializes this to an **actual minimum equivalent
common-carrier presentation**.  It returns one minimum witness and preserves
that same witness in the dichotomy, rather than changing presentations between
cases.

## Scope

This removes an equality side-condition from downstream progress arguments, but
it is still a one-step statement.  Strict scalar slack is not known to telescope
across a walk, and the selected target-only blocker is not yet known to remain
selected or tight over a later carrier interval.  The verified same-phase
blocker bridge separately shows what saturation implies inside the cubic
circuit-walk phase structure.