# Saturated same-phase selected blocker verification — 2026-09-11

Frozen source commit: `64319ec1e9695cf05f02b1c95808fca63faade82`.
Hosted run: `34640923336`; job `103400069952`.
Artifact: `10279684868`, digest
`sha256:c6ddaf435805c193a201bdf5c79e1c5ef4fe07ba4f83b3668c2a02174abb62be`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The normal repository gate built
`Solutions.PolynomialCircuitSaturatedPhaseBlocker` successfully and axiom-audited

`HirschCircuitLocalization.rowCircuitStep_saturated_same_phase_selected_target_positive_blocker`.

Its transitive axiom closure contains only `propext`, `Classical.choice`, and
`Quot.sound`.

## Mathematical content

For a saturated selected presentation of a maximal row-circuit step `x -> y`,
assume the slack checkpoints at `x` and `y` remain in the same phase relative to
a feasible fixed final target `v`. Then there is a selected row `i` such that:

- `i` is target-only for the step;
- the row is strictly slack at `v`, equivalently target slack coordinate `i` is
  positive;
- `i` was already trapped at the phase reference:
  `r i <= M * slack(v) i`;
- its slack coordinate is positive at `x` and drops to zero at `y`.

The theorem combines the saturated selected-blocker result with the checked
same-phase zero-blocker persistence theorem from the cubic circuit-walk
construction. It is the first verified bridge from the exact carrier-saturation
resource to the actual phase order.

## Remaining gap

This theorem does **not** show that different saturated steps use distinct
blockers, that a selected blocker remains in later minimum carrier
presentations, or that the ordinary-edge cost of a saturated phase is
polynomially bounded. The next useful target must control recurrence/persistence
or turn the trapped selected blocker into an independently bounded face/section
routing cost.