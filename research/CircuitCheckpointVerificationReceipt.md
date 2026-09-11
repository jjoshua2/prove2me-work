# Circuit checkpoint localization — kernel verification receipt

Date: 2026-09-10/11 (America/New_York / UTC boundary).

## Frozen source and repair

The research package originated at draft PR #64, commit
`ae17119009aca095114c3f984010d368aace5708`. A verification-only branch added
no mathematical changes except one elaboration repair in
`Solutions/PolynomialCircuitStepCommutation.lean`: the final feasibility goal
is normalized with

```lean
simpa only [inner_add_right, inner_smul_right] using hi
```

The resulting mathematical source was verified at commit
`cd9507f1dc08bfea234e9963707fc68de2d1356f`.

## Exact gate

- GitHub Actions run: `34550443602`
- job: `103112037411`
- artifact: `10180667590` (`circuit-checkpoint-final`)
- artifact ZIP SHA-256 reported by Actions:
  `575b58f90f2c7c840a592eacf0d7f57d7d1b5bd86eed0504f195ff38fa9f521a`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The gate reran the carrier, ordering, and checkpoint exact regression
certificates, compiled the four targeted top-level modules, then generated a
fresh audit file from `research/circuit_checkpoint_required_axioms.txt`.
Exactly 28 requested declarations produced 28 fresh axiom reports. Every
report used only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`
or other assumption survived.

## Main mathematical content

The checked package includes:

- active-neutral row rank and defect criteria for when a maximal circuit step
  leaving a vertex is already an ordinary edge;
- the vertex-to-vertex corollary that row excess at most two forces a maximal
  circuit step to be an edge;
- nonvertex checkpoint localization with explicit source/target nullities and
  all-neutral direction defect, plus its row-circuit specialization;
- conditional routing of a feasible checkpoint sequence through intrinsic
  common-carrier diameter budgets; and
- commutation of consecutive maximal circuit steps under rowwise-separated
  (equivalently disjoint row-support) directions.

These results do **not** solve Polynomial Hirsch. They do not assert polynomial
common-carrier diameter budgets, and the current `d >= 4` circuit-to-edge
refinement theorem remains the sole formal Open frontier.

## Publication status

This receipt is only a source/kernel verification record. No theorem in this
checkpoint package is claimed Prove2Me Proved unless a later publication
receipt names its theorem ID, submission ID, and authenticated readback.
