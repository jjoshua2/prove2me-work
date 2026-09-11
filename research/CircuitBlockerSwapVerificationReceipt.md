# Overlapping circuit-step blocker lemmas — verification receipt

Date: 2026-09-10/11 (America/New_York).

Verified mathematical source was checked out by the final gate at commit `8d598e1d2f6789fb2387e32175b3db007e080eaa`. The temporary verification commit differed from draft #64 only by an owner-only workflow trigger; the mathematical `Solutions/PolynomialCircuitStepCommutation.lean` blob is `2cc2e6630a9b5889184c70e712b0b4cb53921a3e`.

GitHub Actions verification:
- run `34552669988`
- job `103118630590`
- result: completed / success
- environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- artifact `10181451003`
- artifact digest `sha256:79775eaabdb0d73fcfb37d050cf239b4a53284ef05cf316b16e7e135d5fd9fea`

The gate reran all four exact regression suites and required fresh axiom reports for 30 reviewed declarations. All 30 reports passed and every transitive axiom set is contained in `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or other nonstandard axiom was reported.

The two newly verified declarations are:

1. `HirschCircuit.rowCircuitStep_of_feasible_of_tight_increasing_row`
2. `HirschCircuit.rowCircuitStep_swap_of_feasible_and_tight_blockers`

The second permits overlapping row supports: feasibility of the swapped point plus one tight increasing blocker for each swapped segment certifies preservation of both original circuit displacements and their maximality.

The exact blocker-swap regression contains 5,855 rational two-step cases on ten bounded models in dimensions 1--3; its committed output SHA-256 is `3caf7f0d5bac6db5f1cd1aec1bbd23543c50fd09e49e4e472a0cc652fb0de85c`. The checkpoint-localization suite also passed in the same final gate.

This receipt records kernel/source evidence only. It is not a Prove2Me publication receipt. The ordinary iff statement in `research/CircuitStepBlockerSwaps.md` is stronger than the two verified declarations until a separate Lean iff theorem is added and checked.
