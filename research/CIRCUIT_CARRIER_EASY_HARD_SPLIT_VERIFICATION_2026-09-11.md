# Circuit-carrier easy/hard split: verification receipt — 2026-09-11

## Verified source

- Candidate source branch: `formal/circuit-carrier-easy-hard-split`.
- Verified source commit: `b5253b566acabd4749504ac6b6f59ff98d4c6737`.
- Source file: `Solutions/PolynomialCircuitCarrierEasyHardSplit.lean`.
- Source blob: `af54895a5cc2939a95ee73446f8d81011a35d8e9`.
- Lean: `v4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Verification run: `34636072334`.
- Verification job: `103384150200`.
- Result: **success**.

The gate ran `lake build Solutions.PolynomialCircuitCarrierEasyHardSplit` and then `scripts/check_lean_axiom_log.py` for
`HirschCircuitLocalization.rowCircuit_commonFace_easy_cost_or_hard_neutral_defect`. The job succeeded, so the declaration compiled and passed the repository axiom policy (only the allowed logical axioms; no `sorryAx`).

## Statement and role

For a feasible row-circuit step in a bounded parent, let

`e = commonFaceMinSubpresentationCount - commonFaceDim`

be the minimum-presentation excess of its common carrier. Then either:

1. **easy:** `e ≤ 3`, and the intrinsic common-carrier graph has `DiamLE e`; or
2. **hard:** `e ≥ 4`, and for an effective minimum-presentation witness the remaining neutral-rank defect is at most `(n-d)-4`.

The proof uses the existing reference-free budget

`e + neutralDefect ≤ n-d`.

The failed first run `34634988759` was not a mathematical failure: its final `omega` saw definitionally equal common-face aliases and an opaque local `F` as separate arithmetic atoms. The repair names the public-vocabulary defect `D`, proves the exact budget in that vocabulary, converts the dimension alias once, and lets `omega` reason only about natural-number inequalities.

## Scope

This is a **per-step** resource dichotomy. It does not yet amortize high-excess carriers across a whole circuit walk and does not solve the d≥4 edge-refinement frontier. Its purpose is to make the remaining high-excess problem explicit: easy carriers already have exact graph cost, while every hard carrier has spent at least four units of the ambient excess/neutral-defect budget and therefore requires an order/persistence argument to charge repeated hard steps.
