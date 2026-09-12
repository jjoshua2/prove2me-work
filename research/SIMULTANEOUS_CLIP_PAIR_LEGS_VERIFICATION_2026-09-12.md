# Pair-specific simultaneous clipping verification

Date: 2026-09-12.

Successful theorem head: `731412c39e0583aa0b8e4ebd153577bdafcfac93`.

Hosted verification:
- run `34692098231`
- job `103549049444`
- artifact `10298165276`
- artifact digest `sha256:daffb37a4583992ea9a330aa096f5f336568976aabdefd6875b7304d27418705`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialSimultaneousClipPairLegs` and transitive-axiom-audited all three requested declarations. Their reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschRadial.clipRepairPairCost_sum_eq_cut_add_old_length`
- `HirschRadial.route_clip_of_lifted_endpoints_with_pair_specific_cut_legs`
- `HirschRadial.route_clip_with_pair_specific_cut_legs`

Formal contribution: simultaneous clipping no longer needs one whole-face budget per cut. Each actual used cut leg retains its concrete parent-vertex entry/exit pair, both certified tight on that cut row, and may be charged by a pair-specific local cost `B i entry exit`. The mixed repair cost decomposes into those actual cut-leg costs plus one unit per distinct used old outer-edge label; duplicate-freeness bounds the latter by the supplied outer route budget `D`. The final route cost is therefore exactly controlled by `D + sum(pair-specific costs of actual used cut legs)` after padding.

Verification history: the first two runs exposed only list-projection elaboration issues in the bookkeeping lemmas. No theorem statement or geometry changed. The successful third run used explicit list-induction reductions; no credentials or Prove2Me mutation were involved.

This is a routing interface, not a polynomial bound on the pair-specific costs. The remaining research problem is to prove a globally amortized/decreasing resource for the actual cut-leg portal pairs, especially in the target-rooted endpoint-lift spoke. The one-shot verifier is removed before integration.
