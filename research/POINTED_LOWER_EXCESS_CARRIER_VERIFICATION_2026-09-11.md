# Pointed lower-excess carrier recursion — verification

Research date: 2026-09-11 (America/New_York).
PR: #161.

- Frozen proof source: `d1c5d93a916dea43ae53b80a928a1d9ca993c3f3`.
- Source SHA-256: `92f45288ab05a53bc5b36af183fc375b1bbdc29b42942388ade9d5d75d31bb73`.
- Lean `v4.30.0`; Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Successful run: `34671787140`; job: `103494388746`.
- Artifact: `10291014147`, `pointed-lower-excess-carrier-verification`.
- Artifact ZIP SHA-256: `4beeb031a67b256c5a1da567f3571d76030c57d9de23ed8fc1b9ddd328aafb7c`.

The artifact was downloaded independently, its ZIP digest checked, and its source commit/hash checked against the frozen source. Compilation and all four requested transitive axiom reports passed on the first targeted run:

1. `HirschCircuitLocalization.commonFace_diamLE_of_minPresentationExcess_lt_of_injective`
2. `HirschCircuitLocalization.feasible_sequence_edge_route_sum_of_strict_carriers_of_injective`
3. `HirschCircuitLocalization.feasible_sequence_edge_route_mul_of_strict_carriers_of_injective`
4. `HirschCircuitLocalization.rowCircuitStep_same_phase_recursive_or_essential_trapped_blocker_of_injective`

Each declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The exact source and all dependencies compiled; no `sorryAx` was admitted.

This establishes the conditional pointed lower-excess carrier bound, weighted/uniform parent-edge assembly, and conditional same-phase edge-cost/trapped-blocker dichotomy. The induction hypothesis and hard blocker branch remain explicit. See `POINTED_LOWER_EXCESS_CARRIER_RECURSION_2026-09-11.md` for the mathematical boundaries, padding caveat, and global recurrence obligation.

Only one focused Lean gate was invoked. It used the shared pinned environment, ran on explicit ready-for-review rather than push/synchronize, and exposed no secrets. The temporary gate is removed before integration; documentation/cleanup does not alter proof source.

Platform status: GitHub-hosted Lean verification only. No Prove2Me registration, submission, or ACCEPTED verdict is claimed.
