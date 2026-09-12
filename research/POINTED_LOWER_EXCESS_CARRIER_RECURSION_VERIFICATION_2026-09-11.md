# Pointed lower-excess carrier recursion verification

Date: 2026-09-11.

Frozen theorem source commit: `d1c5d93a916dea43ae53b80a928a1d9ca993c3f3`.
Source SHA-256: `92f45288ab05a53bc5b36af183fc375b1bbdc29b42942388ade9d5d75d31bb73`.

Hosted final gate:
- run `34671787140`
- job `103494388746`
- artifact `10291014147`
- artifact digest `sha256:4beeb031a67b256c5a1da567f3571d76030c57d9de23ed8fc1b9ddd328aafb7c`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The gate checked the exact frozen source hash, compiled `Solutions.PolynomialPointedLowerExcessCarrierRecursion`, and axiom-audited its four public declarations. The reports contain only the repository-allowed standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschCircuitLocalization.commonFace_diamLE_of_minPresentationExcess_lt_of_injective`
- `HirschCircuitLocalization.feasible_sequence_edge_route_sum_of_strict_carriers_of_injective`
- `HirschCircuitLocalization.feasible_sequence_edge_route_mul_of_strict_carriers_of_injective`
- `HirschCircuitLocalization.rowCircuitStep_same_phase_recursive_or_essential_trapped_blocker_of_injective`

The result is conditional recursion, not a global diameter theorem: `LowerExcessInjectiveHpolyDiameterBound` remains a hypothesis. In particular the essential trapped-blocker equality branch and uniform fixed-degree polynomial accounting remain unresolved.
