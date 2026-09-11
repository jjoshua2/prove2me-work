# Excess-two whole-walk routing verification — 2026-09-11

## Kernel result

Verification-only source commit: `2935f42d255029dcbc337c953dbb364d71ef1c94`.
GitHub Actions run: `34629152760`; job: `103361465979`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
Exact source blob: `Solutions/PolynomialExcessTwoWholeWalkRouting.lean` SHA-1 `93f0fd01cb13c95b9c9c7630d9fbce1cb85a1a7a`.

`lake build Solutions.PolynomialExcessTwoWholeWalkRouting` completed successfully. The required three declarations were present and the axiom checker inspected 120 printed reports; every report used only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`.

Required declarations:

1. `HirschCircuitLocalization.hpoly_isClosed`;
2. `HirschCircuitLocalization.feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two`;
3. `HirschCircuitLocalization.rowCircuitWalk_edge_route_two_mul_of_rows_le_dim_add_two`.

The build also compiled the previously candidate-only `Solutions/PolynomialCircuitCarrierRouting.lean`; its own printed reports for `commonFace_isClosed_of_compact_parent` and `route_of_feasible_commonFace_carrier_budgets` appeared in the successful all-standard-axiom log.

## Mathematical content

Assume a bounded `n`-row H-polyhedron in ambient dimension `d` with `n <= d+2`, and assume the small-excess H-polyhedron theorem through the explicit `SmallExcessHpolyBound` logical premise.

For any feasible checkpoint sequence `w 0, ..., w L` whose endpoints are parent vertices, the common carrier of every consecutive pair has intrinsic graph diameter at most two. The checked feasible-face-cover routing theorem then gives a parent edge/stay route of length at most

```text
2 * L.
```

The interior checkpoints need not be vertices and the output route need not visit them.

The row-circuit corollary therefore says any `RowCircuitWalk a b L u v` between parent vertices in the same ambient excess-two regime admits an ordinary parent edge/stay route with budget `2 * L`.

## Evidence boundary

The local source keeps the already-Proved small-excess theorem behind an explicit logical premise; this verification does not treat a local theorem stub as an axiom-clean unconditional proof. The public theorem `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two` is separately ACCEPTED/Proved on Prove2Me and can discharge the carrier-diameter part in a public composition.

This result is structurally useful because it validates whole-walk composition through nonvertex circuit checkpoints. It is not a new global Polynomial Hirsch bound: the ambient hypothesis `n <= d+2` is much stronger than the general open regime, and in that restricted regime the direct public small-excess diameter theorem already gives a stronger endpoint bound.

The next useful strengthening is to replace the ambient `n <= d+2` assumption with a per-step intrinsic condition saying each selected common carrier admits an equivalent coordinate H-presentation with at most `commonFaceDim + 2` rows. That condition can hold locally even when the parent has large row excess.
