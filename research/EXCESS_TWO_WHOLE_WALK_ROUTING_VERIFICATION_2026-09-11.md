# Excess-two whole-walk edge-routing verification — 2026-09-11

## Kernel-verified result

Frozen source commit: `2935f42d255029dcbc337c953dbb364d71ef1c94`.
Verification run: `34629152760`; job `103361465979`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build `Solutions.PolynomialExcessTwoWholeWalkRouting` completed
successfully. The audit checked 120 transitive axiom reports and required the
following three declarations; each has only `propext`, `Classical.choice`, and
`Quot.sound`:

1. `HirschCircuitLocalization.hpoly_isClosed`;
2. `HirschCircuitLocalization.feasible_sequence_edge_route_two_mul_of_rows_le_dim_add_two`;
3. `HirschCircuitLocalization.rowCircuitWalk_edge_route_two_mul_of_rows_le_dim_add_two`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

Assume the established small-excess H-polyhedron bound as an explicit premise.
Let `P = Hpoly a b` be bounded with `n <= d+2`. For any feasible checkpoint
sequence `w 0,...,w L` whose two endpoints are parent vertices, the theorem
constructs

```text
Route (Adj P) (2*L) (w 0) (w L).
```

The intermediate checkpoints need not be vertices, and the old sequence need
not be a circuit walk. Each consecutive pair lies in its common carrier. The
previously verified arbitrary-checkpoint carrier theorem gives intrinsic
`DiamLE <= 2` for every such carrier. Compactness of the bounded finite
H-polytope and the checked face-preserving checkpoint router then replace the
whole feasible sequence by one parent vertex-edge/stay route, charging two per
old step.

The `RowCircuitWalk` corollary only unpacks circuit-walk feasibility. Circuit
maximality/support minimality are not needed by this low-excess routing step.
Thus a length-`L` circuit walk between parent vertices admits an ordinary
edge/stay refinement with budget `2*L`, even when all intermediate circuit
checkpoints are nonvertices.

## Evidence boundary

The local source represents the public theorem
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` as the explicit
premise `SmallExcessHpolyBound`; the kernel audit therefore does not import a
local theorem stub. An unconditional public composition can instead use the
now-Prove2Me-Proved common-carrier theorem
`Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`
(theorem `ca4c980f-86d7-4810-be9e-30e473b9dd70`, accepted proof
`b9d5af5b-51d3-48dd-b008-a365a18b053e`) together with the checked generic
carrier-routing theorem.

This proves a complete circuit-to-edge refinement result only in the ambient
row-excess-at-most-two regime. It does not imply that arbitrary carriers in the
general d>=4 Polynomial Hirsch frontier have such low excess, and it does not
close that frontier.
