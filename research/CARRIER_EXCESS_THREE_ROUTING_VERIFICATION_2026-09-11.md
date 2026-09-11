# Carrier-excess-three routing verification — 2026-09-11

Frozen source commit: `6552ca5edf585354b043e53d2e15218f59b9d688`.
Verification run: `34630058450`; job `103364397358`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build completed successfully. The audit checked 123 transitive
reports and required these three declarations; each has only `propext`,
`Classical.choice`, and `Quot.sound`:

1. `HirschCircuitLocalization.commonFace_diamLE_three_of_subpresentation_at_most`;
2. `HirschCircuitLocalization.commonFace_diamLE_three_of_minCount_le_dim_add_three`;
3. `HirschCircuitLocalization.feasible_sequence_edge_route_three_mul_of_carrier_minCount_le_dim_add_three`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

The first theorem is an intrinsic carrier statement. If the canonical
common-face coordinate H-polyhedron has an equivalent presentation using at
most `h+3` rows, where `h` is the carrier dimension, then the carrier has padded
vertex-edge graph diameter at most three. The ambient parent may have arbitrary
row excess. The proof uses the public small-excess H-polyhedron theorem as an
explicit logical premise, applies it to the bounded equivalent coordinate
presentation, pads its `m-h <= 3` walk, and transports actual graph adjacency
through the checked common-face affine chart.

The second theorem packages the same condition using the presentation-independent
`commonFaceMinSubpresentationCount`; it requires no checkpoint-vertex hypothesis.

The third theorem applies the existing feasible-checkpoint carrier router: if
every consecutive carrier of a feasible length-`L` checkpoint sequence has
minimum coordinate row excess at most three, then the parent graph has an
ordinary edge/stay route of length `3*L` between the endpoint vertices.
Intermediate checkpoints may be nonvertices.

## Scope

This is a conditional reduction for arbitrary ambient row excess. It does not
prove that all carriers in a general circuit walk have row excess at most three,
and therefore does not close the general d>=4 edge-refinement or Polynomial
Hirsch frontier. Its purpose is to turn a concrete carrier presentation-excess
bound into an explicit ordinary-edge routing cost.
