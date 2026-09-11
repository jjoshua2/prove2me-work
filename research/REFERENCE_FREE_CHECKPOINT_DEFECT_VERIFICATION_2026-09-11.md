# Reference-free nonvertex checkpoint defect — verification receipt

Date: 2026-09-11.

## Result

The following declarations were kernel-checked at frozen source commit
`2d0794c46940cf7be3221c3ce02a117becb7ba4f`:

1. `HirschCircuitLocalization.rowCircuit_selectedEffectiveRows_defect_budget_of_bounded`;
2. `HirschCircuitLocalization.rowCircuit_selectedEffectiveRows_excess_defect_of_bounded`;
3. `HirschCircuitLocalization.rowCircuit_commonFace_minSubpresentation_excess_defect_of_bounded`.

The final theorem says: for a bounded finite H-polyhedron, any feasible source
checkpoint `x`, and any ambient row-circuit displacement `y-x`, let `M` be the
minimum number of original common-face coordinate rows needed for an equivalent
presentation and let `h` be the common-carrier dimension.  A minimum effective
presentation exists, and

```text
(M - h) + neutralRankDefect <= n - d.
```

No checkpoint extremality, auxiliary/reference parent vertex, or source/target
self-face correction term is required.

## Verification

- Lean 4.30.0.
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Workflow run `34632388202`.
- Job `103372091147`.
- Source file `Solutions/PolynomialCircuitCheckpointMinSubpresentationDefectBounded.lean`.
- Build completed successfully (`8500` Lake jobs including dependencies).
- Artifact `10277175831`, ZIP SHA-256
  `042633400c932f00aa944e989d635d779728079fbef6cc80f48066db4ccc4580`.

All three declarations report only the standard logical axioms `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axiom occurs.
The gate explicitly audited the latter two public-facing declarations and the
build log records the subtraction-free helper as standard-axiom-only as well.

## Proof structure

The earlier nonvertex theorem used a fixed parent vertex only to obtain the
rank-`h-1` neutral-row identity for an ambient row circuit.  The already-verified
bounded neutral-rank theorem shows that boundedness plus source feasibility are
enough.  This yields a subtraction-free selected-row budget first:

```text
|F| + defect + d <= n + h.
```

The ordinary excess form then follows using `h <= |F|` and `d <= n`.  For a
minimum equivalent common-face presentation, boundedness of the intrinsic
coordinate model makes its row map injective, proving `h <= M` even though the
checkpoint is not a vertex.  This removes the last artificial endpoint
parameter from the minimum-presentation resource inequality.

## Boundary

This theorem is a structural accounting resource, not a whole-walk polynomial
routing theorem.  Low intrinsic excess carriers are already cheaply routable;
for larger excess the remaining problem is to amortize the neutral-rank defect
and/or construct recursive carrier routes without repeatedly paying expensive
high-dimensional carriers.  Polynomial Hirsch and the d>=4 circuit-to-edge
frontier remain Open.

No Prove2Me publication is claimed by this receipt.
