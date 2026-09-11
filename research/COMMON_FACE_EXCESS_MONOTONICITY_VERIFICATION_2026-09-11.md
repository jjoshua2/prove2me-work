# Common-face presentation-excess monotonicity verification — 2026-09-11

Frozen source commit: `3d238d38df205ebd1b56964fc3214c6f16abfad6`.
Verification run: `34632625742`; job `103372881492`.
Environment: Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build `Solutions.PolynomialCommonFaceExcessMonotonicity` completed
successfully. The axiom audit checked 51 printed transitive reports and required
these three declarations; each has only `propext`, `Classical.choice`, and
`Quot.sound`:

1. `HirschCircuitLocalization.commonFace_minSubpresentation_excess_le_parent_excess_of_bounded_feasible`;
2. `HirschCircuitLocalization.commonFace_minSubpresentationCount_le_faceDim_add_parent_excess`;
3. `HirschCircuitLocalization.commonFace_has_subpresentation_faceDim_add_parent_excess`.

No `sorryAx` or other axiom occurs in their transitive closures.

## Mathematical content

Let `P=Hpoly a b` be bounded, let `x` be any feasible source checkpoint, and let
`y` be arbitrary. Write `h` for the canonical common-face coordinate dimension
and `M_min` for the least number of original coordinate rows needed for an
equivalent common-carrier H-presentation. Then

```text
M_min - h <= n - d.
```

Equivalently,

```text
M_min <= h + (n-d),
```

and an actual equivalent original-row coordinate subpresentation with at most
`h+(n-d)` rows exists.

No circuit, maximality, checkpoint extremality, strict feasibility, or
irredundancy assumption is used. The proof combines the effective-row count
inequality with the feasible-checkpoint minimum-subpresentation witness and the
bounded parent row-map injectivity theorem.

This establishes a clean monotonicity invariant: passing to a common carrier
cannot increase finite row-presentation excess beyond the ambient `n-d`.

## Scope

This does not make large ambient excess cheap. It supplies an upper bound on the
carrier excess quantity consumed by the public small-carrier cost theorem. The
general whole-walk problem remains to show that large carrier excesses are rare,
amortized by another resource, or otherwise route cheaply.
