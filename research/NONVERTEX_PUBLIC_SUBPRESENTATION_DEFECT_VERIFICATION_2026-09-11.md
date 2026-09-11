# Public-vocabulary nonvertex subpresentation defect verification — 2026-09-11

Frozen source commit: `52b4ebdf3e1f76bd297c765a15b2d22dfc1650a9`.
Verification run: `34633224935`; job `103374853296`.
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The targeted build

```text
lake build Solutions.PolynomialCircuitCheckpointSubpresentationPublic
```

completed all 8,500 jobs successfully. The axiom audit inspected 53 printed transitive reports and required

```text
HirschCircuitLocalization.rowCircuit_commonFace_subpresentation_excess_defect_checkpoint
```

which depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Public statement

This theorem is deliberately phrased in the same public `HirschCommonFace` vocabulary as the existing vertex-source Prove2Me defect theorem. Let `P=Hpoly a b` be bounded, let `z` be any parent vertex, let `x` be any feasible checkpoint, and suppose `y-x` is a row circuit. If the canonical common carrier of `x,y` has an equivalent original-row coordinate subpresentation using at most `M` rows, then there is such a subpresentation whose effective selected row set `F` satisfies

```text
commonFaceDim(a,b,x,y) <= |F| <= M
```

and

```text
(|F|-commonFaceDim) +
((commonFaceDim-1)-selectedNeutralRank) <= n-d.
```

The source checkpoint `x` need not be a parent vertex. The fixed reference vertex `z` is used only to discharge the global row-circuit neutral-rank accounting; one endpoint vertex of a whole circuit walk can serve as the same reference for every step.

## Relation to the internal minimum-count theorem

The stronger internal theorem `rowCircuit_commonFace_minSubpresentation_excess_defect_checkpoint` was already verified and merged. This adapter eliminates the repo-internal `commonFaceMinSubpresentationCount` from the public interface and exposes a reusable theorem directly in terms of `CommonFaceHasSubpresentationAtMost`.

This is a structural localization theorem, not a global Polynomial Hirsch bound. It removes checkpoint vertexhood from the defect accounting but does not by itself amortize high carrier presentation excess across a walk.
