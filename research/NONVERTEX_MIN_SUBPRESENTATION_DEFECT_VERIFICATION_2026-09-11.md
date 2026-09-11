# Nonvertex minimum-subpresentation defect verification — 2026-09-11

## Kernel evidence

Frozen source commit: `183f6764b4e8d18de80ec9854e607905584b275e`.
GitHub Actions run: `34631227163`; job: `103368257058`.
Audit artifact: `10276472810` (`nonvertex-min-subpresentation-defect-audit`).
Environment: Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The gate ran

```text
lake build Solutions.PolynomialCircuitCheckpointMinSubpresentationDefect
```

and completed all 8,498 jobs successfully. The five required declarations were axiom-audited and each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Checked declarations:

1. `rowCircuit_selectedEffectiveRows_defect_budget_of_reference_vertex`;
2. `rowCircuit_selectedEffectiveRows_excess_defect_of_reference_vertex`;
3. `commonFace_minSubpresentation_effective_witness_of_feasible`;
4. `commonFaceDim_le_minSubpresentation_of_bounded_feasible`;
5. `rowCircuit_commonFace_minSubpresentation_excess_defect_checkpoint`.

## Mathematical consequence

The old minimum-subpresentation theorem required the actual source checkpoint to be a parent vertex. The checked extension removes that restriction.

Let `x` be merely feasible in a bounded parent H-polyhedron, let `y-x` be an ambient row-circuit direction, and let `z` be any fixed parent vertex. If

```text
h = commonFaceDim(a,b,x,y)
M = commonFaceMinSubpresentationCount(a,b,x,y),
```

then a minimum effective equivalent common-face presentation can be chosen and the same scalar budget as in the vertex-source theorem holds:

```text
(M - h) + ((h - 1) - selectedNeutralRank) <= n - d.
```

There are no source/target self-face-nullity correction terms in this inequality.

Two ingredients remove the apparent vertex dependence:

- a single fixed reference parent vertex suffices for the ambient circuit neutral-rank identity, so the actual circuit checkpoint need not be extreme;
- boundedness of the common-face coordinate H-polyhedron plus source feasibility forces its row map to be injective, yielding `h <= M` without making coordinate zero a vertex.

A single endpoint vertex of a `RowCircuitWalk` can serve as the reference `z` for every step of the walk. Therefore this result applies uniformly to all nonvertex intermediate circuit checkpoints.

Separately, `Solutions/PolynomialCircuitBoundedNeutralRank.lean` now proves an even cleaner bounded/feasible neutral-rank identity with no reference vertex. The present theorem remains useful as an already-checked end-to-end minimum-presentation defect extension; the reference parameter can be eliminated in a later cleanup without changing the scalar bound.

## Frontier consequence

The nonvertex localization gap identified in the earlier research handoff is closed at the scalar defect-accounting level. The remaining difficulty is not checkpoint vertexhood but amortization: the inequality alone does not force `M-h <= 3`, and existing exact obstruction work warns that excess/defect trade alone need not create graph-distance progress. Future work should combine this exact budget with ordered blocker/rank progress, persistent carrier intervals, distinct-carrier charging, or another monotone geometric resource.
