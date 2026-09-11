# Excess-two shared-index adjacency verification — 2026-09-10

Kernel/source receipt for the normalized excess-two moment-slice portal geometry.

- exact source commit: `787b81662b30dde39c4567b568cc97dd69d3a6f7`
- Lean: `v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Actions run: `34558107938`
- job: `103135022007`
- artifact: `10183359015`
- artifact digest: `sha256:aafbd9540a9b5fa1d358eab67143eeeb1b0153e6ffdbeed1164500b7e9445553`

The gate compiled `Solutions.PolynomialExcessTwoConvexity` and `Solutions.PolynomialExcessTwoSharedAdjacency` and freshly audited these eight declarations:

- `HirschExcessTwo.momentSlice_convex`
- `HirschExcessTwo.segment_subset_supportFace`
- `HirschExcessTwo.sum_eq_add_add_of_zero_off_triple`
- `HirschExcessTwo.supportFace_triple_eq_segment_shared_low`
- `HirschExcessTwo.pairPoint_adj_shared_low`
- `HirschExcessTwo.supportFace_triple_eq_segment_shared_high`
- `HirschExcessTwo.pairPoint_adj_shared_high`
- `HirschExcessTwo.pairPoint_two_step_route`

Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or other transitive axiom occurs.

## Mathematical result

For one low moment index `i` and two distinct high indices `j,k`, the support carrier on `{i,j,k}` is exactly

```text
segment (pairPoint i j) (pairPoint i k).
```

Since that support carrier is an extreme face, the pair vertices sharing the low index are adjacent. The symmetric statement holds for two low indices sharing one high index.

Consequently, arbitrary low/high pair vertices have the canonical two-edge/stay route

```text
pair(i,j) → pair(i,l) → pair(k,l).
```

Each arrow is either equality or an actual `Adj` edge of the normalized moment slice. Thus the pair-vertex subgraph has padded diameter at most two.

This receipt is Lean kernel/source evidence only; these declarations have not been separately published to Prove2Me. It does not yet classify all extreme points of the moment slice. The next formal step is to show every extreme point is either an equal-moment singleton or a low/high pair point, then handle the singleton adjacency cases and conclude the full normalized excess-two slice has graph diameter at most two.
