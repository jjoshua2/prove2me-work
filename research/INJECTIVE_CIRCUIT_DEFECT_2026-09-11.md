# Injective circuit neutral-rank and deletion-savings generalization

Date: 2026-09-11 (America/New_York)

Status while this note is written: candidate formalization; focused hosted Lean verification is configured and pending. This note does not claim kernel verification or Prove2Me publication.

## Observation

The existing bounded nonvertex neutral-kernel proof uses boundedness only to obtain

`Function.Injective (HirschCircuit.rowMap a)`.

After that point the argument is entirely circuit support-minimality and finite-dimensional rank-nullity. The same is true of the exact deletion-savings identity: boundedness enters through exact neutral rank and the ambient row-count lower bound, both of which follow directly from row-map injectivity.

## Candidate generalization

`Solutions/PolynomialCircuitInjectiveNeutralRank.lean` replaces boundedness/vertexhood by explicit row-map injectivity and proves:

- `rows_ge_dimension_of_injective`;
- `rowCircuit_neutral_kernel_eq_span_of_injective`;
- `rowCircuit_neutral_rank_eq_dim_sub_one_of_injective`;
- the corresponding arbitrary-subspace kernel/rank theorems;
- exact `commonFaceDim - 1` neutral rank on a circuit common direction.

`Solutions/PolynomialCircuitInjectiveDeletionSavings.lean` then proves the injective versions of the complete exact resource accounting:

- selected neutral defect is bounded by discarded neutral rows;
- exact five-term identity `e_F + delta + kappa + s + t = n-d`;
- omitted nonneutral effective rows add certified savings;
- the old budget saturates iff all three explicit savings vanish.

## Direct one-row deletion application

`Solutions/PolynomialOneRowDeletionCircuitDefect.lean` instantiates these theorems with the canonical one-row deletion presentation from PR #151. Since the original bounded parent supplies injectivity after deleting one row, the potentially unbounded deletion outer inherits:

- exact neutral rank `h-1` on every row-circuit carrier;
- the complete excess/defect/savings identity using the deletion outer's own retained-row count;
- the strengthened nonneutral-savings inequality.

## Frontier meaning

After PR #151, the unbounded deletion outer already has an explicit cubic row-circuit route. This candidate would show that the same sharp rank/defect accounting used in the bounded parent remains valid along those deletion-outer circuit steps.

It still does **not** convert a circuit step into an ordinary edge path. The remaining `D` obstruction is therefore increasingly isolated to dynamic circuit-to-edge routing, not circuit-walk existence and not loss of the neutral-rank/excess bookkeeping under deletion.
