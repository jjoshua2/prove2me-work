# Injective / one-row-deletion cubic circuit walk

Date: 2026-09-11

Status while this note is written: candidate formalization in PR #151; hosted Lean verification pending. This note does not claim kernel verification or Prove2Me publication.

## Structural observation

The completed `standardCircuitWalk_cubic` theorem is matrix-free and does not assume boundedness. For an H-presentation, boundedness had only been used by the existing wrapper to derive injectivity of the row-evaluation map before transporting the standard-slice walk back to row coordinates.

Therefore the natural stronger interface is:

- assume `Function.Injective (rowMap a)` directly;
- take any feasible source `u` and any vertex target `v`;
- map them to slack coordinates;
- use `standardCircuitWalk_cubic` in `LinearMap.range (rowMap a)`;
- transport the walk back with `rowCircuitWalk_iff_slackCircuitWalk` and `slackCircuitWalk_iff_standardCircuitWalk`.

This yields the same explicit padded length `17*n^3` without boundedness of `Hpoly a b`.

## One-row deletion application

For a bounded nonempty parent H-presentation, `HirschDeletion.rowMapWithout_injective_of_bounded` already proves that deleting any one row leaves an injective row-evaluation map. Reindex the remaining rows by

`Fin (Fintype.card {i : Fin n // i ≠ j})`.

The reindexed H-polyhedron is exactly `HirschCapVertices.deletionOuterSet a b j`, and the retained row count is at most `n`.

Hence, if the candidate compiles, every feasible point of the potentially unbounded deletion outer reaches every deletion-outer vertex by a row-circuit walk of length

`17 * m^3`, where `m = Fintype.card {i : Fin n // i ≠ j}` and `m ≤ n`.

## What this changes

This would remove **circuit-walk existence** from the old-outer cost `D` in the merged current exterior-cap interface. It does **not** turn that circuit walk into an edge walk. The remaining substantive problem is still circuit-to-edge refinement on the pointed lower-row deletion presentation (plus the separate blocker-face budget `B`).

So this is useful because it narrows the dynamic obstruction; it is not a disguised solution of the Open polynomial edge-refinement theorem.
