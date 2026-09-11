# Compact cap vertex classification — hosted verification receipt

Date: 2026-09-11

This receipt upgrades the source in PR #147 from ordinary/exact evidence to Lean kernel evidence. It does **not** claim Prove2Me publication.

## Frozen verified source

- PR: #147, `formal/compact-cap-vertex-classification`
- source commit: `4750a4021f8dc12465fbe711bb184fbe04094e7b`
- Lean: `v4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Actions run: `34654729053`
- job: `103444522860`
- conclusion: **success**
- artifact: `10285363012`, `compact-cap-vertex-classification-verification`
- artifact digest: `sha256:0677fc1dcf153734ca749e530509dfb9f75dd0d63902d7db02e871ede35f464f`

## Exact regression gate

The hosted job reran `scripts/check_cap_vertex_classification.py` and compared the complete deterministic JSON report against the committed hash. The report reproduced exactly:

- 129 instances;
- 735 outer-vertex occurrences;
- 824 capped-vertex occurrences;
- 193 constructed new-cap/old-neighbor edge certificates;
- 754 old-edge preservation checks over 100 strict-far instances;
- 29 non-far instances excluding old vertices;
- full report SHA-256 `084a002e8c4447edf73bfd665e93ef90d9e5d7338b1cb99fbf6fa7b0d4229a0c`.

These remain finite exact evidence, not the universal proof.

## Kernel-checked declarations

`Solutions/PolynomialCompactCapVertexClassification.lean` built successfully and the following six declarations were axiom-audited:

- `HirschCapVertices.cap_active_kernel_eq_zero`
- `HirschCapVertices.hpoly_extremePoints_finite`
- `HirschCapVertices.compact_hpoly_cap_vertex_classification`
- `HirschCapVertices.exists_level_above_compact_and_outer_vertices`
- `HirschCapVertices.old_vertex_survives_cap`
- `HirschCapVertices.old_edge_survives_cap`

`Solutions/PolynomialOneRowDeletionCapWitness.lean` also built successfully and the following four declarations were axiom-audited:

- `HirschCapVertices.erased_hpoly_eq_deletionOuterSet`
- `HirschCapVertices.deletionCapNormal_eval`
- `HirschCapVertices.deletionOuterSet_cap_eq`
- `HirschCapVertices.exists_deletion_cap_with_vertex_classification`

For every declaration, the complete axiom report contained only:

- `propext`
- `Classical.choice`
- `Quot.sound`

The axiom checker reported:

- `Axiom audit passed: 6 required declarations; 6 reports checked; only standard logical axioms.`
- `Axiom audit passed: 4 required declarations; 4 reports checked; only standard logical axioms.`

No `sorryAx` remains in the verified declarations.

## Formal result now established

The generic compact single-halfspace theorem is kernel-checked: every vertex of a compact clip `Hpoly a b ∩ {x | <c,x> <= M}` is either an old outer vertex, or it is a cap vertex adjacent by an **actual clipped edge** to an old outer vertex strictly below the cap.

The one-row deletion integration is also kernel-checked. For every nonempty bounded parent and deleted row, there exists an explicit cap level such that:

1. the capped deletion outer is compact;
2. the whole parent is strictly below the cap;
3. **every old deletion-outer vertex** is strictly below the cap;
4. reinserting the deleted row recovers the parent exactly;
5. every old outer vertex survives;
6. every old outer edge survives;
7. every new capped vertex is on the cap and adjacent to an old deletion-outer vertex.

This closes the universal cap-vertex/edge classification gap identified after PR #144, without formalizing recession-ray classification.

## Scope still unresolved

This theorem supplies cap geometry, not a polynomial cost theorem. In particular:

- the uncapped deletion outer may be unbounded, so the bounded-only lower-excess diameter induction does not automatically provide its old-vertex graph cost `D`;
- adding the artificial cap makes the outer bounded but restores one row in the presentation count;
- the deleted blocker facet can retain the parent row excess, so its budget `B` is not automatically lower-excess either.

Current-main horizon-shadow results can route cap motion onto the deleted blocker facet, and the separate facet-reentry/dimension-descent line is aimed at paying repeated visits to that facet. These are separate obligations from the cap classification proved here.

No Prove2Me theorem registration or submission was performed by this verification run.
