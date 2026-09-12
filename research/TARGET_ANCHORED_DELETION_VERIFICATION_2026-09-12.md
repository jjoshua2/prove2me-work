# Target-anchored batch deletion: verification receipt

Date: 2026-09-12. PR #165.

## Frozen source and executed gate

- Source commit: `7533ea8f4a4517d5939bd36665c185d87bdd2ff0`.
- Source file: `Solutions/PolynomialTargetAnchoredDeletion.lean`.
- Source SHA-256: `1b8e3c801aa4a549728880ce253381aab0317ded1a1ee95c0635c9dea4d62a7e`.
- Gate checkout: `1d66750bad249e0cf45f75ddba33f5ff3b9ac551`.
- GitHub Actions run: `34673820743`.
- Job: `103499983050`.
- Result: **success on the first final-gate run; no proof repair/rerun required**.
- Lean `v4.30.0`, Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Artifact: `10291368656`, `target-anchored-deletion-verification`.
- Artifact SHA-256: `729f298a800d491102ea05ed48acd4649f1ebecd067e2c568b1253fbafa70017`.

The artifact was downloaded and independently checked: its ZIP hash matches the GitHub digest; the exact regression JSON matches the expected hash; all seven complete, line-wrapped transitive axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` occurs. There is one harmless unused-`change` tactic linter warning; the verified source was retained unchanged.

## Verified declarations

Every declaration below is in namespace `HirschTargetDeletion`:

1. `selected_rowMap_injective_of_covers_target_tight`
2. `selected_vertex_of_covers_target_tight`
3. `exists_target_preserving_batch_deletion`
4. `selected_tight_outer_extremePoints_eq_singleton`
5. `selected_tight_outer_diamLE_zero`
6. `exists_zero_diameter_target_outer`
7. `same_phase_step_has_target_preserving_blocker_deletion`

Each report has exactly the standard logical axiom set `{propext, Classical.choice, Quot.sound}`.

## Mathematical consequences and limits

Retaining every inequality tight at an original vertex preserves that vertex and an injective row map. Therefore any simultaneous batch J of target-slack inequalities can be deleted, retaining exactly n-|J| rows, with exact recovery when J is restored. No boundedness or source-vertex premise is used.

Keeping exactly the target-tight rows produces a pointed outer with extreme-point set `{v}` and old-vertex graph diameter zero. Its feasible set need not be a singleton, and other original vertices can disappear.

For an actual same-phase maximal circuit step toward a vertex target, the chosen destination blocker is target-slack, so its deletion is pointed and preserves the target. PR #163's all-vertices-tight exceptional alternative is ruled out in this application.

These results do not prove inexpensive batch reinsertion, preserve the source as an outer vertex, or solve the global fixed-degree polynomial recurrence. The zero old-vertex cost of the target-tight outer must not be confused with the graph cost of the original clipped parent.

## Exact regression

`python3 scripts/test_target_anchored_deletion.py` passes 212 batch-deletion checks across 30 target vertices in 9 fixtures. The controls include unbounded and lower-dimensional presentations, redundant/duplicate/zero rows, dimension zero, and coefficients above 10^40. The nonvertex same-phase, exception-changing-phase, and loss-of-other-vertices controls all pass.

Full JSON SHA-256: `094ebcb1551b051d86d0e29e773e2530934a3766a4e9a9bf1087b802ecad7097`. Two local exact runs and the hosted gate produced byte-identical JSON.

## Reproduce

```bash
python3 scripts/test_target_anchored_deletion.py
lake build Solutions.PolynomialTargetAnchoredDeletion
lake env lean Solutions/PolynomialTargetAnchoredDeletion.lean > /tmp/target-deletion-axioms.log
python3 scripts/check_lean_axiom_log.py /tmp/target-deletion-axioms.log \
  HirschTargetDeletion.selected_rowMap_injective_of_covers_target_tight \
  HirschTargetDeletion.selected_vertex_of_covers_target_tight \
  HirschTargetDeletion.exists_target_preserving_batch_deletion \
  HirschTargetDeletion.selected_tight_outer_extremePoints_eq_singleton \
  HirschTargetDeletion.selected_tight_outer_diamLE_zero \
  HirschTargetDeletion.exists_zero_diameter_target_outer \
  HirschTargetDeletion.same_phase_step_has_target_preserving_blocker_deletion
```

Run the commands with `set -euo pipefail`. The temporary ready-for-review-only verifier is removed before integration; no push/synchronize proof loop is left behind.

**Publication status: kernel-verified only. No Prove2Me registration, `/verify` submission, authenticated acceptance, or credential use occurred in this PR.**
