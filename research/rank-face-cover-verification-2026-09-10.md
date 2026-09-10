# Rank-sensitive face-cover verification receipt

## Observed final gate

- Repository: `jjoshua2/prove2me-work`.
- Research PR: https://github.com/jjoshua2/prove2me-work/pull/61 (draft; no merge).
- Tested source commit: `681314640b6f84792d8ae011c3534a6e8c456930`.
- Workflow run: https://github.com/jjoshua2/prove2me-work/actions/runs/34532572816.
- Job: `103056581418`.
- Result: **completed / success**.
- Lean build completed: `2026-09-10T21:32:39Z`.
- Lean: `4.30.0`.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Workflow checked out the exact source commit above, not an unreviewed merge commit.

The actual job log was retrieved after completion. It reports `Build completed
successfully (8486 jobs).` and `PASS: 17 declarations audited`. Those 8486
Lake jobs include cached dependencies; this is not a claim that 8486 new
proofs were written or checked from scratch.

## Targeted Lean command

```sh
lake build Solutions.PolynomialBalancedPairFaceCover \
  Solutions.PolynomialWeightedFaceCover \
  Solutions.PolynomialRankSensitiveFaceCover \
  Solutions.PolynomialFaceCoverBarrier
```

All four modules compiled successfully. The target audit allows only
`propext`, `Classical.choice`, and `Quot.sound` and fails on missing reports
or any other axiom, including `sorryAx`. Each of the following 17 declarations
passed its transitive axiom check (14 newly added declarations and 3 repaired
pair-face declarations):

```text
HirschBalancedFaceCover.nonzeroRowPairFace_isExtreme
HirschBalancedFaceCover.row_face_vertex_pair_multiplicity
HirschBalancedFaceCover.row_face_diamLE_of_pair_face_bounds
HirschFaceSplice.shortest_weighted_face_cover_budget
HirschFaceSplice.diamLE_of_weighted_face_cover
HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim
HirschRankFaceCover.rowSection_isExtreme
HirschRankFaceCover.faceRowSpan_mono
HirschRankFaceCover.rowSection_ne_of_not_mem_faceRowSpan
HirschRankFaceCover.faceRowSpan_lt_rowSection
HirschRankFaceCover.faceRowSpan_finrank_lt_rowSection
HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds
HirschFaceCoverBarrier.weighted_cover_cardinality_lower_bound
HirschFaceCoverBarrier.averaging_budget_ge_card_sub_one
HirschFaceCoverBarrier.improving_certificate_requires_improving_child
HirschFaceCoverBarrier.cubeAveragingBudget_add_one
HirschFaceCoverBarrier.cubeAveragingBudget_eq
```

The two cube-recurrence declarations use only `propext` and `Quot.sound`;
the other 15 use all three allowed axioms. The only Lean linter warning in
the targeted build is a pre-existing unnecessary `simpa` in
`PolynomialBalancedRowFaceCover.lean:67`. No Lean errors occurred.

## Exact finite certificate checks

The same gate successfully ran:

```sh
python3 scripts/test_rank_face_cover_barrier.py --max-dimension 7
```

The original CI artifact was downloaded and inspected. Its result JSON agrees
with the locally executed exact tests:

- 2,000 general weighted-cover regression cases passed.
- 28 cube primal/dual certificates passed, through dimension 7.
- 21,296 proper-face dual constraints were checked.
- The 3D redundant-supporting-row saturation counterexample passed.

The checks use exact integers and rational fractions, not floating-point LP
solutions. The finite examples complement, rather than replace, the abstract
Lean proofs.

Original artifact: `rank-face-cover-final-audit.zip`, GitHub artifact ID
`10174152001`. It contains `rank-face-lean.log` and
`rank-face-exact-results.json`. Downloaded ZIP SHA-256:

```text
bf68a645631d9b209fa54a75a126c0c765e073b7c27bfd079d0d8643c089aeff
```

GitHub artifact retention is three days. This receipt and the source pin
remain in the repository for reproduction after that artifact expires.

## What is and is not established

Lean-checked: codimension incidence, saturated strict rank descent, the
weighted and rank-selected diameter certificates under their stated child
bounds/connectivity hypotheses, the general vertex-count obstruction, and
the numerical singleton-seeded cube recurrence.

The full mixed-rank cube optimization formula `(k+1)*2^(d-k)-1` has an ordinary
mathematical primal/dual proof in the companion research note and exact
finite certificates through dimension 7. This continuation does not
formalize the full cube face lattice or that optimization theorem in Lean.

The obstruction is a lower bound on the averaging **certificate**, not on
actual graph diameter. No general polynomial graph-diameter bound is proved.
No Prove2Me API calls, submissions, or publications were made, and no platform
acceptance is claimed. Publication remains with the user. Main was not
changed. The research PR is based on a frozen pre-continuation research
commit, so its diff does not include the unrelated older integration work.

This receipt is a documentation-only addition after the tested source commit.
