#!/usr/bin/env bash
# Run from the repository root with its committed Lean/Mathlib environment.
set -euo pipefail
python3 scripts/check_actions_policy.py
test "$(cat lean-toolchain)" = 'leanprover/lean4:v4.30.0'
grep -Fq c5ea00351c28e24afc9f0f84379aa41082b1188f lake-manifest.json
python3 scripts/check_cap_vertex_classification.py --output /tmp/cap-vertex-exact.json
python3 - <<'PY'
import hashlib, json
from pathlib import Path
expected = json.loads(Path('research/CAP_VERTEX_CLASSIFICATION_EXACT_SUMMARY_2026-09-11.json').read_text())
actual = Path('/tmp/cap-vertex-exact.json').read_bytes()
assert hashlib.sha256(actual).hexdigest() == expected['full_report_sha256']
assert json.loads(actual)['summary'] == expected['summary']
print('Exact cap-classification regression and report hash: OK')
PY
lake build Solutions.PolynomialCompactCapVertexClassification Solutions.PolynomialOneRowDeletionCapWitness
lake env lean Solutions/PolynomialCompactCapVertexClassification.lean 2>&1 | tee /tmp/compact-cap-vertices.log
python3 scripts/check_lean_axiom_log.py /tmp/compact-cap-vertices.log \
  HirschCapVertices.cap_active_kernel_eq_zero \
  HirschCapVertices.hpoly_extremePoints_finite \
  HirschCapVertices.compact_hpoly_cap_vertex_classification \
  HirschCapVertices.exists_level_above_compact_and_outer_vertices \
  HirschCapVertices.old_vertex_survives_cap \
  HirschCapVertices.old_edge_survives_cap
lake env lean Solutions/PolynomialOneRowDeletionCapWitness.lean 2>&1 | tee /tmp/deletion-cap-witness.log
python3 scripts/check_lean_axiom_log.py /tmp/deletion-cap-witness.log \
  HirschCapVertices.erased_hpoly_eq_deletionOuterSet \
  HirschCapVertices.deletionCapNormal_eval \
  HirschCapVertices.deletionOuterSet_cap_eq \
  HirschCapVertices.exists_deletion_cap_with_vertex_classification
