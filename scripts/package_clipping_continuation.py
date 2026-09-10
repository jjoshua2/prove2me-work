#!/usr/bin/env python3
"""Package checked sources and receipts, never credentials or unrelated files.

Invoked after the complete Lean audit and exact regression step succeeds.
This creates a local Actions artifact; it does not publish to Prove2Me.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    'PolynomialClosedFaceTrace', 'PolynomialConvexSubsegment',
    'PolynomialRadialRetraction', 'PolynomialClipEndpointLift',
    'PolynomialSimultaneousClipDiameter', 'PolynomialHorizonCap',
]
paths: set[Path] = set()


def collect(module: str) -> None:
    path = Path(module.replace('.', '/') + '.lean')
    if path in paths:
        return
    full = ROOT / path
    if not full.is_file():
        raise RuntimeError(f'Missing local dependency: {path}')
    paths.add(path)
    for imported in re.findall(r'^import\s+([A-Za-z0-9_.]+)', full.read_text(), re.M):
        if imported.startswith(('Solutions.', 'Definitions.')):
            collect(imported)
        elif not imported.startswith('Mathlib'):
            raise RuntimeError(f'Unrecognized external import: {imported}')


for module in MODULES:
    collect('Solutions.' + module)
for name in [
    'lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
    'scripts/check_lean_axiom_log.py', 'scripts/pointed_polyhedron_exact.py',
    'scripts/test_face_preserving_checkpoints.py',
    'scripts/test_cone_carrier_descent.py', 'scripts/check_carrier_regression.py',
    'scripts/test_carrier_euler_refinement.py',
    'scripts/package_clipping_continuation.py',
    'research/ConeCarrierDescent.md', 'research/CarrierEulerRefinement.md',
    'research/ClippingVerificationProgress.md',
    'research/cone_carrier_expected.json',
    '.github/workflows/verify-simultaneous-clipping.yml',
]:
    path = Path(name)
    if not (ROOT / path).is_file():
        raise RuntimeError(f'Missing package input: {name}')
    paths.add(path)

sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
manifest = {str(p): hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in sorted(paths)}
receipt = {
    'source_commit': sha,
    'actions_run_id': os.environ.get('GITHUB_RUN_ID'),
    'bounded_clipping_chain': 'compiled and axiom-audited before packaging',
    'required_lean_declarations': 42,
    'full_unbounded_theorem_formalized': False,
    'cone_carrier_theorem_lean_verified': False,
    'carrier_euler_refinement_lean_verified': False,
    'cone_carrier_exact_regression': 'completed and hash-matched before packaging',
    'carrier_euler_exact_regression': 'completed and hash-matched before packaging',
    'prove2me_calls': 0,
    'source_sha256': manifest,
}
output = Path(sys.argv[1] if len(sys.argv) > 1 else '/tmp/clipping-verified-source.zip')
with zipfile.ZipFile(output, 'w', zipfile.ZIP_DEFLATED) as archive:
    for p in sorted(paths):
        archive.write(ROOT / p, str(p))
    for name in ['all-clipping.log', 'cone-carrier.json', 'carrier-euler.json']:
        full = Path('/tmp') / name
        if not full.is_file():
            raise RuntimeError(f'Missing completed-verification output: {full}')
        archive.write(full, 'verification/' + name)
    archive.writestr('verification/receipt.json', json.dumps(receipt, indent=2, sort_keys=True) + '\n')
print(output, hashlib.sha256(output.read_bytes()).hexdigest())
