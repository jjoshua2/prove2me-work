#!/usr/bin/env python3
"""Build a reproducible Prove2Me proof packet; this script does not publish."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'submission_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET = 'Solutions.PolynomialLowDimFaceSubmission'
NAME = 'Hirsch.target_avoider_lowdim_face'
seen: set[str] = set()
parts: list[str] = []
imports: set[str] = set()
manifest: list[dict[str, str]] = []


def visit(module: str) -> None:
    if module in seen:
        return
    seen.add(module)
    path = ROOT / (module.replace('.', '/') + '.lean')
    text = path.read_text(encoding='utf-8')
    for line in text.splitlines():
        if line.startswith('import '):
            for imported in line[len('import '):].split():
                if imported.startswith('Solutions.'):
                    visit(imported)
                else:
                    if imported.startswith('Theorems.'):
                        raise RuntimeError('Geometric packet must not import theorem stubs: ' + imported)
                    imports.add(imported)
    body = '\n'.join(line for line in text.splitlines()
                     if not line.startswith('import ') and not line.startswith('#print axioms '))
    # These workspace modules use one outer anonymous noncomputable section,
    # closed implicitly by EOF. Close it explicitly when concatenating files.
    if re.search(r'^noncomputable section\s*$', body, re.MULTILINE):
        body += '\nend\n'
    if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b', body):
        raise RuntimeError('Unexpected admission/opaque code in ' + module)
    parts.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
    manifest.append({'path': str(path.relative_to(ROOT)),
                     'sha256': hashlib.sha256(text.encode()).hexdigest()})


visit(TARGET)
OUT.mkdir(exist_ok=True)
header = '\n'.join('import ' + name for name in sorted(imports)) + '\n'
bundle = header + '\n'.join(parts) + '\n#print axioms solution\n'
(OUT / 'solution.lean').write_text(bundle, encoding='utf-8')
model = (ROOT / 'Definitions/Def_Hirsch_model.lean').read_text(encoding='utf-8')
model_body = '\n'.join(line for line in model.splitlines() if not line.startswith('import '))
standalone = bundle.replace('import Definitions.Def_Hirsch_model\n', '')
standalone = 'import Mathlib\n' + model_body + '\n' + standalone.replace('import Mathlib\n', '')
(OUT / 'standalone.lean').write_text(standalone, encoding='utf-8')
source = (ROOT / 'Solutions/PolynomialLowDimFaceSubmission.lean').read_text(encoding='utf-8')
statement = 'theorem ' + source.split('theorem solution', 1)[1].split(':= by', 1)[0]
statement = statement.replace('theorem ', 'theorem ' + NAME, 1).rstrip() + ' := by sorry'
problem = {
    'env': PIN,
    'problems': [{
        'theorem_name': NAME,
        'theorem_title': 'A target-avoiding vertex shares a low-dimensional face with the source',
        'formal_statement': statement,
        'preamble': 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
        'natural_language_statement': (
            'Let P = {y in R^d : <a_i,y> <= b_i for all i}, described by n inequalities. '
            'Let u and v be extreme points with no nonzero describing row tight at both. '
            'If x is an extreme point and no nonzero row tight at v is tight at x, '
            'then there is a linear subspace W of dimension at most n-2d containing x-u '
            'such that P intersect (u+W) is an extreme subset of P. Thus u and x lie '
            'in a common face contained in an affine subspace of dimension at most n-2d. '
            'No boundedness or full-dimensionality assumption is needed. '
            'This is a structural lemma, not a polynomial diameter bound. '
            'Here n counts describing inequalities, including redundant ones.'),
        'source': 'Derived working lemma for the Polynomial Hirsch mission, 2026-09-06; proof and source manifest in jjoshua2/prove2me-work, scripts/bundle_polynomial_face.py and Solutions/PolynomialLowDimFaceSubmission.lean. No priority claim over the literature.',
        'tags': ['convex-geometry', 'polytopes']
    }]
}
(OUT / 'problem.json').write_text(json.dumps(problem, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
(OUT / 'manifest.json').write_text(json.dumps({'mathlib_rev': PIN, 'files': manifest,
    'solution_sha256': hashlib.sha256(bundle.encode()).hexdigest()}, indent=2) + '\n')
(OUT / 'README.md').write_text('''# Low-dimensional common-face proof packet

`solution.lean` imports only Mathlib and the published Hirsch model. All local
proof helpers are inlined. `standalone.lean` also inlines that model, so it can
be checked in a Mathlib-only Lean 4.30.0 workspace pinned to the recorded revision.
`problem.json` is the new theorem declaration, not a proof of the root conjecture.
The `by sorry` in that JSON is required by the platform problem-publication API;
there are no admissions in the proof files.

The workflow checks both exact proof files and records their axiom output.
This packet is not a claim that a platform submission has occurred.

A local authorized agent should first search for an existing equivalent theorem,
then publish the problem in the specified environment, and submit `solution.lean`
to the resulting theorem ID through the documented Prove2Me verification API.
Do not submit this as a solution of the full Polynomial Hirsch conjecture or the
specified-supporting-face leaf: it proves a different, unconditional lemma.
''', encoding='utf-8')
print('Created geometric packet:', OUT)
print('Proof bytes:', len(bundle.encode()))
