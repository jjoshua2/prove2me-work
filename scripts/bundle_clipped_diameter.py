#!/usr/bin/env python3
"""Bundle and independently compile the clipped-diameter proof. Does not publish."""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'clipped_diameter_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET = 'Solutions.PolynomialClippedDiameterSubmission'
NAME = 'Hirsch.clipped_diameter_le_outer_add_cut_face'
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
            for imported in line[7:].split():
                if imported.startswith('Solutions.'):
                    visit(imported)
                else:
                    if imported.startswith('Theorems.'):
                        raise RuntimeError('This proof must not import theorem stubs: ' + imported)
                    imports.add(imported)
    body = '\n'.join(line for line in text.splitlines()
                     if not line.startswith('import ') and not line.startswith('#print axioms '))
    if re.search(r'^noncomputable section\s*$', body, re.MULTILINE):
        body += '\nend\n'
    if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b', body, re.MULTILINE):
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
standalone = 'import Mathlib\n' + model_body + '\n' + bundle.replace(
    'import Definitions.Def_Hirsch_model\n', '').replace('import Mathlib\n', '')
(OUT / 'standalone.lean').write_text(standalone, encoding='utf-8')
source = (ROOT / (TARGET.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
statement = 'theorem ' + NAME + source.split('theorem solution', 1)[1].split(':= by', 1)[0]
statement = statement.rstrip() + ' := by sorry'
problem = {'env': PIN, 'problems': [{
    'theorem_name': NAME,
    'theorem_title': 'Full clipped diameter is at most outer diameter plus cut-face diameter',
    'formal_statement': statement,
    'preamble': 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
    'natural_language_statement': (
        'Let Q be convex in R^d with padded vertex-edge diameter at most B. '
        'Let c.x <= b be a halfspace, and assume Q has an extreme point on or beyond its boundary. '
        'If the equality slice F = Q intersect {c.x=b} has padded diameter at most C, '
        'then the clipped set P = Q intersect {c.x<=b} has padded diameter at most B+C. '
        'This covers all clipped vertices, not only old Q vertices. The two retained ends '
        'of one outer walk share the B budget; replace its first-to-last cut excursion '
        'by a cut-face walk of length C. No monotonicity, low-rank, product, boundedness, '
        'or full-dimensionality assumption is needed beyond the stated hypotheses. '
        'The outer-vertex assumption matters for unbounded Q. This transfers two assumed '
        'diameter bounds; it does not prove a uniform polynomial Hirsch bound.'),
    'source': 'Working formalization for the Polynomial Hirsch mission, 2026-09-06; jjoshua2/prove2me-work branch chatgpt/clipped-diameter. No literature-priority claim.',
    'tags': ['convex-geometry', 'polytopes', 'graph-diameter']
}]}
(OUT / 'problem.json').write_text(json.dumps(problem, indent=2, ensure_ascii=False) + '\n')
(OUT / 'manifest.json').write_text(json.dumps({'mathlib_rev': PIN, 'files': manifest}, indent=2) + '\n')
records = []
for filename in ('solution.lean', 'standalone.lean'):
    path = OUT / filename
    start = time.monotonic()
    process = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                             text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
    elapsed = time.monotonic() - start
    (OUT / (filename + '.log')).write_text(process.stdout)
    data = path.read_bytes()
    record = {'file': filename, 'returncode': process.returncode, 'seconds': elapsed,
              'bytes': len(data), 'lines': len(data.splitlines()),
              'sha256': hashlib.sha256(data).hexdigest(), 'axiom_report': process.stdout}
    records.append(record)
    print(json.dumps(record, ensure_ascii=False), flush=True)
    (OUT / 'verification.json').write_text(json.dumps({'mathlib_rev': PIN, 'checks': records}, indent=2) + '\n')
    if process.returncode or 'sorryAx' in process.stdout:
        raise SystemExit('Exact proof failed compilation or axiom audit: ' + filename)
(OUT / 'README.md').write_text('''# Full clipped-diameter theorem

The exact solution and standalone files are independently compiled in the pinned environment.
All local proof helpers are inlined. No theorem stubs are imported. Standard classical Lean axioms
are allowed, but sorryAx is not. The publication JSON contains the platform-required placeholder
for a problem declaration, not an admission in the proof. This script does not publish anything.
An authorized agent must first check for equivalent results and then publish/verify the exact
solution.lean in the pinned environment. Do not submit this as the unrestricted polynomial leaf.
''')
