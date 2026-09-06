#!/usr/bin/env python3
"""Create and independently compile two exact Prove2Me proof packets. No publication."""
from __future__ import annotations
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'unbounded_cut_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
LARMAN = 'Theorems.Thm_Hirsch_larman_bound'
LAKE = str(Path.home() / '.elan/bin/lake')


def bundle(module: str, reports: list[str], allow_larman: bool) -> tuple[str, list[dict], set[str]]:
    seen: set[str] = set()
    imports: set[str] = set()
    pieces: list[str] = []
    manifest: list[dict] = []
    def visit(name: str) -> None:
        if name in seen:
            return
        seen.add(name)
        path = ROOT / (name.replace('.', '/') + '.lean')
        text = path.read_text(encoding='utf-8')
        for line in text.splitlines():
            if line.startswith('import '):
                for item in line[7:].split():
                    if item.startswith('Solutions.'):
                        visit(item)
                    else:
                        if item.startswith('Theorems.') and (not allow_larman or item != LARMAN):
                            raise RuntimeError('Unapproved external theorem import: ' + item)
                        imports.add(item)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith('import ') and not line.startswith('#print axioms '))
        if re.search(r'^noncomputable section\s*$', body, flags=re.M):
            body += '\nend\n'
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', body, flags=re.M):
            raise RuntimeError('Admission or opaque declaration in ' + name)
        pieces.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
        manifest.append({'path': str(path.relative_to(ROOT)), 'sha256': hashlib.sha256(text.encode()).hexdigest()})
    visit(module)
    text = '\n'.join('import ' + item for item in sorted(imports)) + '\n\n' + '\n'.join(pieces)
    text += '\n' + '\n'.join('#print axioms ' + name for name in reports) + '\n'
    return text, manifest, imports


def check(path: Path, reports: list[str], allowed: set[str]) -> dict:
    start = time.monotonic()
    proc = subprocess.run([LAKE, 'env', 'lean', str(path)], cwd=ROOT,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    elapsed = time.monotonic() - start
    path.with_suffix('.audit.log').write_text(proc.stdout, encoding='utf-8')
    print(proc.stdout, flush=True)
    if proc.returncode:
        raise RuntimeError('Exact-file compilation failed: ' + str(path))
    axioms = {}
    for name in reports:
        match = re.search("'" + re.escape(name) + r"' depends on axioms:\s*\[([^]]*)\]", proc.stdout)
        if not match:
            raise RuntimeError('Missing axiom report: ' + name)
        found = {x.strip() for x in match.group(1).split(',') if x.strip()}
        if not found <= allowed:
            raise RuntimeError('Unexpected axioms: ' + repr(found - allowed))
        axioms[name] = sorted(found)
    data = path.read_bytes()
    return {'compiled': True, 'seconds': round(elapsed, 4), 'bytes': len(data),
            'lines': len(data.splitlines()), 'sha256': hashlib.sha256(data).hexdigest(), 'axioms': axioms}


OUT.mkdir(exist_ok=True)
core_reports = ['HirschUnboundedCut.cut_access_of_outer_diameter_and_path',
                'HirschUnboundedCut.clipped_diameter_of_outer_and_connected_clip']
core, core_manifest, core_imports = bundle('Solutions.PolynomialUnboundedCutCore', core_reports, False)
(OUT / 'geometry.lean').write_text(core, encoding='utf-8')
verification = {'mathlib_rev': PIN, 'geometry': check(OUT / 'geometry.lean', core_reports, STANDARD),
                'platform_submitted': False}
entries = [
    ('access', 'Solutions.PolynomialUnboundedCutAccessSubmission',
     'Hirsch.cut_face_access_of_unbounded_outer_diameter',
     'Specified cut-face access with a possibly unbounded outer H-polyhedron',
     'Let Q be an H-polyhedron described by n inequalities in R^d and P=Q intersect {x:<c,x><=beta}. '
     'Assume P is bounded and the vertex-edge graph of Q has diameter at most B. '
     'For every two extreme points u,v of P with <c,v>=beta, some extreme point z of P on the SAME '
     'specified cut plane is reachable from u by at most B+1 edges. Q need not be bounded, and no '
     'outer extreme point on or beyond the cut plane is required. No nonzero-normal or full-dimensionality '
     'hypothesis is imposed. Larman is used only for connectivity of the bounded (n+1)-row clip; '
     'its numerical bound is discarded. This does not promise reaching v or establish a uniform '
     'polynomial outer-graph diameter bound.'),
    ('diameter', 'Solutions.PolynomialUnboundedCutDiameterSubmission',
     'Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one',
     'Bounded clipped diameter is at most outer plus cut-face diameter plus one',
     'Let Q be an H-polyhedron in R^d, P=Q intersect {x:<c,x><=beta}, and F=Q intersect {x:<c,x>=beta}. '
     'If P is bounded, DiamLE Q B, and DiamLE F C, then DiamLE P (B+C+1). Q may be unbounded. '
     'No exterior outer vertex, nonempty clip, nonempty cut face, nonzero normal, or full-dimensionality '
     'assumption is required. This covers all clipped vertices, including newly created ones. '
     'It transfers two assumed bounds and does not prove the unrestricted polynomial Hirsch conjecture.')
]
for key, module, name, title, natural in entries:
    folder = OUT / key
    folder.mkdir(exist_ok=True)
    text, manifest, imports = bundle(module, ['solution'], True)
    if {s for s in imports if s.startswith('Theorems.')} != {LARMAN}:
        raise RuntimeError('The final packet must have exactly the public Larman theorem import')
    proof = folder / 'solution.lean'
    proof.write_text(text, encoding='utf-8')
    source = (ROOT / (module.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
    signature = source.split('theorem solution', 1)[1].split(':= by', 1)[0]
    statement = 'theorem ' + name + signature.rstrip() + ' := by sorry'
    problem = {'env': PIN, 'problems': [{'theorem_name': name, 'theorem_title': title,
        'formal_statement': statement,
        'preamble': 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
        'natural_language_statement': natural,
        'source': 'Working theorem for the Polynomial Hirsch mission; jjoshua2/prove2me-work, branch chatgpt/unbounded-cut-routing. No literature-priority claim.',
        'tags': ['convex-geometry', 'polytopes']}]}
    (folder / 'problem.json').write_text(json.dumps(problem, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    (folder / 'manifest.json').write_text(json.dumps({'files': manifest, 'imports': sorted(imports)}, indent=2) + '\n')
    verification[key] = check(proof, ['solution'], STANDARD | {'sorryAx'})
    verification[key]['external_theorem_dependency'] = 'Hirsch.larman_bound (public Proved); represented by local stub'
(OUT / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
(OUT / 'README.md').write_text('''# Possibly unbounded outer clipping — checked proof packets

The exact geometry.lean was independently compiled and audited with only the
standard axioms propext, Classical.choice, and Quot.sound. It imports no
external theorem stubs. Both final exact solution.lean files are independently
compiled and use only public Proved Hirsch.larman_bound externally. Their
local axiom reports include sorryAx solely from the workspace Larman stub.
All local helpers are inlined; the proof texts contain no admissions.

Problem JSON contains declaration placeholders as required for publication;
these are NOT the proof files. Platform verification must resolve the Larman
import. Nothing in this packet records a Prove2Me submission or acceptance.
An authenticated local agent must check equivalent results before publishing.

The access bound is B+1 to the specified cut face, not to a selected vertex.
The diameter bound is B+C+1 for the full bounded clip. The outer H-polyhedron
need not be bounded. These transfer assumed diameter bounds, not uniform
polynomial bounds in describing-row count. The unrestricted leaf is unchanged.
''', encoding='utf-8')
print('EXACT_PACKETS_VERIFIED', json.dumps(verification), flush=True)
