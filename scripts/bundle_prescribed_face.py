#!/usr/bin/env python3
"""Create two reproducible proof packets. No authenticated writes or publication."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'prescribed_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
CONFIGS = [
    ('access', 'Solutions.PolynomialPrescribedFaceSubmission',
     'Hirsch.given_supporting_face_access_of_boundary_new_rank',
     'Prescribed supporting-face access under a boundary-local new-normal rank bound',
     'Let P be a bounded H-polytope described by n inequalities, with vertices u,v. '
     'Fix a describing row i tight at v. At every edge x-z entering its supporting '
     'face from outside, assume that all nonzero normals active at x but not at u '
     'are contained in some subspace K of dimension at most r. K may depend on x,z. '
     'Then an extreme point on THAT prescribed supporting face is reachable from '
     'u in at most n*2^max(r-3,0)+1 padded edge steps. Normals of other target rows '
     'are included if newly active: neutral rank alone is not this hypothesis. '
     'No endpoint separation or distinctness is needed. This is a restricted '
     'access theorem, not a proof of the unconditional polynomial Hirsch leaf.'),
    ('exposure', 'Solutions.PolynomialVertexExposureSubmission',
     'Hirsch.vertex_exposing_redundant_row_extension',
     'A vertex-exposing redundant row preserves the polytope and endpoint separation',
     'For a finite H-polytope, a vertex v and a distinct feasible point u with '
     'no nonzero describing row tight at both, append one nonzero inequality '
     'which is tight precisely at v among feasible points and is strict at u. '
     'All old rows and the feasible set are preserved exactly, as is endpoint '
     'separation. The new row is tight at v and hence is not neutral. Thus the '
     'graph and all old neutral normals remain unchanged, but access to the '
     'specified new row is exactly access to v. Boundedness is not required. '
     'The exposing normal is the sum of the original normals active at v.')
]


def build_packet(key: str, target: str, name: str, title: str, natural: str) -> None:
    seen: set[str] = set()
    imports: set[str] = set()
    parts: list[str] = []
    manifest: list[dict[str, str]] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = ROOT / (module.replace('.', '/') + '.lean')
        text = path.read_text(encoding='utf-8')
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):
                        visit(dep)
                    else:
                        if dep.startswith('Theorems.') and dep != 'Theorems.Thm_Hirsch_larman_bound':
                            raise RuntimeError('Unexpected theorem dependency: ' + dep)
                        imports.add(dep)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith('import ') and not line.startswith('#print axioms '))
        if re.search(r'^noncomputable section\s*$', body, re.MULTILINE):
            body += '\nend\n'
        if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b', body):
            raise RuntimeError('Unexpected unchecked code: ' + module)
        parts.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
        manifest.append({'path': str(path.relative_to(ROOT)),
                         'sha256': hashlib.sha256(text.encode()).hexdigest()})

    visit(target)
    if key == 'exposure' and any(i.startswith('Theorems.') for i in imports):
        raise RuntimeError('Exposure theorem must have no theorem-stub imports')
    text = '\n'.join('import ' + i for i in sorted(imports)) + '\n' + '\n'.join(parts)
    text += '\n#print axioms solution\n'
    dest = OUT / key
    dest.mkdir(parents=True, exist_ok=True)
    (dest / 'solution.lean').write_text(text, encoding='utf-8')
    src = (ROOT / (target.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
    statement = 'theorem ' + name + src.split('theorem solution', 1)[1].split(':= by', 1)[0]
    statement = statement.rstrip() + ' := by sorry'
    problem = {'env': PIN, 'problems': [{
        'theorem_name': name, 'theorem_title': title,
        'formal_statement': statement,
        'preamble': 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
        'natural_language_statement': natural,
        'source': 'Working result for the Polynomial Hirsch mission, September 2026. Exact checked source in jjoshua2/prove2me-work, branch chatgpt/prescribed-face-rank. No literature-priority claim.',
        'tags': ['convex-geometry', 'polytopes']
    }]}
    (dest / 'problem.json').write_text(json.dumps(problem, indent=2, ensure_ascii=False) + '\n')
    (dest / 'manifest.json').write_text(json.dumps({
        'mathlib_rev': PIN, 'target': target, 'imports': sorted(imports),
        'files': manifest, 'solution_sha256': hashlib.sha256(text.encode()).hexdigest()
    }, indent=2) + '\n')
    (dest / 'README.md').write_text(
        '# ' + title + '\n\n' + natural + '\n\n'
        'The exact proof imports only Mathlib and the published Hirsch model' +
        (', plus the public Proved Larman theorem. The local Larman stub causes '
         'sorryAx in a local audit; the proof text itself contains no admissions. '
         'All geometric helpers are independently admission-free.\n\n' if key == 'access'
         else '. No theorem stubs are imported; the exact proof must have only '
              'propext, Classical.choice and Quot.sound as axioms.\n\n') +
        'The publication JSON contains the required statement placeholder, not a '
        'proof admission. This packet has NOT been submitted to Prove2Me. An '
        'authorized local agent must first inspect the exact statement, confirm '
        'public dependencies in the pinned environment, search for equivalent '
        'results, then publish and verify this exact solution. Never submit either '
        'restricted result as the unrestricted polynomial-access leaf.\n'
    )
    print(key, len(text.encode()), hashlib.sha256(text.encode()).hexdigest())


if __name__ == '__main__':
    for config in CONFIGS:
        build_packet(*config)
