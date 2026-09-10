#!/usr/bin/env python3
"""Package a checked proof; never publishes or reads credentials."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'local_rank_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET = 'Solutions.PolynomialLocalRankSubmission'
NAME = 'Hirsch.target_face_access_of_local_neutral_rank'
ALLOWED_PUBLIC = {'Theorems.Thm_Hirsch_larman_bound'}
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
            for dep in line[len('import '):].split():
                if dep.startswith('Solutions.'):
                    visit(dep)
                else:
                    if dep.startswith('Theorems.') and dep not in ALLOWED_PUBLIC:
                        raise RuntimeError('Unexpected public theorem dependency: ' + dep)
                    imports.add(dep)
    body = '\n'.join(line for line in text.splitlines()
                     if not line.startswith('import ') and not line.startswith('#print axioms '))
    if re.search(r'^noncomputable section\s*$', body, re.MULTILINE):
        body += '\nend\n'
    if re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide)\b', body):
        raise RuntimeError('Unexpected admission or opaque declaration: ' + module)
    parts.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
    manifest.append({'path': str(path.relative_to(ROOT)),
                     'sha256': hashlib.sha256(text.encode()).hexdigest()})


visit(TARGET)
OUT.mkdir(exist_ok=True)
header = '\n'.join('import ' + name for name in sorted(imports)) + '\n'
bundle = header + '\n'.join(parts) + (
    '\n#print axioms HirschPolynomialAccess.target_face_access_of_local_neutral_rank_core\n'
    '#print axioms solution\n')
(OUT / 'solution.lean').write_text(bundle, encoding='utf-8')
source = (ROOT / 'Solutions/PolynomialLocalRankSubmission.lean').read_text(encoding='utf-8')
signature = source.split('theorem solution', 1)[1].split(':= by', 1)[0].rstrip()
statement = 'theorem ' + NAME + signature + ' := by sorry'
problem = {'env': PIN, 'problems': [{
    'theorem_name': NAME,
    'theorem_title': 'Target supporting-face access controlled by local active neutral rank',
    'formal_statement': statement,
    'preamble': 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
    'natural_language_statement': (
        'Let P be a nonempty bounded H-polytope described by n inequalities in R^d, '
        'and u,v distinct extreme points. Assume that at every extreme point x '
        'avoiding all nonzero supporting rows tight at v, the nonzero row normals '
        'active at x but active at neither u nor v belong to a linear subspace '
        'K_x of dimension at most r. K_x may vary with x. Then some extreme point '
        'z on some nonzero supporting row tight at v can be reached from u by a '
        'padded edge walk of length n*2^(max(r-3,0))+1. No separation assumption '
        'is required: a source already on a target row is handled by a constant '
        'walk. In particular r<=3 gives n+1 steps; r bounded logarithmically '
        'in n gives a polynomial estimate. This is not a uniform polynomial '
        'Hirsch bound, not access to an arbitrarily prescribed row, and not a '
        'walk to v. The number n counts describing rows, not necessarily '
        'irredundant facets. The accepted parallel-neutral two-edge theorem '
        'is sharper at rank one; this result extends the method to local '
        'subspaces of arbitrary finite rank.'),
    'source': 'Working derivation for the Polynomial Hirsch mission, 2026-09-06, jjoshua2/prove2me-work branch chatgpt/local-neutral-rank. Uses the public proved Hirsch.larman_bound. No literature priority claim.',
    'tags': ['convex-geometry', 'polytopes']
}]}
(OUT / 'problem.json').write_text(json.dumps(problem, indent=2, ensure_ascii=False) + '\n')
(OUT / 'manifest.json').write_text(json.dumps({
    'mathlib_rev': PIN, 'files': manifest,
    'solution_sha256': hashlib.sha256(bundle.encode()).hexdigest(),
    'public_theorem_dependencies': ['Hirsch.larman_bound'],
    'trust_note': 'The geometric core has no admitted imports. The final solution uses the public Proved Larman theorem through the workspace theorem stub. Local compilation does not replace platform verification.'
}, indent=2) + '\n')
(OUT / 'README.md').write_text('''# Local active-neutral-rank proof packet

This is a new restricted access theorem, not a proof of the open
`Hirsch.polynomial_access_to_given_supporting_face` leaf.

`solution.lean` inlines every local proof helper and imports only Mathlib,
the public Hirsch model, and the public proved `Hirsch.larman_bound`.
The geometric core is audited separately and must depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
The final solution compiles against the local Larman theorem stub; its
reported `sorryAx` is that already-proved imported theorem, not an admission
in the submitted proof. The platform must resolve this import and verify
this exact proof file. No full platform verification is implied by CI.

`problem.json` has the exact declaration and pinned environment. Its
statement placeholder is required for publishing a new problem; the proof
file contains no admissions. Search the live platform for equivalent
results before publishing. Do not publish a speculative decomposition.

The hypothesis is LOCAL: only active neutral normals at each avoiding
vertex are constrained, and their containing rank-r subspace may vary.
The conclusion chooses SOME target supporting row. Inactive neutral normals
and the target vertex are not asserted to be reached by the short walk.

To reproduce:

    lake build Solutions.PolynomialLocalRankSubmission
    python3 scripts/bundle_local_neutral_rank.py
    lake env lean local_rank_packet/solution.lean

Submit the exact bundled solution after checking the live public Larman
status and for an equivalent existing theorem. Do not import the new target
into its own proof. Credentials remain in the local gitignored workspace.
''')
print('LOCAL_RANK_PACKET', OUT)
print('SOLUTION_BYTES', len(bundle.encode()))
