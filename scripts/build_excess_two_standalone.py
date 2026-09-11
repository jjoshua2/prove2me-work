#!/usr/bin/env python3
"""Build a self-contained excess-two packet with narrowly scoped Mathlib imports.

The public theorem types use expanded Mathlib primitives, never the local
adjacency helper. Existing source bodies are copied, not imported as axioms.
The canonical Hirsch model is copied into a distinct internal namespace to
avoid redefining a platform declaration. A manifest records every source hash.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
IMPORTS = [
    'Mathlib.Analysis.InnerProductSpace.PiL2',
    'Mathlib.Analysis.Convex.Extreme', 'Mathlib.Data.Finset.Max',
    'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.NormNum', 'Mathlib.Tactic.Ring',
    'Mathlib.Tactic.FieldSimp', 'Mathlib.Tactic.Positivity',
    'Mathlib.Tactic.LinearCombination',
]
COMMON = [
    'Definitions.Def_Hirsch_model',
    'Solutions.PolynomialExcessTwoMomentSlice',
    'Solutions.PolynomialExcessTwoPairVertices',
    'Solutions.PolynomialExcessTwoSupportFaces',
]
TAIL = {
    'selector': ['Solutions.PolynomialExcessTwoVertexClassification',
                 'Solutions.Sol_Hirsch_normalized_two_moment_slice_vertex_selector'],
    'routing': ['Solutions.PolynomialExcessTwoConvexity',
                'Solutions.PolynomialExcessTwoSharedAdjacency',
                'Solutions.PolynomialExcessTwoVertexClassification',
                'Solutions.PolynomialExcessTwoDiameter',
                'Solutions.Sol_Hirsch_normalized_two_moment_slice_two_step_route'],
}
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def build(kind: str, output: Path, manifest_path: Path) -> dict:
    toolchain = (ROOT / 'lean-toolchain').read_text().strip()
    if toolchain != 'leanprover/lean4:v4.30.0':
        raise ValueError('Unexpected Lean pin')
    lake = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = [p for p in lake['packages'] if p['name'] == 'mathlib']
    if len(mathlib) != 1 or mathlib[0]['rev'] != PIN:
        raise ValueError('Unexpected Mathlib pin')
    modules = COMMON + TAIL[kind]
    seen = set()
    chunks = ['\n'.join('import ' + m for m in IMPORTS) + '\n']
    records = []
    for module in modules:
        path = ROOT / (module.replace('.', '/') + '.lean')
        raw = path.read_bytes()
        text = raw.decode('utf-8')
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line.removeprefix('import ').split():
                    if dep != 'Mathlib' and dep not in seen:
                        raise ValueError(f'Unresolved dependency {dep} in {module}')
        if module.startswith('Solutions.Sol_'):
            statement = text.split('theorem solution', 1)[1].split(':= by', 1)[0]
            if 'Hirsch' in statement:
                raise ValueError('Public type must use expanded Mathlib primitives')
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith(('import ', '#print axioms ')))
        body = body.replace('namespace Hirsch\n', 'namespace HirschExcessTwoBase\n')
        body = body.replace('end Hirsch\n', 'end HirschExcessTwoBase\n')
        if body.endswith('end Hirsch'):
            body = body[:-len('end Hirsch')] + 'end HirschExcessTwoBase'
        body = body.replace('open Set Hirsch\n', 'open Set HirschExcessTwoBase\n')
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', body):
            raise ValueError(f'Forbidden proof token in {module}')
        chunks.append(f'\n-- BEGIN {module}\n{body}\n-- END {module}\n')
        records.append({'module': module, 'source_sha256': sha(raw),
                        'inlined_body_sha256': sha(body.encode())})
        seen.add(module)
    chunks.append('\n#print axioms solution\n')
    packet = ''.join(chunks)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(packet, encoding='utf-8')
    result = {'kind': kind, 'lean_toolchain': toolchain, 'mathlib_rev': PIN,
              'source_modules': records, 'imports': IMPORTS,
              'proof_sha256': sha(output.read_bytes()),
              'public_type_has_no_local_predicates': True}
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(result, indent=2) + '\n')
    return result


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('kind', choices=TAIL)
    p.add_argument('output', type=Path)
    p.add_argument('manifest', type=Path)
    a = p.parse_args()
    print(json.dumps(build(a.kind, a.output, a.manifest), indent=2))


if __name__ == '__main__':
    main()
