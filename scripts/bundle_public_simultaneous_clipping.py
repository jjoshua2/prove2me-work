#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'public_simultaneous_clipping_packet'
TARGET = 'Solutions.Sol_Hirsch_simultaneous_clipping_diameter_bound'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PUBLIC_DEFINITION = 'Definitions.Def_Hirsch_model'


def main() -> None:
    seen, visiting, imports = set(), set(), set()
    pieces, sources = [], []

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError('cyclic local import: ' + module)
        visiting.add(module)
        path = ROOT / (module.replace('.', '/') + '.lean')
        text = path.read_text(encoding='utf-8')
        body = []
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):
                        visit(dep)
                    elif dep == PUBLIC_DEFINITION or dep == 'Mathlib' or dep.startswith('Mathlib.'):
                        imports.add(dep)
                    else:
                        raise ValueError('unexpected import: ' + dep)
            elif not line.startswith('#print axioms '):
                body.append(line)
        joined = '\n'.join(body)
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', joined, re.M):
            raise ValueError('admission or unchecked declaration: ' + module)
        anonymous = len(re.findall(r'^noncomputable section\s*$', joined, re.M))
        joined += '\nend\n' * anonymous
        pieces.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + joined + '\n')
        sources.append({'path': str(path.relative_to(ROOT)),
                        'sha256': hashlib.sha256(text.encode()).hexdigest()})
        visiting.remove(module)
        seen.add(module)

    visit(TARGET)
    if PUBLIC_DEFINITION not in imports:
        raise ValueError('public Hirsch definition import was not found')
    if any(not (dep == PUBLIC_DEFINITION or dep == 'Mathlib' or dep.startswith('Mathlib.'))
           for dep in imports):
        raise ValueError('unexpected public imports: ' + repr(imports))
    proof = '\n'.join('import ' + x for x in sorted(imports)) + '\n\n'
    proof += '\n'.join(pieces) + '\n#print axioms solution\n'
    OUT.mkdir(exist_ok=True)
    (OUT / 'solution.lean').write_text(proof, encoding='utf-8')
    manifest = {
        'mathlib_rev': PIN,
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'proposed_theorem_name': 'Hirsch.simultaneous_clipping_diameter_bound',
        'solution_sha256': hashlib.sha256(proof.encode()).hexdigest(),
        'bytes': len(proof.encode()),
        'sources': sources,
        'public_imports': sorted(imports),
        'formal_scope': 'BOUNDED_COMPACT_OUTER_SIMULTANEOUS_CLIPPING_FINAL_FACE_BUDGETS',
    }
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    main()
