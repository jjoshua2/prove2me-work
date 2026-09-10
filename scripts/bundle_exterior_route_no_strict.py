#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, shutil, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'exterior_route_no_strict_packet'
TARGET = 'Solutions.Sol_Hirsch_exterior_route_clip_diameter_no_strict'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def main() -> None:
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()
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
                    elif dep == 'Definitions.Def_Hirsch_model':
                        imports.add(dep)
                    elif dep == 'Mathlib' or dep.startswith('Mathlib.'):
                        imports.add('Mathlib')
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
    if 'Definitions.Def_Hirsch_model' not in imports:
        raise ValueError('public Hirsch definition import not found')
    proof = '\n'.join('import ' + dep for dep in sorted(imports)) + '\n\n'
    proof += '\n'.join(pieces) + '\n#print axioms solution\n'
    (OUT / 'solution.lean').write_text(proof, encoding='utf-8')
    wrapper = (ROOT / (TARGET.replace('.', '/') + '.lean')).read_text()
    manifest = {
        'mathlib_rev': PIN,
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'proposed_theorem_name': 'Hirsch.clip_diameter_from_exterior_routes_without_strict_centre',
        'formal_scope': 'GENERIC_EXTERIOR_ROUTE_TRANSFER_WITHOUT_SEPARATE_STRICT_CENTRE',
        'imports': sorted(imports),
        'sources': sources,
        'theorem_type': wrapper[wrapper.index('theorem solution'):wrapper.index(' := by')],
        'solution_sha256': hashlib.sha256(proof.encode()).hexdigest(),
        'bytes': len(proof.encode()),
    }
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({k: manifest[k] for k in ('source_commit','solution_sha256','bytes','formal_scope')}, indent=2))


if __name__ == '__main__':
    main()
