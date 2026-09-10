#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, shutil, subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'hpoly_pointed_packet'
TARGET = 'Solutions.Sol_Hirsch_pointed_finite_hpoly_clip_diameter'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
IGNORED_UNUSED_IMPORTS = {'Theorems.Thm_Hirsch_larman_bound'}
STRIP_DECLARATION_MODULE = 'Solutions.PolynomialUnboundedCutHpoly'
STRIP_DECLARATION_START = '/-- A bounded clipped H-polyhedron has a connected vertex graph'
STRIP_DECLARATION_END = '\nend HirschUnboundedCut'


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
                    elif dep in IGNORED_UNUSED_IMPORTS:
                        pass
                    else:
                        raise ValueError('unexpected import: ' + dep)
            elif not line.startswith('#print axioms '):
                body.append(line)
        joined = '\n'.join(body)
        if module == STRIP_DECLARATION_MODULE:
            start = joined.find(STRIP_DECLARATION_START)
            end = joined.find(STRIP_DECLARATION_END, start)
            if start < 0 or end < 0:
                raise ValueError('could not locate unused Larman declaration for pruning')
            joined = joined[:start] + joined[end:]
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', joined, re.M):
            raise ValueError('admission or unchecked declaration: ' + module)
        anonymous = len(re.findall(r'^noncomputable section\s*$', joined, re.M))
        joined += '\nend\n' * anonymous
        pieces.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + joined + '\n')
        sources.append({
            'path': str(path.relative_to(ROOT)),
            'sha256': hashlib.sha256(text.encode()).hexdigest(),
        })
        visiting.remove(module)
        seen.add(module)

    visit(TARGET)
    if 'Definitions.Def_Hirsch_model' not in imports:
        raise ValueError('public Hirsch definition import not found')
    proof = '\n'.join('import ' + dep for dep in sorted(imports)) + '\n\n'
    proof += '\n'.join(pieces) + '\n#print axioms solution\n'
    (OUT / 'solution.lean').write_text(proof, encoding='utf-8')
    wrapper = (ROOT / (TARGET.replace('.', '/') + '.lean')).read_text(encoding='utf-8')
    manifest = {
        'mathlib_rev': PIN,
        'source_commit': subprocess.check_output(
            ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'proposed_theorem_name': 'Hirsch.simultaneous_clip_diameter_from_pointed_finite_hpoly',
        'formal_scope': 'GEOMETRIC_POINTED_FINITE_HPOLY_SIMULTANEOUS_CLIPPING',
        'imports': sorted(imports),
        'ignored_unused_imports': sorted(IGNORED_UNUSED_IMPORTS),
        'stripped_unused_declaration_module': STRIP_DECLARATION_MODULE,
        'sources': sources,
        'theorem_type': wrapper[wrapper.index('theorem solution'):wrapper.index(' := by')],
        'solution_sha256': hashlib.sha256(proof.encode()).hexdigest(),
        'bytes': len(proof.encode()),
    }
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({k: manifest[k] for k in
        ('source_commit', 'solution_sha256', 'bytes', 'formal_scope')}, indent=2))


if __name__ == '__main__':
    main()
