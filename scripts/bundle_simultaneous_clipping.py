#!/usr/bin/env python3
"""Offline-only source/standalone packet; no network, registration, or submission."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'clipping_offline_packet'
TARGET = 'Solutions.Sol_Hirsch_simultaneous_clip_diameter'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def main() -> None:
    seen: set[str] = set()
    visiting: set[str] = set()
    imports: set[str] = set()
    pieces: list[str] = []
    sources: list[dict[str, str]] = []
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir()

    def copy_source(path: Path) -> None:
        relative = path.relative_to(ROOT)
        dest = OUT / 'sources' / relative
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, dest)

    def visit(module: str) -> None:
        if module in seen:
            return
        if module in visiting:
            raise ValueError('Cyclic local import: ' + module)
        visiting.add(module)
        path = ROOT / (module.replace('.', '/') + '.lean')
        text = path.read_text(encoding='utf-8')
        body: list[str] = []
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):
                        visit(dep)
                    elif dep == 'Mathlib' or dep.startswith('Mathlib.'):
                        imports.add('Mathlib')
                    elif dep == 'Definitions.Def_Hirsch_model':
                        imports.add(dep)
                        copy_source(ROOT / 'Definitions/Def_Hirsch_model.lean')
                    else:
                        raise ValueError('Unexpected external import: ' + dep)
            elif not line.startswith('#print axioms '):
                body.append(line)
        joined = '\n'.join(body)
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', joined, re.M):
            raise ValueError('Admission or unchecked declaration: ' + module)
        anonymous = len(re.findall(r'^noncomputable section\s*$', joined, re.M))
        if anonymous and re.search(r'^end\s*$', joined, re.M):
            raise ValueError('Anonymous-section closure requires manual review: ' + module)
        joined += '\nend\n' * anonymous
        pieces.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + joined + '\n')
        sources.append({'path': str(path.relative_to(ROOT)),
                        'sha256': hashlib.sha256(text.encode()).hexdigest()})
        copy_source(path)
        visiting.remove(module)
        seen.add(module)

    visit(TARGET)
    proof = '\n'.join('import ' + dep for dep in sorted(imports)) + '\n\n'
    proof += '\n'.join(pieces) + '\n#print axioms solution\n'
    (OUT / 'solution.lean').write_text(proof, encoding='utf-8')
    original = (ROOT / (TARGET.replace('.', '/') + '.lean')).read_text()
    manifest = {
        'mathlib_rev': PIN,
        'lean_toolchain': (ROOT / 'lean-toolchain').read_text().strip(),
        'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
        'proposed_theorem_name': 'Hirsch.simultaneous_clip_diameter_le_outer_add_final_faces',
        'publication_status': 'NOT_SUBMITTED_USER_HANDLES_PUBLICATION',
        'imports': sorted(imports),
        'sources': sources,
        'theorem_type': original[original.index('theorem solution'):original.index(' := by')],
        'solution_sha256': hashlib.sha256(proof.encode()).hexdigest(),
        'bytes': len(proof.encode()),
    }
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    for relative in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json',
                     'scripts/check_lean_axiom_log.py', 'scripts/bundle_simultaneous_clipping.py',
                     'scripts/test_face_preserving_checkpoints.py',
                     'scripts/test_full_clipping_diameter.py',
                     'research/FullSimultaneousClipping.md',
                     'research/full_clipping_regression.json']:
        path = ROOT / relative
        if path.exists():
            copy_source(path)
    print(json.dumps({k: manifest[k] for k in
          ('source_commit', 'solution_sha256', 'bytes', 'publication_status')}, indent=2))


if __name__ == '__main__':
    main()
