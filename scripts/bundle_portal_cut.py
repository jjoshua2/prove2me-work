#!/usr/bin/env python3
"""Build an offline standalone proof packet; never contacts Prove2Me."""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'portal_cut_packet'
TARGET = 'Solutions.Sol_Hirsch_mixed_repair_route_or_cut'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'


def main() -> None:
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
                    elif dep.startswith('Mathlib') or dep == 'Definitions.Def_Hirsch_model':
                        imports.add(dep)
                    else:
                        raise ValueError('Unreviewed external dependency: ' + dep)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith('import ') and not line.startswith('#print axioms '))
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', body, re.M):
            raise ValueError('Unacceptable proof declaration in ' + module)
        # Every dependency in this reviewed chain has one unclosed, unnamed
        # noncomputable section. Close it before the next source file.
        if re.search(r'^noncomputable section\s*$', body, re.M):
            body += '\nend\n'
        parts.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\nsection\n' + body + '\nend\n')
        manifest.append({'path': str(path.relative_to(ROOT)),
                         'sha256': hashlib.sha256(text.encode()).hexdigest()})

    visit(TARGET)
    text = '\n'.join('import ' + x for x in sorted(imports)) + '\n\n'
    text += 'set_option maxHeartbeats 8000000\n\n' + '\n'.join(parts)
    text += '\n#print axioms solution\n'
    OUT.mkdir(exist_ok=True)
    (OUT / 'solution.lean').write_text(text, encoding='utf-8')
    data = {'mathlib_rev': PIN, 'target': TARGET, 'files': manifest,
            'solution_sha256': hashlib.sha256(text.encode()).hexdigest(),
            'bytes': len(text.encode()), 'publication': 'NOT SUBMITTED'}
    (OUT / 'manifest.json').write_text(json.dumps(data, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
