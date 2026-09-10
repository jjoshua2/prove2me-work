#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "public_common_face_packet"
PUBLIC_DEF = "Definitions.Def_Hirsch_common_face_geometry"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
TARGETS = [
    ("tradeoff", "Solutions.Sol_Hirsch_common_face_dimension_tradeoff"),
    ("effective_count", "Solutions.Sol_Hirsch_common_face_effective_count_bound"),
    ("effective_diameter", "Solutions.Sol_Hirsch_common_face_effective_diameter"),
    ("splitter", "Solutions.Sol_Hirsch_separated_common_face_split"),
]

def make_bundle(label: str, target: str) -> dict:
    seen: set[str] = set()
    parts: list[str] = []
    imports: set[str] = set()
    manifest: list[dict[str,str]] = []

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
                        if dep.startswith('Theorems.'):
                            raise RuntimeError('unexpected theorem import: ' + dep)
                        imports.add(dep)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith('import ') and not line.startswith('#print axioms '))
        if re.search(r'^noncomputable section\s*$', body, flags=re.M):
            body += '\nend\n'
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', body, flags=re.M):
            raise RuntimeError('admission or opaque declaration in ' + module)
        parts.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
        manifest.append({'path':str(path.relative_to(ROOT)), 'sha256':hashlib.sha256(text.encode()).hexdigest()})

    visit(target)
    imports.add(PUBLIC_DEF)
    header = '\n'.join('import ' + x for x in sorted(imports)) + '\n\n'
    bundle = header + '\n'.join(parts) + '\n#print axioms solution\n'
    path = OUT / f'{label}_solution.lean'
    path.write_text(bundle, encoding='utf-8')
    return {
      'label':label,
      'target':target,
      'files':manifest,
      'solution_sha256':hashlib.sha256(bundle.encode()).hexdigest(),
      'bytes':len(bundle.encode()),
      'path':str(path.relative_to(ROOT)),
    }

OUT.mkdir(exist_ok=True)
items=[make_bundle(label,target) for label,target in TARGETS]
(OUT / 'manifest.json').write_text(json.dumps({
  'mathlib_rev':PIN,
  'public_definition':PUBLIC_DEF,
  'bundles':items,
}, indent=2) + '\n')
for item in items:
    print(item['label'], item['solution_sha256'], item['bytes'])
