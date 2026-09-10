#!/usr/bin/env python3
"""Flatten the bounded simultaneous-clipping proof into a standalone Prove2Me solution."""
from __future__ import annotations
import hashlib, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = 'Solutions.PolynomialSimultaneousClipDiameter'
ADAPTER = ROOT / 'Solutions/Sol_Hirsch_simultaneous_clipping_diameter_of_compact_outer.lean'
OUT = Path(sys.argv[1] if len(sys.argv) > 1 else '/tmp/bounded-solution.lean')
MANIFEST = Path(sys.argv[2] if len(sys.argv) > 2 else '/tmp/bounded-manifest.json')
seen:set[str]=set(); visiting:set[str]=set(); pieces:list[str]=[]; sources=[]

def visit(name:str)->None:
    if name in seen: return
    if name in visiting: raise RuntimeError('cyclic source import: '+name)
    visiting.add(name)
    p=ROOT/(name.replace('.','/')+'.lean')
    text=p.read_text(encoding='utf-8')
    body=[]
    for line in text.splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.startswith('Solutions.'): visit(dep)
                elif dep=='Definitions.Def_Hirsch_model' or dep.startswith('Mathlib'): pass
                else: raise RuntimeError('unexpected import: '+dep)
        elif not line.startswith('#print axioms '):
            body.append(line)
    joined='\n'.join(body)
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',joined,re.M):
        raise RuntimeError('unchecked source: '+name)
    anonymous=len(re.findall(r'^noncomputable section\s*$',joined,re.M))
    joined += '\nend\n' * anonymous
    pieces.append('-- BEGIN '+str(p.relative_to(ROOT))+'\n'+joined+'\n')
    sources.append({'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(text.encode()).hexdigest()})
    visiting.remove(name); seen.add(name)

visit(TARGET)
adapter=ADAPTER.read_text(encoding='utf-8')
adapter='\n'.join(line for line in adapter.splitlines() if not line.startswith('import '))+'\n'
proof='import Mathlib\nimport Definitions.Def_Hirsch_model\n\n'+'\n'.join(pieces)+adapter
if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',proof,re.M):
    raise RuntimeError('flattened proof contains forbidden declaration/admission')
OUT.write_text(proof,encoding='utf-8')
manifest={'status':'GENERATED_PENDING_COMPILE','solution_sha256':hashlib.sha256(proof.encode()).hexdigest(),'bytes':len(proof.encode()),'sources':sources}
MANIFEST.write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps(manifest,indent=2))
