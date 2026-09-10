#!/usr/bin/env python3
"""Inline and independently compile the exact box-slice diameter submission."""
from __future__ import annotations
import hashlib, json, pathlib, re, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=ROOT/'pivot_packet'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET='Solutions.BoxSliceDiameter'
NAME='Hirsch.box_slice_diameter_le_dimension'
seen=set(); parts=[]; imports=set(); manifest=[]
def visit(module):
    if module in seen: return
    seen.add(module)
    path=ROOT/(module.replace('.','/')+'.lean')
    text=path.read_text()
    for line in text.splitlines():
        if line.startswith('import '):
            for name in line[7:].split():
                if name.startswith('Solutions.'): visit(name)
                elif name.startswith('Theorems.'): raise RuntimeError('Theorem stub import: '+name)
                else: imports.add(name)
    body='\n'.join(line for line in text.splitlines() if not line.startswith('import ') and not line.startswith('#print axioms '))
    if re.search(r'^noncomputable section\s*$',body,re.M): body+='\nend\n'
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',body,re.M):
        raise RuntimeError('Unexpected admission in '+module)
    parts.append('-- BEGIN '+str(path.relative_to(ROOT))+'\n'+body+'\n')
    manifest.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(text.encode()).hexdigest()})
    dst=OUT/'sources'/path.relative_to(ROOT); dst.parent.mkdir(parents=True,exist_ok=True); dst.write_text(text)
OUT.mkdir(exist_ok=True)
visit(TARGET)
header='\n'.join('import '+name for name in sorted(imports))+'\n'
proof=header+'\n'.join(parts)+'\n#print axioms HirschBoxSlice.decreasing_pivot\n#print axioms solution\n'
(OUT/'solution.lean').write_text(proof)
model=(ROOT/'Definitions/Def_Hirsch_model.lean').read_text()
model='\n'.join(l for l in model.splitlines() if not l.startswith('import '))
standalone='import Mathlib\n'+model+'\n'+proof.replace('import Mathlib\n','').replace('import Definitions.Def_Hirsch_model\n','')
(OUT/'standalone.lean').write_text(standalone)
source=(ROOT/'Solutions/BoxSliceDiameter.lean').read_text()
statement='theorem '+NAME+source.split('theorem solution',1)[1].split(':= by',1)[0]+' := by sorry'
problem={'env':PIN,'problems':[{'theorem_name':NAME,
 'theorem_title':'A box cut by one balance equation has graph diameter at most the number of coordinates',
 'formal_statement':statement,
 'preamble':'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen Set Hirsch',
 'natural_language_statement':'For any real capacities cap indexed by Fin d and any real total, the set of x with 0 <= x_k <= cap_k and sum x_k = total has vertex-edge graph diameter at most d. Negative capacities simply make it empty; zero-width coordinates and dimension zero are included. The proof constructs maximal two-coordinate edges with a strictly decreasing mismatch-plus-mixed-buffer potential. This is a restricted one-balance box theorem, not a general polynomial Hirsch bound.',
 'source':'Constructive formalization in jjoshua2/prove2me-work, chatgpt/box-slice-pivot. Related two-row transportation bounds are known; no literature-priority claim.',
 'tags':['convex-geometry','polytopes']} ]}
(OUT/'problem.json').write_text(json.dumps(problem,indent=2,ensure_ascii=False)+'\n')
allowed={'propext','Classical.choice','Quot.sound'}
report={'mathlib_rev':PIN,'commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'files':{}}
for name in ('solution.lean','standalone.lean'):
    path=OUT/name; start=time.monotonic()
    proc=subprocess.run([str(pathlib.Path.home()/'.elan/bin/lake'),'env','lean',str(path)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    elapsed=time.monotonic()-start
    (OUT/(name+'.log')).write_text(proc.stdout)
    print(proc.stdout)
    if proc.returncode: raise SystemExit(proc.returncode)
    matches=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",proc.stdout)
    audited={key:sorted({x.strip() for x in val.split(',') if x.strip()}) for key,val in matches}
    for theorem in ('HirschBoxSlice.decreasing_pivot','solution'):
        if theorem not in audited: raise RuntimeError('Missing audit '+theorem)
        if not set(audited[theorem])<=allowed: raise RuntimeError('Unexpected axioms '+repr(audited))
    report['files'][name]={'compiled':True,'seconds':round(elapsed,4),'bytes':len(path.read_bytes()),'lines':len(path.read_text().splitlines()),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'axioms':audited}
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('BOX_SLICE_PACKET_VERIFIED',json.dumps(report))
