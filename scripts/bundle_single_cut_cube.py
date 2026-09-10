#!/usr/bin/env python3
"""Produce and independently compile a closed proof; never publishes implicitly."""
from __future__ import annotations
import hashlib,json,re,subprocess,time,shutil
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'cube_packet'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET='Solutions.SingleCutCubeSubmission'
NAME='Hirsch.single_halfspace_cube_diameter_le_dim_add_two'
seen=set();parts=[];imports=set();manifest=[]
def visit(module):
    if module in seen:return
    seen.add(module)
    path=ROOT/(module.replace('.','/')+'.lean')
    text=path.read_text()
    for line in text.splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.startswith('Solutions.'):visit(dep)
                elif dep.startswith('Theorems.'):raise RuntimeError('External theorem stub: '+dep)
                else:imports.add(dep)
    body='\n'.join(l for l in text.splitlines() if not l.startswith('import ') and not l.startswith('#print axioms '))
    if re.search(r'^noncomputable section\s*$',body,re.M):body+='\nend\n'
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',body,re.M):raise RuntimeError('Admission in '+module)
    parts.append('-- BEGIN '+str(path.relative_to(ROOT))+'\n'+body+'\n')
    manifest.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(text.encode()).hexdigest()})
visit(TARGET)
OUT.mkdir(exist_ok=True)
proof='\n'.join('import '+m for m in sorted(imports))+'\n'+'\n'.join(parts)+'\n#print axioms solution\n'
(OUT/'solution.lean').write_text(proof)
model=(ROOT/'Definitions/Def_Hirsch_model.lean').read_text()
model='\n'.join(l for l in model.splitlines() if not l.startswith('import '))
standalone='import Mathlib\n'+model+'\n'+proof.replace('import Mathlib\n','').replace('import Definitions.Def_Hirsch_model\n','')
(OUT/'standalone.lean').write_text(standalone)
source=(ROOT/(TARGET.replace('.','/')+'.lean')).read_text()
statement='theorem '+NAME+source.split('theorem solution',1)[1].split(':= by',1)[0].rstrip()+' := by sorry'
problem={'env':PIN,'problems':[{'theorem_name':NAME,'theorem_title':'A cube cut by one real halfspace has diameter at most d+2','formal_statement':statement,'preamble':'import Mathlib\nimport Definitions.Def_Hirsch_model','natural_language_statement':'For every natural d, every real coefficient vector a, and every real beta, the vertex-edge graph of {x in R^d: 0<=x_i<=1 for all i and sum_i a_i*x_i<=beta} has diameter at most d+2. This is the continuous polytope, not its integer hull. No sign, genericity, rank, integrality, nonemptiness, full-dimensionality, or assumed diameter bound is needed. Empty and zero-dimensional cases are included. Fin d -> R is the finite real coordinate vector space; the graph notion is the published Hirsch.Adj. This is a restricted concrete class, not the general polynomial Hirsch conjecture; optimality is not claimed.','source':'Working derivation for the Polynomial Hirsch mission in jjoshua2/prove2me-work, branch chatgpt/single-cut-cube. Related vertex classification: Black and Steiner, Finding Short Paths On Simple Polytopes, arXiv:2603.05482v1, Lemma 2.2. No literature-priority claim.','tags':['convex-geometry','polytopes']}]}
(OUT/'problem.json').write_text(json.dumps(problem,indent=2,ensure_ascii=False)+'\n')
(OUT/'manifest.json').write_text(json.dumps({'mathlib_rev':PIN,'modules':manifest},indent=2)+'\n')
shutil.copyfile(ROOT/'research/SingleCutCubeProof.md',OUT/'EXPLANATION.md')
shutil.copyfile(ROOT/'scripts/submit_checked_packet.py',OUT/'submit_checked.py')
report={}
for name in ['solution.lean','standalone.lean']:
    p=OUT/name;t=time.monotonic()
    run=subprocess.run([str(Path.home()/'.elan/bin/lake'),'env','lean','-DautoImplicit=false',str(p)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-t
    (OUT/(name+'.audit.log')).write_text(run.stdout)
    print(run.stdout,flush=True)
    if run.returncode:raise SystemExit(run.returncode)
    m=re.search(r"'solution' depends on axioms:\s*\[([^]]*)\]",run.stdout)
    if not m:raise RuntimeError('Missing axiom audit')
    axioms={x.strip() for x in m.group(1).split(',') if x.strip()}
    if not axioms<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('Unexpected axioms: '+repr(axioms))
    data=p.read_bytes()
    report[name]={'compiled':True,'autoImplicit':False,'axioms':sorted(axioms),'seconds':elapsed,'lines':len(data.splitlines()),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('CLOSED_CUBE_THEOREM_CHECKED',json.dumps(report),flush=True)
