#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; OUT=ROOT/'public_interval_start_portal_packet'
TARGET='Solutions.Sol_Hirsch_face_interval_start_containment_route_bound'; PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'; ALLOWED={'Mathlib','Definitions.Def_Hirsch_model'}
def main():
    seen=set(); visiting=set(); imports=set(); pieces=[]; sources=[]
    def visit(module):
        if module in seen:return
        if module in visiting:raise ValueError('cycle '+module)
        visiting.add(module); path=ROOT/(module.replace('.','/')+'.lean'); text=path.read_text(); body=[]
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):visit(dep)
                    elif dep in ALLOWED:imports.add(dep)
                    else:raise ValueError('unexpected import '+dep)
            elif not line.startswith('#print axioms '):body.append(line)
        joined='\n'.join(body)
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',joined,re.M):raise ValueError('forbidden '+module)
        joined+='\nend\n'*len(re.findall(r'^noncomputable section\s*$',joined,re.M))
        pieces.append('-- BEGIN '+str(path.relative_to(ROOT))+'\n'+joined+'\n');sources.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(text.encode()).hexdigest()});visiting.remove(module);seen.add(module)
    visit(TARGET)
    if imports != ALLOWED:raise ValueError(repr(imports))
    proof='\n'.join('import '+x for x in sorted(imports))+'\n\n'+'\n'.join(pieces)+'\n#print axioms solution\n'
    OUT.mkdir(exist_ok=True);(OUT/'solution.lean').write_text(proof)
    m={'mathlib_rev':PIN,'source_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'solution_sha256':hashlib.sha256(proof.encode()).hexdigest(),'bytes':len(proof.encode()),'sources':sources};(OUT/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps(m,indent=2))
if __name__=='__main__':main()
