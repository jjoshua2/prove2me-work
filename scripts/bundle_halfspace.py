#!/usr/bin/env python3
"""Produce exact cut-face submission bytes. No API writes or credentials."""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'halfspace_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.cut_face_access_of_outer_diameter'
TARGET = 'Solutions.PolynomialHalfspaceAccessSubmission'
seen, imports, parts, manifest = set(), set(), [], []

def visit(mod):
    if mod in seen: return
    seen.add(mod)
    path=ROOT/(mod.replace('.', '/')+'.lean'); text=path.read_text()
    for line in text.splitlines():
        if line.startswith('import '):
            for dep in line[7:].split():
                if dep.startswith('Solutions.'): visit(dep)
                else:
                    if dep.startswith('Theorems.'): raise RuntimeError('Theorem stub import '+dep)
                    imports.add(dep)
    body='\n'.join(s for s in text.splitlines() if not s.startswith('import ') and not s.startswith('#print axioms '))
    if re.search(r'^noncomputable section\s*$',body,re.M): body+='\nend\n'
    if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s',body,re.M):
        raise RuntimeError('Admission-like token in '+mod)
    parts.append('-- BEGIN '+str(path.relative_to(ROOT))+'\n'+body+'\n')
    manifest.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(text.encode()).hexdigest()})

visit(TARGET)
OUT.mkdir(exist_ok=True)
proof='\n'.join('import '+s for s in sorted(imports))+'\n\n'+'\n'.join(parts)+'\n#print axioms solution\n'
(OUT/'solution.lean').write_text(proof)
model=(ROOT/'Definitions/Def_Hirsch_model.lean').read_text()
model='\n'.join(s for s in model.splitlines() if not s.startswith('import '))
standalone='import Mathlib\n'+model+'\n'+proof.replace('import Mathlib\n','').replace('import Definitions.Def_Hirsch_model\n','')
(OUT/'standalone.lean').write_text(standalone)
source=(ROOT/(TARGET.replace('.', '/')+'.lean')).read_text()
signature=source.split('theorem solution',1)[1].split(':= by',1)[0].strip()
problem={'env':PIN,'problems':[{
    'theorem_name':NAME,
    'theorem_title':'A halfspace cut inherits an outer diameter budget for reaching its new face',
    'preamble':'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
    'formal_statement':'theorem '+NAME+'\n    '+signature+' := by sorry',
    'natural_language_statement':
      'Let Q be a subset of R^d with padded vertex-edge diameter at most B. Let u be an extreme point of Q satisfying <c,u><=b and let v be an extreme point of Q satisfying b<=<c,v>. '
      'Then in P=Q intersect {x:<c,x><=b}, an extreme point on the SPECIFIED new cut plane <c,x>=b is reachable from u in at most B padded edge steps. '
      'If u is on the cut, use a constant walk. Otherwise follow any B-step Q-walk to v until its first contact or crossing, retain its earlier edges and clip the crossing edge at the cut plane. '
      'The bound has no additive loss. The outer walk need not be monotone. The hypothesis explicitly requires that the source was a vertex of Q, not merely a vertex created by clipping. '
      'The conclusion does not select a particular cut-face vertex, does not concern an arbitrary old supporting face, and does not bound the entire diameter of P. '
      'No convexity or boundedness assumption is separately needed for this path-transfer statement because actual Adj edges and the outer diameter hypothesis supply the required geometry.',
    'source':'Working derivation for the Polynomial Hirsch mission. jjoshua2/prove2me-work branch chatgpt/halfspace-routing; exact segment clipping and first-crossing proof. No literature-priority claim.',
    'tags':['convex-geometry','polytopes','supporting-face']}]}
(OUT/'problem.json').write_text(json.dumps(problem,indent=2,ensure_ascii=False)+'\n')
(OUT/'manifest.json').write_text(json.dumps({'mathlib_rev':PIN,'files':manifest,'imports':sorted(imports),'solution_sha256':hashlib.sha256(proof.encode()).hexdigest()},indent=2)+'\n')
(OUT/'README.md').write_text('''# Cut-face access proof packet

solution.lean is the exact top-level theorem solution, with all helpers inlined.
standalone.lean also inlines the Hirsch model. Both files import no theorem
placeholders and must have only propext, Classical.choice, and Quot.sound as
axioms. problem.json carries the platform-required placeholder for a new
problem declaration; this is not present in either proof file.

This theorem transfers an ASSUMED outer diameter budget to the specified new
cut face, from a retained original vertex. It does not prove the unrestricted
polynomial Hirsch leaf or a diameter bound for the whole clipped polytope.
An authorized local agent should check for equivalent public results and
submit the checked bytes in the recorded environment only if appropriate.
The bundler performs no API writes.
''')
print('BUNDLED',len(proof.encode()),hashlib.sha256(proof.encode()).hexdigest())
