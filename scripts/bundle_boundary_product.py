#!/usr/bin/env python3
"""Reproducible exact proof packets. Does not publish or access credentials."""
from pathlib import Path
import hashlib, json, re
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'boundary_product_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.given_supporting_face_access_of_boundary_product_factors'
TARGET = 'Solutions.PolynomialBoundaryProductSubmission'

def bundle(roots, prints):
    seen, imports, bodies, manifest = set(), set(), [], []
    def visit(mod):
        if mod in seen: return
        seen.add(mod)
        path = ROOT / (mod.replace('.', '/') + '.lean')
        text = path.read_text()
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'): visit(dep)
                    else:
                        if dep.startswith('Theorems.') and dep != 'Theorems.Thm_Hirsch_larman_bound':
                            raise RuntimeError('Unexpected external theorem: ' + dep)
                        imports.add(dep)
        body = '\n'.join(s for s in text.splitlines() if not s.startswith('import ') and not s.startswith('#print axioms '))
        if re.search(r'^noncomputable section\s*$', body, re.M): body += '\nend\n'
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s', body, re.M):
            raise RuntimeError('Admission-like token: ' + mod)
        bodies.append('-- BEGIN ' + str(path.relative_to(ROOT)) + '\n' + body + '\n')
        manifest.append({'path':str(path.relative_to(ROOT)), 'sha256':hashlib.sha256(text.encode()).hexdigest()})
    for mod in roots: visit(mod)
    text = '\n'.join('import ' + x for x in sorted(imports)) + '\n\n' + '\n'.join(bodies)
    text += '\n' + '\n'.join('#print axioms ' + x for x in prints) + '\n'
    return text, manifest, sorted(imports)

OUT.mkdir(exist_ok=True)
proof, manifest, imports = bundle([TARGET], ['solution'])
core, core_manifest, core_imports = bundle(['Solutions.PolynomialAffineProductFace','Solutions.PolynomialBoundaryWalk'],
    ['HirschProduct.diamLE_pi','HirschProduct.walk_via_affine_face','HirschProduct.access_of_boundary_walks'])
if any(s.startswith('Theorems.') for s in core_imports): raise RuntimeError('Stub in geometric core')
(OUT/'solution.lean').write_text(proof)
(OUT/'geometry.lean').write_text(core)
source = (ROOT/(TARGET.replace('.', '/')+'.lean')).read_text()
signature = source.split('theorem solution',1)[1].split(':= by',1)[0].strip()
statement = 'theorem '+NAME+'\n    '+signature+' := by sorry'
problem = {'env':PIN,'problems':[{
    'theorem_name':NAME,
    'theorem_title':'Prescribed supporting-face access through affine products of small factors',
    'preamble':'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch',
    'formal_statement':statement,
    'natural_language_statement':
      'Fix a describing row i tight at a vertex v of a bounded n-row H-polytope P in R^d and a source vertex u. '
      'Suppose for every edge x-z entering the prescribed equality face i, there is an injective affine chart of a finite Cartesian product of bounded H-polytopes whose image is an extreme subset of P containing u and x. '
      'The factors may depend on the crossing. Each factor dimension is at most r; the sum of their describing-row counts is at most M. '
      'Then an extreme point on the SAME prescribed row i is reached from u in M*2^(max(r-3,0))+1 padded edge steps. '
      'Total face dimension and residual rank are not bounded by r. If r<=3 the budget is M+1. '
      'The empty product is allowed. No separation or distinctness hypothesis is needed. '
      'This does not assert that arbitrary common-source faces have a small-factor product structure and does not prove an unrestricted polynomial Hirsch bound.',
    'source':'Working derivation, jjoshua2/prove2me-work branch chatgpt/boundary-product-access. Standard additive product-diameter construction applied locally to first-contact faces. No literature-priority claim.',
    'tags':['convex-geometry','polytopes','supporting-face']}]}
(OUT/'problem.json').write_text(json.dumps(problem,indent=2,ensure_ascii=False)+'\n')
(OUT/'manifest.json').write_text(json.dumps({'mathlib_rev':PIN,'files':manifest,'imports':imports,
    'solution_sha256':hashlib.sha256(proof.encode()).hexdigest()},indent=2)+'\n')
(OUT/'README.md').write_text('''# Boundary product-face access

The exact proof is solution.lean; publication metadata is problem.json.
The declaration JSON uses the platform-required problem placeholder. The proof
files contain no admissions. geometry.lean imports no theorem placeholders.
The final proof uses only the public Proved Larman theorem as an external lemma;
its local theorem stub introduces sorryAx until resolved by platform verification.
CI must compile these exact bytes and record their hashes and axiom reports.

An authorized agent must search for equivalent results before publication,
confirm the Larman dependency and pinned environment, and submit only this
restricted theorem. This packet is not a proof of the open polynomial leaf.
No publication or verification API request is made by this bundler.
''')
print('BUNDLED',len(proof.encode()),'bytes',hashlib.sha256(proof.encode()).hexdigest())
