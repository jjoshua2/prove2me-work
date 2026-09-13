#!/usr/bin/env python3
"""Freeze the actual-route additive-spill theorem and its explicit certificate definition."""
import argparse,hashlib,json,subprocess
from pathlib import Path
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
DEF='Hirsch_additive_portal_repair'
NAME='Hirsch.additive_portal_repair_polynomial_route'
PRE='import Mathlib\nimport Definitions.Def_'+DEF+'\nopen scoped BigOperators\nopen HirschRegionRoute HirschAdditiveAllowance'
BINDERS='''{V : Type*} {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : HirschAdditiveAllowance.AdditiveRepair R b C x y h e cost) :
    HirschRegionRoute.Route R cost x y ∧ cost ≤ C*e+(1+b*C)*h*(e-b)'''
NAT='''A finite additive repair certificate assembles actual steps of a relation R.
A leaf has excess e<=b and an actual route of cost<=C*e. A nonleaf records one
initial R-edge or stationary step, followed by child repairs. Child dimensions
strictly drop, each child excess is at most the parent e, and sibling excesses
sum to at most e+b. Internal parents have positive dimension and e>b.
Then the certificate gives an actual route of its recorded cost, and that cost
is at most C*e+(1+b*C)*h*max(e-b,0). Fixed b and C give a quadratic bound.
The certificate is a conditional interface: dimension/excess tags are not
automatically geometric, and arbitrary polytopes are not asserted to admit it.
The cyclic fixed-slack obstruction and its adaptive routes are separate work.'''
def prepare(source,out):
    source=subprocess.check_output(['git','rev-parse',source],text=True).strip();blobs={}
    def body(path):
        blobs[path]=subprocess.check_output(['git','rev-parse',source+':'+path],text=True).strip()
        s=subprocess.check_output(['git','show',source+':'+path],text=True)
        return '\n'.join(l for l in s.splitlines() if not l.startswith(('import ','#print axioms')))+'\n'
    region=body('Solutions/PolynomialRegionRouting.lean');route=region[region.index('def Route '):region.index('/-- Region intersections')]
    additive=body('Solutions/PolynomialAdditiveAllowanceRouting.lean')
    start=additive.index('inductive AdditiveRepair');end=additive.index('theorem AdditiveRepair.sound')
    repair=additive[start:end]
    definition='import Mathlib\nopen scoped BigOperators\nnamespace HirschRegionRoute\n'+route+'end HirschRegionRoute\nnamespace HirschAdditiveAllowance\nopen HirschRegionRoute\nvariable {V : Type*}\n'+repair+'end HirschAdditiveAllowance\n'
    product=body('Solutions/PolynomialProductWalk.lean');product=product[:product.index('lemma pad_walk')]+ '\nend HirschProduct\nend\n'
    product=product.replace('open Set Hirsch','open Set')
    amortized=body('Solutions/PolynomialAmortizedPortalRoutes.lean')
    amortized=amortized[:amortized.index('/-- This is a FINITE route certificate')]+ '\nend HirschAmortized\n'
    amortized=amortized.replace('open Set Hirsch HirschRegionRoute','open Set HirschRegionRoute')
    additive=additive[:start]+additive[end:]
    additive=additive.replace('open Hirsch HirschRegionRoute HirschAmortized','open HirschRegionRoute HirschAmortized')
    solution=PRE+'\n'+product+amortized+additive+'\ntheorem solution '+BINDERS+' := by\n  simpa only [allowanceBudget] using cert.sound\n'
    origin='Explicit conditional recurrence and actual-route assembly; https://github.com/jjoshua2/prove2me-work/tree/'+source
    problem={'theorem_name':NAME,'theorem_title':'Bounded additive sibling spill gives a polynomial actual route bound','formal_statement':'theorem '+NAME+' '+BINDERS+' := by sorry','preamble':PRE,'natural_language_statement':NAT,'source':origin,'tags':['polyhedra','graph-theory','formalization'],'env':PIN}
    defproblem={'definition_name':DEF,'definition_title':'Finite additive-spill repair certificates with actual leaf routes','definition':definition,'natural_language_statement':NAT.split('Then the certificate')[0]+'The tags must be separately justified when used for polytope geometry.','source':origin,'tags':['polyhedra','formalization'],'env':PIN}
    files={'solution.lean':solution,'driver.lean':solution+'\n#print axioms solution\n','statement.lean':PRE+'\ntheorem '+NAME+' '+BINDERS+' := by sorry\n','problem.json':json.dumps(problem,indent=2)+'\n','definition.lean':definition,'definition.json':json.dumps(defproblem,indent=2)+'\n','explanation.md':'''Conserve shifted child excess sum(max(e_i-b,0))<=max(e-b,0). With zero or one large child this follows from individual monotonicity; with two or more the subtraction of b per child pays the additive sibling spill. Multiply shifted mass by the strictly decreasing dimension and induct over the finite repair certificate. The polynomial potential pays the initial step and every child's budget. Concatenating the actual bounded leaf routes proves the route conclusion simultaneously. No universal geometric certificate existence is assumed or concluded, and fixed-slack portal selection is not asserted.\n'''}
    out.mkdir(parents=True,exist_ok=True)
    for n,s in files.items():(out/n).write_text(s)
    Path('Definitions/Def_'+DEF+'.lean').write_text(definition)
    (out/'manifest.json').write_text(json.dumps({'source_commit':source,'mathlib_rev':PIN,'source_blobs':blobs,'public_dependencies':{},'definition_name':DEF,'sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}},indent=2)+'\n')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();prepare(a.source,a.out)
