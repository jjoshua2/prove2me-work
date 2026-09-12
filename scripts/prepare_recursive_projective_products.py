#!/usr/bin/env python3
"""Freeze a standalone recursive-product definition and proof from immutable Git source."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME='Hirsch.hpoly_diameter_le_excess_of_recursive_projective_products'
DEF='Hirsch_recursive_projective_products'
DEP='Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three'
PREAMBLE=f'import Mathlib\nimport Definitions.Def_{DEF}\nopen Set Hirsch\nopen scoped RealInnerProductSpace'
BINDERS='''{d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (cert : HirschRecursiveProducts.ProductTree a b) : DiamLE (Hpoly a b) (n-d)'''
NATURAL=r'''Let $P$ be described by $n$ real linear inequalities in $\mathbb R^d$.
Suppose it has a finite recursive geometric certificate built from the following operations.
A leaf is a bounded H-polyhedron with at most three excess describing rows.
An affine step transports a certificate through an affine equivalence without
changing the dimension or number of rows. At a split, an invertible linear
coordinate map and a partition of all rows identify a source with a Cartesian
product of at least two positive-dimensional certified factors. Each factor's
row count is at least its dimension. A positive projective map
$x\mapsto x/(1+c\cdot x)$ then sends this source onto the parent with sheared
rows $a_i+b_i c$; both forward and inverse denominators are required positive
on their full feasible sets. Different nodes may use different charts.

Then the ordinary-edge graph diameter of $P$ is at most $n-d$.
Product costs add and chart/affine transport preserves them, so the sum of leaf
excesses is exactly the parent excess. There is no restriction on total excess
or tree depth beyond the existence of the finite certificate.

This is a sufficient criterion. It does not assert that arbitrary polytopes
admit such trees, or that chart discovery is efficient. The separate exact
rational search is not part of this Lean theorem. Natural subtraction and
stationary walk steps follow the Hirsch model's padded diameter convention.'''
EXPLANATION=r'''Induct on the geometric ProductTree. At a leaf, apply the already-Proved
small-excess H-polyhedron theorem. At an affine node, transport extreme points,
ordinary edges and the padded walk through the given affine equivalence.
At a split, use the inductively obtained factor bounds and the Cartesian-product
walk construction to add their costs. The row and coordinate equivalences imply
sum_i(counts_i-dims_i)=n-d. The row identities identify the feasible product with
the source polyhedron. Finally transport this exact cost through the positive
projective chart, proving its inverse, slack scaling, segment/extreme-set and
ordinary-edge preservation explicitly.

The submitted proof contains the transport, product-walk and row-count proofs.
Its only imported diameter theorem is the already-Proved excess-at-most-three
bound. The separate local driver retains this input as an explicit premise and
has a standard-axiom audit. The registered ProductTree definition has only
geometric constructors; it does not contain a diameter-bound premise.

No recognition-completeness, JSON-to-Lean certificate translation, universal
carrier factorization or resolution of Polynomial Hirsch is claimed here.'''

def prepare(source: str,out: Path)->None:
    source=subprocess.check_output(['git','rev-parse',source],text=True).strip()
    blobs={}
    def blob(path):
        blobs[path]=subprocess.check_output(['git','rev-parse',source+':'+path],text=True).strip()
        return subprocess.check_output(['git','show',source+':'+path],text=True)
    def body(module):
        return '\n'.join(line for line in blob('Solutions/'+module+'.lean').splitlines()
                         if not line.startswith('import ') and not line.startswith('#print axioms'))+'\n'
    def before(s,declaration):
        return s[:s.rfind('/--',0,s.index(declaration))]
    prefix=PREAMBLE+'\n'
    for mod in ['PolynomialProductWalk','PolynomialSegmentChartTransport','PolynomialPositivePerspective']:
        prefix+=body(mod)+'\nend\n'
    prefix+=before(body('PolynomialAffineDiameterTransport'),
                   'theorem affineMap_isExtreme_image_iff_of_injective')+'\nend Hirsch\n'
    prefix+=before(body('PolynomialRowBlockRouting'),
                   'theorem hpoly_diamLE_excess_of_small_row_blocks')+'\nend HirschRowBlocks\nend\n'
    prefix+=before(body('PolynomialProjectiveRowBlockRouting'),
                   'theorem positiveDomain_of_row_multipliers')+'\nend HirschProjectiveBlocks\nend\n'
    prefix+=before(body('PolynomialRecursiveProjectiveProducts'),
                   'theorem carrier_diamLE_rows_of_recursive_projective_model')+'\nend HirschRecursiveProducts\nend\n'
    driver=prefix+'\n#print axioms HirschRecursiveProducts.ProductTree.diamLE\n'
    dep_module=DEP.replace('.', '_')
    solution=(f'import Theorems.Thm_{dep_module}\n'+prefix+'\ntheorem solution '+BINDERS+''' := by
  apply HirschRecursiveProducts.ProductTree.diamLE ?_ cert
  intro d n a b hbd hrows
  exact Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three d n a b hrows hbd
''')
    definition=blob('Definitions/Def_'+DEF+'.lean')
    statement='theorem '+NAME+' '+BINDERS+' := by sorry'
    origin=f'Derived geometric certificate criterion; https://github.com/jjoshua2/prove2me-work/blob/{source}/research/RECURSIVE_PROJECTIVE_DISCOVERY_2026-09-12.md sections 1-3; classical projective invariance and product graph additivity are reused, not claimed novel.'
    problem={'theorem_name':NAME,'theorem_title':'Recursive positive projective product certificates give the Hirsch row-excess bound',
             'formal_statement':statement,'natural_language_statement':NATURAL,'preamble':PREAMBLE,
             'source':origin,'tags':['polyhedra','graph-diameter','formalization'],'env':PIN}
    defproblem={'definition_name':DEF,'definition_title':'Recursive positive projective product geometry certificates',
                'definition':definition,'natural_language_statement':NATURAL.split('\n\nThen')[0]+'\n\nThis definition contains geometric data only; its diameter consequence is a separate theorem.',
                'source':origin,'tags':['polyhedra','formalization'],'env':PIN}
    files={'driver.lean':driver,'solution.lean':solution,'statement.lean':PREAMBLE+'\n'+statement+'\n',
           'definition.lean':definition,'definition.json':json.dumps(defproblem,indent=2)+'\n',
           'problem.json':json.dumps(problem,indent=2)+'\n','explanation.md':EXPLANATION+'\n'}
    out.mkdir(parents=True,exist_ok=True)
    for name,content in files.items(): (out/name).write_text(content)
    manifest={'source_commit':source,'mathlib_rev':PIN,'source_blobs':blobs,
              'public_dependencies':{DEP:'12426807-9602-4014-bd5e-c69fb43f4cb6'},
              'sha256':{name:hashlib.sha256(content.encode()).hexdigest() for name,content in files.items()}}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'source':source,'files':len(files),'proof_lines':len(solution.splitlines())}))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',required=True);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();prepare(a.source,a.out)
