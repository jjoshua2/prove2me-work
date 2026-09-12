#!/usr/bin/env python3
"""Freeze #207's occurrence-counted near-geodesic joint-budget theorem."""
import argparse, hashlib, json, subprocess
from pathlib import Path

PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME='Hirsch.near_geodesic_occurrence_carrier_budget'
PRE='import Mathlib\nopen scoped BigOperators\nopen Set'
BINDERS='''{V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) (q : ℕ) (hp : p.length ≤ G.dist u v + q)
    (available : Finset V) (positions : Finset ℕ)
    (hpositions : ∀ k ∈ positions, k ≤ p.length) (delta : ℕ → ℕ) (e : ℕ)
    (hbudget : ∀ k ∈ positions, delta k + available.card ≤ e +
      (available.filter (fun z => z = p.getVert k ∨ G.Adj z (p.getVert k))).card) :
    (∑ k ∈ positions, delta k) + positions.card * available.card ≤
      positions.card * e + (q+3)*available.card'''
NAT='''A graph walk at most q edges above endpoint distance has at most q+3
closed-neighborhood contact positions with any fixed vertex. Count occurrence
positions, including repeated labels, and double-count contacts with any finite
available set. If each selected position satisfies the explicit pointwise
integer resource inequality, the total resource obeys the stated joint bound.
At full availability e=|A| the mass is at most (q+3)|A|.
This is a graph/resource theorem, not an unconditional polytope diameter bound.
The geometric portal-debt and simple-polytope interpretations are separate.'''
def prepare(source,out):
    source=subprocess.check_output(['git','rev-parse',source],text=True).strip()
    path='Solutions/PolynomialNearGeodesicWindows.lean'
    blob=subprocess.check_output(['git','rev-parse',source+':'+path],text=True).strip()
    body=subprocess.check_output(['git','show',source+':'+path],text=True)
    body='\n'.join(l for l in body.splitlines() if not l.startswith(('import ','#print axioms')))
    solution=PRE+'\n'+body+'\nend\ntheorem solution '+BINDERS+''' := by
  classical
  apply HirschPortalDebt.near_geodesic_carrier_mass p q hp available positions hpositions delta e
  intro k hk
  simpa only [HirschPortalDebt.positionLoad, HirschPortalDebt.Contact] using hbudget k hk
'''
    problem={'theorem_name':NAME,'theorem_title':'Near-geodesic occurrence windows bound joint carrier resources',
      'formal_statement':'theorem '+NAME+' '+BINDERS+' := by sorry','preamble':PRE,
      'natural_language_statement':NAT,'source':'Graph shortcut and double-counting proof; https://github.com/jjoshua2/prove2me-work/tree/'+source,
      'tags':['graph-theory','polyhedra','formalization'],'env':PIN}
    files={'solution.lean':solution,'driver.lean':solution+'\n#print axioms solution\n',
      'statement.lean':PRE+'\ntheorem '+NAME+' '+BINDERS+' := by sorry\n',
      'problem.json':json.dumps(problem,indent=2)+'\n',
      'explanation.md':'''A two-edge shortcut through a shared neighbor bounds contact-index separation by q+2. All contacts lie in q+3 consecutive positions. Double-count available-vertex versus selected-position incidences, then sum the explicit pointwise budgets. Positions remain distinct even when their graph labels repeat. The complete proof is included, with no imported theorem dependency. This does not assert a universal portal-selection or polytope diameter bound.\n'''}
    out.mkdir(parents=True,exist_ok=True)
    for name,s in files.items():(out/name).write_text(s)
    (out/'manifest.json').write_text(json.dumps({'source_commit':source,'mathlib_rev':PIN,'source_blobs':{path:blob},'public_dependencies':{},'sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}},indent=2)+'\n')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();prepare(a.source,a.out)
