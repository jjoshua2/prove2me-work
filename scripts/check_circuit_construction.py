#!/usr/bin/env python3
"""Compile exact proof bytes; never publish or read credentials."""
from __future__ import annotations
import hashlib
import json
import pathlib
import re
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / 'circuit_construction_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
LAKE = str(pathlib.Path.home() / '.elan/bin/lake')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
OUT.mkdir(exist_ok=True)


def inline(module: str) -> str:
    seen: set[str] = set()
    parts: list[str] = []
    def visit(name: str) -> None:
        if name in seen or name == 'Mathlib': return
        if name.startswith('Theorems.'): raise RuntimeError('Theorem stub import: '+name)
        if not name.startswith(('Definitions.', 'Solutions.')):
            raise RuntimeError('Unexpected import: '+name)
        seen.add(name)
        text = (ROOT / (name.replace('.', '/')+'.lean')).read_text()
        for line in text.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split(): visit(dep)
        body = '\n'.join(line for line in text.splitlines()
                         if not line.startswith(('import ', '#print axioms ')))
        if re.search(r'\b(sorry|admit|native_decide)\b', body):
            raise RuntimeError('Unexpected admission token: '+name)
        if re.search(r'^noncomputable section\s*$', body, re.M): body += '\nend\n'
        parts.append('-- BEGIN '+name+'\n'+body+'\n')
    visit(module)
    return 'import Mathlib\n'+'\n'.join(parts)


def audit(path: pathlib.Path, names: list[str]) -> dict:
    start = time.monotonic()
    proc = subprocess.run([LAKE, 'env', 'lean', str(path.relative_to(ROOT))],
                          cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    seconds = time.monotonic()-start
    path.with_suffix('.audit.log').write_text(proc.stdout)
    print(proc.stdout, flush=True)
    if proc.returncode: raise RuntimeError('Lean rejected '+str(path))
    axioms = {}
    for name in names:
        match = re.search(r"'"+re.escape(name)+r"' depends on axioms:\s*\[([^]]*)\]", proc.stdout)
        if not match: raise RuntimeError('Missing axiom report: '+name)
        values = {s.strip() for s in match[1].split(',') if s.strip()}
        if not values <= ALLOWED: raise RuntimeError('Unexpected axioms: '+repr(values-ALLOWED))
        axioms[name] = sorted(values)
    return {'compiled': True, 'seconds': seconds, 'lines': len(path.read_text().splitlines()),
            'bytes': path.stat().st_size, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'axioms': axioms}


def elementary(g: str) -> str:
    return '('+g+' ∈ K ∧ '+g+' ≠ 0 ∧ ∀ h ∈ K, h ≠ 0 → '+\
        '{i | h i ≠ 0} ⊆ {i | '+g+' i ≠ 0} → {i | '+g+' i ≠ 0} ⊆ {i | h i ≠ 0})'


def expand(statement: str) -> str:
    std = '{s : Fin n → ℝ | s - b ∈ K ∧ ∀ i, 0 ≤ s i}'
    step = '(x ∈ '+std+' ∧ y ∈ '+std+' ∧ '+elementary('(y - x)')+\
        ' ∧ ∀ t : ℝ, 1 < t → x + t • (y - x) ∉ '+std+')'
    statement = statement.replace('StandardStep K b x y', step)
    statement = statement.replace('standardSet K b', std)
    statement = statement.replace('Elementary K g', elementary('g'))
    statement = statement.replace('ConformalPart g v', '(∀ i, min 0 (v i) ≤ g i ∧ g i ≤ max 0 (v i))')
    statement = statement.replace('ConformalPart g (fun i => v i - x i)',
        '(∀ i, min 0 (v i - x i) ≤ g i ∧ g i ≤ max 0 (v i - x i))')
    return statement


report = {'mathlib_rev': PIN, 'submitted': False, 'files': {}}
bridge = OUT / 'slack_bridge.lean'
bridge_names = ['HirschSlack.walk_iff','HirschSlack.extreme_iff','HirschSlack.elementary_iff']
bridge.write_text(inline('Solutions.CircuitSlackBridge')+'\n'+'\n'.join('#print axioms '+x for x in bridge_names)+'\n')
report['files']['slack_bridge.lean'] = audit(bridge, bridge_names)
configs = [
 ('CircuitConformal','HirschConformal','exists_conformal_decomposition','{n : ℕ}',
  'K v hvK','decomposition','Hirsch.conformal_elementary_decomposition',
  'Every vector of a real subspace is a conformal sum of at most n elementary vectors'),
 ('CircuitNormReduction','HirschCircuitNorm','exists_norm_reducing_circuit_step','',
  'n K b x v N weight M hM hn hx hv hw hvN hmass','norm_step','Hirsch.exists_norm_reducing_circuit_step',
  'Existence of a maximal weighted-norm-reducing circuit augmentation'),
 ('CircuitElimination','HirschCircuitElimination','exists_eliminating_circuit_step','',
  'n K b x ref v T N M lambda eta hM hn hx hr hv hl he hprotect hsmall hxt hrt htangent hN q hxq hq',
  'elimination_step','Hirsch.exists_eliminating_circuit_step',
  'Existence of a maximal circuit augmentation eliminating a coordinate outside the trapped set'),
 ('CircuitProgressNumerics','HirschCircuitProgress','greedy_norm_step','',
  'N x v g weight M alpha hM ha hx hv hweight hvN hconf hfeas hmass hgain',
  'norm','Hirsch.circuit_greedy_norm_step','Weighted gain contracts mass and preserves trapped coordinates'),
 ('CircuitProgressNumerics','HirschCircuitProgress','elimination_trapped_coordinate','',
  'M alpha lambda eta x ref v g hM ha0 haM hl he hprotect hsmall hx0 hr0 hv0 hxM hrM hconf',
  'elimination','Hirsch.circuit_elimination_trapped_coordinate','Elimination steps protect trapped coordinates'),
 ('CircuitParameters','HirschCircuitParameters','elimination_parameters','',
  'M rho hM hr0 hr','parameters','Hirsch.circuit_elimination_parameters',
  'Rational ghost-point parameters satisfy the quantitative protection conditions'),
]
for module, namespace, local, prefix, args, folder, public, title in configs:
    source = (ROOT/('Solutions/'+module+'.lean')).read_text()
    statement = prefix+' '+source.split('theorem '+local,1)[1].split(':= by',1)[0].strip()
    statement = expand(statement.strip())
    path = OUT / folder
    path.mkdir(exist_ok=True)
    proof = inline('Solutions.'+module)
    proof += '\ntheorem solution '+statement+' := by\n  exact '+namespace+'.'+local+' '+args+'\n\n#print axioms solution\n'
    (path/'solution.lean').write_text(proof)
    report['files'][folder+'/solution.lean'] = audit(path/'solution.lean', ['solution'])
    problem = {'env': PIN, 'problems': [{
        'theorem_name':public, 'theorem_title':title,
        'formal_statement':'theorem '+public+' '+statement+' := by sorry',
        'preamble':'import Mathlib',
        'natural_language_statement':title+'. All supports are coordinate supports. The entire statement is explicit in Mathlib primitives. These are proved construction ingredients for circuit routing, not polynomial vertex-edge diameter bounds; an intermediate circuit endpoint need not be a vertex.',
        'source':'Formalization of ingredients of Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Lemma 2.2, Claim 3.5 and elimination-step analysis, using the looser ambient coordinate count. No novelty claim. Source: jjoshua2/prove2me-work, Solutions/'+module+'.lean.',
        'tags':['convex-geometry','polytopes']
    }]}
    (path/'problem.json').write_text(json.dumps(problem,ensure_ascii=False,indent=2)+'\n')
    (path/'signature.txt').write_text(statement+'\n')
    (OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('CIRCUIT_CONSTRUCTION_VERIFIED', json.dumps(report), flush=True)
