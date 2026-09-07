#!/usr/bin/env python3
"""Compile exact circuit-construction proof bytes. Never publishes or reads secrets."""
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

report = {'mathlib_rev': PIN, 'submitted': False, 'files': {}}
bridge = OUT / 'slack_bridge.lean'
bridge_names = ['HirschSlack.walk_iff','HirschSlack.extreme_iff','HirschSlack.elementary_iff']
bridge.write_text(inline('Solutions.CircuitSlackBridge')+'\n'+'\n'.join('#print axioms '+x for x in bridge_names)+'\n')
report['files']['slack_bridge.lean'] = audit(bridge, bridge_names)
source = (ROOT/'Solutions/CircuitProgressNumerics.lean').read_text()
for local, public, folder, title in [
    ('greedy_norm_step','Hirsch.circuit_greedy_norm_step','norm',
     'Greedy conformal augmentation contracts weighted mass and preserves trapped coordinates'),
    ('elimination_trapped_coordinate','Hirsch.circuit_elimination_trapped_coordinate','elimination',
     'Elimination augmentation preserves trapped coordinates and cannot zero a positive trapped coordinate'),
]:
    statement = source.split('theorem '+local,1)[1].split(':= by',1)[0].strip()
    statement = statement.replace('ConformalPart g (fun i => v i - x i)',
        '(∀ i, min 0 (v i - x i) ≤ g i ∧ g i ≤ max 0 (v i - x i))')
    path = OUT / folder
    path.mkdir(exist_ok=True)
    args = {
      'greedy_norm_step': 'N x v g weight M alpha hM ha hx hv hweight hvN hconf hfeas hmass hgain',
      'elimination_trapped_coordinate': 'M alpha lambda eta x ref v g hM ha0 haM hl he hprotect hsmall hx0 hr0 hv0 hxM hrM hconf',
    }[local]
    proof = inline('Solutions.CircuitProgressNumerics')
    proof += '\ntheorem solution '+statement+' := by\n  exact HirschCircuitProgress.'+local+' '+args+'\n\n#print axioms solution\n'
    (path/'solution.lean').write_text(proof)
    report['files'][folder+'/solution.lean'] = audit(path/'solution.lean', ['solution'])
    problem = {'env': PIN, 'problems': [{
        'theorem_name':public, 'theorem_title':title,
        'formal_statement':'theorem '+public+' '+statement+' := by sorry',
        'preamble':'import Mathlib',
        'natural_language_statement':title+'. This is a numerical lemma used in circuit routing; it does not assert that a conformal direction is an edge, nor a polynomial graph-diameter bound.',
        'source':'Formalization of quantitative ingredients of Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Claim 3.5 and elimination-step analysis. No novelty claim. Source in jjoshua2/prove2me-work, Solutions/CircuitProgressNumerics.lean.',
        'tags':['convex-geometry','polytopes']
    }]}
    (path/'problem.json').write_text(json.dumps(problem,ensure_ascii=False,indent=2)+'\n')
    (path/'signature.txt').write_text(statement+'\n')
(OUT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('CIRCUIT_CONSTRUCTION_VERIFIED', json.dumps(report), flush=True)
