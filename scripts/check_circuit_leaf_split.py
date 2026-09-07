#!/usr/bin/env python3
"""Prepare exact sketch bytes and verify its implication without imported axioms."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'circuit_leaf_packet'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
LEAF = '33fc334e-e05b-4090-ac49-f83fd94d9305'
CHILDREN = [
    'Hirsch.cubic_circuit_walk_bound',
    'Hirsch.polynomial_edge_refinement_of_circuit_walks',
]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
PREAMBLE = ('import Definitions.Def_Hirsch_circuit_model\n'
            'set_option autoImplicit false\nopen scoped RealInnerProductSpace\nopen Hirsch')


def theorem_type(text: str, name: str) -> str:
    tail = text.split('theorem ' + name, 1)[1]
    result = tail.split(':= by', 1)[0].strip()
    if not result.startswith(':'):
        raise ValueError('Expected a closed theorem type: ' + name)
    return result[1:].strip()


def audit(path: Path, declaration: str, allow_stubs: bool = False) -> dict:
    start = time.monotonic()
    run = subprocess.run([str(Path.home()/'.elan/bin/lake'), 'env', 'lean', str(path)],
                         cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         timeout=295)
    elapsed = time.monotonic() - start
    path.with_suffix('.audit.log').write_text(run.stdout, encoding='utf-8')
    print(run.stdout)
    if run.returncode:
        raise RuntimeError('Lean failed: ' + str(path))
    match = re.search("'" + re.escape(declaration) + r"' depends on axioms:\s*\[([^]]*)\]", run.stdout)
    if not match:
        raise RuntimeError('Missing axiom report: ' + declaration)
    axioms = {part.strip() for part in match.group(1).split(',') if part.strip()}
    allowed = ALLOWED | ({'sorryAx'} if allow_stubs else set())
    if not axioms <= allowed:
        raise RuntimeError('Unexpected axioms: ' + repr(axioms - allowed))
    data = path.read_bytes()
    return {'compiled': True, 'seconds': round(elapsed, 4), 'bytes': len(data),
            'lines': len(data.splitlines()), 'sha256': hashlib.sha256(data).hexdigest(),
            'axioms': sorted(axioms), 'open_child_stubs_allowed': allow_stubs}


def main() -> None:
    OUT.mkdir(exist_ok=True)
    definition = (ROOT/'Definitions/Def_Hirsch_circuit_model.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b', definition):
        raise RuntimeError('Admission in definition module')
    parent = (ROOT/'Solutions/Sol_Hirsch_leaf_circuit_split.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b', parent):
        raise RuntimeError('Admission in parent proof')
    if 'import Theorems.Thm_Hirsch_polynomial_access_to_given_supporting_face' in parent:
        raise RuntimeError('Own-target import')
    original = (ROOT/'Theorems/Thm_Hirsch_polynomial_access_to_given_supporting_face.lean').read_text()
    target = theorem_type(original, 'polynomial_access_to_given_supporting_face')
    actual = theorem_type(parent, 'solution')
    if re.sub(r'\s+', '', target) != re.sub(r'\s+', '', actual):
        raise RuntimeError('Parent signature is not the exact existing leaf')
    (OUT/'solution.lean').write_text(parent)
    child_texts = [(ROOT/('Theorems/Thm_' + name.replace('.', '_') + '.lean')).read_text()
                   for name in CHILDREN]
    child_types = [theorem_type(text, name) for text, name in zip(child_texts, CHILDREN)]
    proof = parent.split('theorem solution', 1)[1].split(':= by', 1)[1].split('#print axioms', 1)[0]
    for name, arg in zip(CHILDREN, ['routing', 'rounding']):
        proof = proof.replace(name, arg)
    conditional = (PREAMBLE + '\nset_option maxHeartbeats 1000000\n\n'
                   'theorem checked_reduction\n'
                   f'    (routing : {child_types[0]})\n'
                   f'    (rounding : {child_types[1]}) :\n'
                   + target + ' := by' + proof + '\n#print axioms checked_reduction\n')
    (OUT/'conditional_reduction.lean').write_text(conditional)
    geom = (ROOT/'Solutions/CircuitIrredundantModel.lean').read_text()
    if re.search(r'\b(sorry|admit|native_decide)\b', geom):
        raise RuntimeError('Admission in normalization proof')
    (OUT/'normalization.lean').write_text(geom)
    reports = {
        'normalization.lean': audit(OUT/'normalization.lean', 'HirschCircuit.exists_irredundant_strict_model'),
        'conditional_reduction.lean': audit(OUT/'conditional_reduction.lean', 'checked_reduction'),
        'solution.lean': audit(OUT/'solution.lean', 'solution', allow_stubs=True),
    }
    payload_def = {
        'env': PIN, 'private': False, 'definition_name': 'Hirsch_circuit_model',
        'definition_title': 'Maximal row-circuit walks and irredundant H-polytope presentations',
        'definition': definition,
        'natural_language_statement': ('Support-minimal nonzero row directions, maximal feasible circuit '
            'augmentations with possibly nonvertex intermediate points, padded circuit walks, '
            'irredundancy witnesses, and strict feasibility. These definitions do not identify circuit steps with edges.'),
        'source': 'Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Section 1.1; row-support formulation via slack coordinates.',
        'tags': ['convex-geometry', 'polytopes'],
    }
    descriptions = [
        ('Cubic circuit routing after irredundant normalization',
         'A uniform constant C exists so that any separated feasible extreme endpoints of a bounded '
         'n-row H-polytope admit a retained subfamily of m <= n original rows defining exactly the same '
         'polytope, with no redundant rows and a strict feasible point, and a padded maximal circuit '
         'walk between those endpoints of length C(m+d)^3. Source-backed FORMALIZATION TARGET: finite '
         'minimal row selection and the strict midpoint, followed by an injective slack identification '
         'and Natura Theorem 3.1/Corollary 3.2. The paper states O(r^2 log r); this cubic envelope is weaker. '
         'The d=m=0 case uses a constant walk. This is not a graph-diameter theorem.',
         'Bento Natura, arXiv:2602.06958v2 (10 February 2026), Theorem 3.1 and Corollary 3.2, plus elementary irredundant-row and slack-coordinate reductions detailed in research/CircuitLeafSplit.md.'),
        ('Polynomial edge refinement of irredundant circuit walks — open research',
         'For irredundant strictly feasible bounded H-polytope presentations, is there a uniform '
         'polynomial C(n+d)^k such that any length-L padded maximal circuit walk between vertices '
         'can be replaced by a graph-edge walk between the same vertices of length C(n+d)^k L? '
         'The replacement need not visit the original circuit intermediates, which can be nonvertices. '
         'It need not be monotone or preserve every already visited facet. This is an OPEN CONJECTURAL '
         'bridge, not a theorem of Natura and not a routine rounding lemma. Together with the circuit '
         'bound it retains the essential polynomial-Hirsch difficulty.',
         'Proposed research bridge for the Polynomial Hirsch mission; sufficiency proved in Solutions/Sol_Hirsch_leaf_circuit_split.lean. Motivation, not proof of this bridge: arXiv:2602.06958v2. No literature-priority claim.'),
    ]
    problems = []
    for name, typ, (title, description, source) in zip(CHILDREN, child_types, descriptions):
        problems.append({'theorem_name': name, 'theorem_title': title,
                         'formal_statement': 'theorem ' + name + ' :\n' + typ + ' := by sorry',
                         'preamble': PREAMBLE, 'natural_language_statement': description,
                         'source': source, 'tags': ['convex-geometry', 'polytopes']})
    (OUT/'definition.json').write_text(json.dumps(payload_def, indent=2, ensure_ascii=False)+'\n')
    (OUT/'children.json').write_text(json.dumps({'env':PIN, 'private':False, 'problems':problems}, indent=2, ensure_ascii=False)+'\n')
    (OUT/'verification.json').write_text(json.dumps({'env':PIN, 'leaf_id':LEAF,
        'exact_parent_signature_match':True, 'proofs':reports,
        'conclusion':'Checked conditional sketch, NOT a proof of either child or the leaf.'}, indent=2)+'\n')
    explanation = '''This is a conditional reduction, not a completed polynomial bound.

The first child removes redundant rows without changing the polytope and supplies a maximal circuit walk of length C_c(m+d)^3, with m at most the original row count n. Its quantitative input is the circuit-diameter theorem of Natura (arXiv:2602.06958v2, Theorem 3.1/Corollary 3.2), after a slack-coordinate identification. The second child is an explicitly open circuit-to-edge replacement conjecture for irredundant strictly feasible presentations. It is not established by that paper.

Assuming the second child with constants C_e,k_e, the same endpoints can be joined by at most C_e(m+d)^{k_e} C_c(m+d)^3 = C_e C_c(m+d)^{k_e+3} actual edge steps. Since m <= n, this is at most C_e C_c(n+d)^{k_e+3}. Pad with stationary steps to this last budget. The target vertex v itself lies on the originally prescribed supporting row, so choose z=v. No change from a prescribed face to an existentially chosen face is made.

The two children are assumptions of this sketch. In particular, an edge walk cannot generally be obtained by keeping all circuit intermediates or by replacing each circuit augmentation with a single edge. The remaining essential conjectural difficulty is the polynomial-cost edge replacement.
'''
    (OUT/'explanation.md').write_text(explanation)
    print('CIRCUIT_LEAF_SKETCH_CHECKED', json.dumps(reports))


if __name__ == '__main__':
    main()
