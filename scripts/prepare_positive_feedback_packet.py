#!/usr/bin/env python3
"""Freeze the complete positive-feedback proof from immutable Git blobs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

NAME = 'Hirsch.positive_feedback_box_diameter_le_dimension'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
PREAMBLE = 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen Set Hirsch\nopen scoped BigOperators'
BINDERS = '''{d : ℕ} (C : Fin d → Fin d → ℝ) (hC : ∀ i j, 0 ≤ C i j)
    (b w : Fin d → ℝ) (hb : ∀ i, 0 < b i) (hw : ∀ i, 0 < w i)
    (hcw : ∀ i, (∑ j, C i j * w j) < w i) :
    DiamLE {x : Fin d → ℝ | (∀ i, 0 ≤ x i) ∧
      ∀ i, x i ≤ b i + ∑ j, C i j * x j} d'''
NATURAL = '''Let C be an entrywise nonnegative real d by d matrix and b a strictly
positive vector. Suppose a strictly positive vector w satisfies Cw < w in
every coordinate. Then the ordinary-edge graph of the polytope
{x : 0 <= x <= b + Cx} has diameter at most d.

The proof constructs and classifies its vertices by lower/upper binary
signatures and proves that changing one signature coordinate gives an
ordinary edge. It imposes no dimension cap or acyclicity condition on C.
The weighted maximum principle is classical; this is its explicit
ordinary-edge formalization for the Hirsch workspace. This sufficient class
does not imply that arbitrary Hirsch carriers have this form.'''
EXPLANATION = '''A weighted maximum principle using w proves z <= Cz implies z <= 0.
It gives injectivity, and hence finite-dimensional invertibility, of every
masked complementary system I-D_s C. Each binary signature therefore has a
unique feasible solution. Strict positivity of b excludes simultaneous lower
and upper equality for one coordinate. A perturbation argument classifies
every extreme point as one such solution. Shared equalities for signatures
differing in one coordinate cut out exactly their segment, an extreme subset;
thus they are adjacent in the ordinary-edge graph. Flip each differing
coordinate once and pad stationary steps to length d.

All these arguments are included in the submitted source. It imports the
Hirsch model but no diameter theorem or unproved routing assumption. The
complete standalone solution was compiled and transitively axiom-audited.
The separate rational fixture checks and paper-only monotone-cut and Schur
claims are not assumptions or conclusions of this theorem.'''

def prepare(source, out):
    source = subprocess.check_output(['git', 'rev-parse', source], text=True).strip()
    prefix = PREAMBLE + '\n'
    blobs = {}
    for mod in ['PolynomialPairedBasisRouting', 'PolynomialPositiveFeedbackBoxes']:
        path = 'Solutions/' + mod + '.lean'
        blobs[path] = subprocess.check_output(['git', 'rev-parse', source + ':' + path], text=True).strip()
        body = subprocess.check_output(['git', 'show', source + ':' + path], text=True)
        prefix += '\n'.join(line.replace('open Set Hirsch HirschRegionRoute', 'open Set Hirsch')
                            for line in body.splitlines()
                            if not line.startswith(('import ', '#print axioms'))) + '\nend\n'
    solution = prefix + '\ntheorem solution ' + BINDERS + ''' := by
  exact HirschPositiveBoxes.matrix_positive_feedback_diamLE C hC b w hb hw hcw
'''
    files = {'solution.lean': solution, 'driver.lean': solution + '\n#print axioms solution\n',
             'statement.lean': PREAMBLE + '\ntheorem ' + NAME + ' ' + BINDERS + ' := by sorry\n',
             'explanation.md': EXPLANATION + '\n'}
    problem = {'theorem_name': NAME, 'theorem_title': 'Contractive nonnegative feedback boxes have ordinary-edge diameter at most their dimension',
               'formal_statement': 'theorem ' + NAME + ' ' + BINDERS + ' := by sorry',
               'natural_language_statement': NATURAL, 'preamble': PREAMBLE,
               'source': 'Classical complementary-basis and weighted maximum-principle argument, explicitly formalized at https://github.com/jjoshua2/prove2me-work/tree/' + source,
               'tags': ['polyhedra', 'graph-diameter', 'formalization'], 'env': PIN}
    files['problem.json'] = json.dumps(problem, indent=2) + '\n'
    out.mkdir(parents=True, exist_ok=True)
    for name, body in files.items():
        (out / name).write_text(body)
    manifest = {'source_commit': source, 'mathlib_rev': PIN, 'source_blobs': blobs,
                'public_dependencies': {},
                'sha256': {name: hashlib.sha256(body.encode()).hexdigest() for name, body in files.items()}}
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps({'source': source, 'proof_lines': len(solution.splitlines())}))

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    prepare(args.source, args.out)
