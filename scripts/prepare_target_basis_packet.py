#!/usr/bin/env python3
"""Freeze a self-contained tight-basis theorem from the checked continuation."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.vertex_has_injective_target_tight_basis'
PREAMBLE = 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen Set Hirsch\nopen scoped BigOperators RealInnerProductSpace'
BINDERS = '''{d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective (fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k)'''
NATURAL = '''At every extreme point v of an n-row real H-polyhedron in R^d, one can
select exactly d distinct original rows, all tight at v, whose row-evaluation
map is injective. No simplicity, boundedness, strict interior point, or supplied
basis is required. In particular this applies to nonsimple vertices with more
than d tight rows.

This is classical active-row basis extraction. Its role in the Polynomial
Hirsch workspace is to remove the previously explicit basis input from the
full-availability compact-star construction. The present statement itself
asserts neither a diameter bound nor the existence of feedback models for
arbitrary carriers.'''
EXPLANATION = '''First prove directly by a finite perturbation that any direction
annihilating all tight rows must vanish. For inactive rows choose positive
step sizes controlled by their slacks and take a finite common lower bound.
Both signed perturbations are feasible, and extremality forces the direction
to be zero. Consequently the orthogonal complement of the tight-normal span
is zero, so the tight normals span all of R^d. Extract an independent spanning
subfamily, identify its cardinality with d through its basis, and reindex by
Fin d. The original row index map is injective. Expanding any vector in the
selected basis proves injectivity of its row-evaluation map.

The complete finite-perturbation and basis-selection proofs are included.
The proof imports only Mathlib and the Hirsch model, with no public theorem
dependencies. The classical basis theorem is reused, not claimed as new
mathematics. The later clipping and mixed-routing applications have separate
local verification and are not conclusions of this public theorem.'''

def prepare(source, out):
    source = subprocess.check_output(['git', 'rev-parse', source], text=True).strip()
    blobs = {}
    def body(path):
        blobs[path] = subprocess.check_output(['git', 'rev-parse', source + ':' + path], text=True).strip()
        s = subprocess.check_output(['git', 'show', source + ':' + path], text=True)
        return '\n'.join(line for line in s.splitlines() if not line.startswith(('import ', '#print axioms'))) + '\n'
    prefix = PREAMBLE + '\n' + body('Solutions/PolynomialVertexSpan.lean')
    core = body('Solutions/PolynomialAutomaticTargetBasis.lean')
    core = core[:core.index('/-- Every bounded strictly feasible')]
    core = core.replace('open Set Hirsch HirschRegionRoute HirschRadial HirschPolynomialAccess',
                        'open Set Hirsch HirschPolynomialAccess')
    old = 'HirschCircuit.rowMap (fun k => a (e k))'
    new = '(fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫)'
    assert core.count(old) == 1
    core = core.replace(old, new)
    prefix += core + '\nend HirschTargetDeletion\nend\n'
    solution = prefix + '\ntheorem solution ' + BINDERS + ''' := by
  exact HirschTargetDeletion.exists_target_tight_basis a b v hv
'''
    problem = {'theorem_name': NAME, 'theorem_title': 'Every polyhedron vertex supplies an injective basis of original tight rows',
               'formal_statement': 'theorem ' + NAME + ' ' + BINDERS + ' := by sorry',
               'natural_language_statement': NATURAL, 'preamble': PREAMBLE,
               'source': 'Classical active-row basis theorem; explicit checked application at https://github.com/jjoshua2/prove2me-work/tree/' + source,
               'tags': ['polyhedra', 'linear-algebra', 'formalization'], 'env': PIN}
    files = {'solution.lean': solution, 'driver.lean': solution + '\n#print axioms solution\n',
             'statement.lean': PREAMBLE + '\ntheorem ' + NAME + ' ' + BINDERS + ' := by sorry\n',
             'problem.json': json.dumps(problem, indent=2) + '\n', 'explanation.md': EXPLANATION + '\n'}
    out.mkdir(parents=True, exist_ok=True)
    for name, s in files.items():
        (out / name).write_text(s)
    (out / 'manifest.json').write_text(json.dumps({'source_commit': source, 'mathlib_rev': PIN,
        'source_blobs': blobs, 'public_dependencies': {},
        'transformations': ['Omit later clipping wrapper and unused namespace opens',
                            'Unfold rowMap into its coordinate-evaluation lambda'],
        'sha256': {name: hashlib.sha256(s.encode()).hexdigest() for name, s in files.items()}}, indent=2) + '\n')
    print(json.dumps({'source': source, 'proof_lines': len(solution.splitlines())}))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    prepare(args.source, args.out)
