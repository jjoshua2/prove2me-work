#!/usr/bin/env python3
"""Build a small publication packet from an immutable, locally checked commit.

The audit driver keeps the two public inputs explicit. The platform solution
supplies their already-Proved declarations, recording real dependency edges.
This script prepares files only; it performs no network writes.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.hpoly_diameter_le_fixed_excess_larman'
PREAMBLE = ('import Mathlib\nimport Definitions.Def_Hirsch_model\n'
            'open scoped RealInnerProductSpace\nopen Set Hirsch')
BINDERS = '''    (E d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + E) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (2 * E * 2 ^ (E - 3))'''
DEPENDENCIES = {
    'Hirsch.larman_bound': '68453b6b-bcef-4672-b877-d04e56527e3f',
    'Hirsch.facet_reduction': '11b3500a-b9f8-4b44-94aa-d71354441ddb',
}
NATURAL = r'''Let $E,d,n$ be nonnegative integers and let $P$ be a bounded
polyhedron in $\mathbb R^d$ described by $n$ linear inequalities. If $n\le d+E$,
then every pair of vertices can be joined by an ordinary edge walk of length at most

$$2E\,2^{\max(E-3,0)}.$$

Empty and lower-dimensional polyhedra, redundant inequalities, and zero row
normals are included. Thus a fixed bound on row excess gives a diameter bound
independent of ambient dimension. This classical coarse bound remains exponential
in excess and does not establish the Polynomial Hirsch conjecture.

**Formalization Note** The exponent uses truncated natural subtraction. The
predicate permits stationary steps, expressing an upper bound on edge distance.'''
EXPLANATION = r'''For a fixed excess cap $E$, induct on the ambient dimension $d$.

If $d\le E$, then $n\le2E$. Apply the already-Proved Larman bound and pad its walk:
$$n2^{\max(d-3,0)}\le2E2^{\max(E-3,0)}.$$
An empty polyhedron has no vertex pair and the diameter assertion is vacuous.

If $d>E$, then $n\le d+E<2d$. The nonzero tight row normals at each vertex span
the ambient space: otherwise a small feasible perturbation in both signs would
contradict extremality. Consequently each endpoint has at least $d$ distinct
nonzero tight rows. The two sets intersect because $n<2d$. Explicitly counting
nonzero rows excludes tautological zero inequalities from this intersection.

Choose a nonzero row tight at both endpoints. The endpoints remain extreme in
its equality section. The already-Proved facet-reduction theorem removes that
row and lowers dimension by one. The resulting $n-1$ row description satisfies
$n-1\le(d-1)+E$, so the induction hypothesis applies with the SAME budget.
Both endpoints already lie in the section: transporting its walk adds no access
step and no multiplicative factor. This is classical shared-facet dimension
descent, with a conservative Larman base, including degenerate H-descriptions.

The submitted source contains the vertex spanning, nonzero-row counting, padding,
and induction proofs. Its only imported theorem dependencies are the already-Proved
Larman and equality-section reduction statements. The local audit driver treats
these as explicit propositions and has only standard logical axioms; the platform
checks the unconditional composition. The separate GitHub clipping assembly
uses the estimate on actual selected carriers, but is not part of this public
theorem's statement. No unresolved Hirsch ancestor is imported.'''


def prepare(source: str, out: Path) -> None:
    source = subprocess.check_output(['git', 'rev-parse', source], text=True).strip()
    blobs = {}

    def body(path: str) -> str:
        raw = subprocess.check_output(['git', 'show', source + ':' + path])
        blobs[path] = {
            'git_blob': subprocess.check_output(
                ['git', 'rev-parse', source + ':' + path], text=True).strip(),
            'sha256': hashlib.sha256(raw).hexdigest(),
        }
        return '\n'.join(line for line in raw.decode().splitlines()
                         if not line.startswith('import ')) + '\n'

    vertex = body('Solutions/PolynomialVertexSpan.lean')
    descent = body('Solutions/PolynomialLowExcessSectionDescent.lean')
    descent = descent.split('/-- Descent preserves n-d', 1)[0] + '\nend HirschLowExcess\nend\n'
    padding = body('Solutions/PolynomialProductWalk.lean')
    padding = ('namespace HirschProduct\nlemma pad_walk' + padding.split('lemma pad_walk', 1)[1]
               .split('\nvariable {ι', 1)[0] + '\nend HirschProduct\n')
    larman = body('Solutions/PolynomialLowDimensionalCarrierRouting.lean')
    larman = ('namespace HirschCircuitLocalization\ndef LarmanHpolyBound' +
              larman.split('def LarmanHpolyBound', 1)[1].split('/-- Larman in', 1)[0]
              + '\nend HirschCircuitLocalization\n')
    fixed = body('Solutions/PolynomialFixedExcessLarman.lean')
    fixed = fixed.split('end HirschLowExcess', 1)[0] + 'end HirschLowExcess\nend\n'
    prefix = PREAMBLE + '\n\n' + vertex + descent + padding + larman + fixed
    driver = prefix + '''
theorem checked_fixed_excess_adapter
    (hlar : HirschCircuitLocalization.LarmanHpolyBound)
    (hfacet : HirschLowExcess.FacetWalkReduction)
''' + BINDERS + ''' := by
  exact HirschLowExcess.hpoly_diamLE_fixed_excess_larman hlar hfacet E d n a b hrows hbd

#print axioms checked_fixed_excess_adapter
'''
    solution = '\n'.join('import Theorems.Thm_' + name.replace('.', '_')
                         for name in DEPENDENCIES) + '\n' + prefix + '''
theorem solution
''' + BINDERS + ''' := by
  exact HirschLowExcess.hpoly_diamLE_fixed_excess_larman
    Hirsch.larman_bound Hirsch.facet_reduction E d n a b hrows hbd
'''
    formal = ('namespace Hirsch\ntheorem hpoly_diameter_le_fixed_excess_larman\n' +
              BINDERS + ' := by sorry\nend Hirsch')
    payload = {
        'theorem_name': NAME,
        'theorem_title': 'A dimension-independent Larman bound at fixed row excess',
        'formal_statement': formal, 'natural_language_statement': NATURAL,
        'preamble': PREAMBLE, 'env': PIN,
        'source': ('Exact H-polyhedron statement and proof: https://github.com/jjoshua2/'
                   'prove2me-work/blob/' + source + '/Solutions/PolynomialFixedExcessLarman.lean'
                   '#L21 ; classical shared-facet descent: Santos, A counterexample to the Hirsch '
                   'conjecture (2012), Lemma 1.1 and its proof, printed pp. 385 and 391; '
                   'https://annals.math.princeton.edu/wp-content/uploads/annals-v176-n1-p07-p.pdf . '
                   'The explicit coarse constant here is derived from the platform Larman '
                   'bound, not claimed to be a verbatim theorem of Santos.'),
        'tags': ['hirsch-conjecture', 'polytopes', 'diameter-bound'],
    }
    out.mkdir(parents=True, exist_ok=True)
    files = {'driver.lean': driver, 'solution.lean': solution,
             'statement.lean': PREAMBLE + '\n' + formal,
             'problem.json': json.dumps(payload, indent=2, ensure_ascii=False) + '\n',
             'explanation.md': EXPLANATION + '\n'}
    for name, content in files.items():
        (out / name).write_text(content)
    manifest = {'source_commit': source, 'source_files': blobs, 'mathlib_rev': PIN,
                'public_dependencies': DEPENDENCIES,
                'sha256': {name: hashlib.sha256(content.encode()).hexdigest()
                           for name, content in files.items()}}
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True)
    parser.add_argument('--out', type=Path,
                        default=Path('research/publication_packets/fixed_excess_larman'))
    args = parser.parse_args()
    prepare(args.source, args.out)
