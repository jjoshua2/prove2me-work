#!/usr/bin/env python3
"""Prepare a reproducible full hidden-product publication; no network writes.

The exact source supplies the projective inverse, segment/edge transport, and
finite positivity-certificate proof. The public row-block theorem is the only
external theorem input; the local audit driver keeps its full type explicit.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks'
DEPENDENCY = 'Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks'
PREAMBLE = ('import Mathlib\nimport Definitions.Def_Hirsch_model\n'
            'open scoped BigOperators RealInnerProductSpace\nopen Set Hirsch')
CERTIFICATES = '''
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) (n - d)'''
NATURAL = r'''Let $P=\{x\in\mathbb R^d:a_i\cdot x\le b_i,\ 1\le i\le n\}$
be nonempty and bounded. Suppose an invertible linear change of coordinates
and a partition of all describing rows identify $P$ with independent factors
$P_j\subseteq\mathbb R^{d_j}$, each described by $n_j$ rows, where
$d_j\le n_j\le d_j+3$. All combinations of factor points must be feasible;
the row identities certify an actual Cartesian product.

Choose $c\in\mathbb R^d$ and define $a'_i=a_i+b_i c$. Suppose there are
nonnegative weights $\mu_i,\nu_i$ satisfying

$$\sum_i\mu_i a_i=-c,\qquad \sum_i\mu_i b_i<1,\qquad
\sum_i\nu_i a'_i=c,\qquad \sum_i\nu_i b_i<1.$$

Then the polyhedron $Q=\{y\in\mathbb R^d:a'_i\cdot y\le b_i\}$ satisfies

$$\operatorname{diam}_{\mathrm{edge}}(Q)\le n-d.$$

There is no bound on total excess, number of factors, or repair-support deficit.
The criterion includes products hidden by a positive projective transformation,
even when the target normals do not split into independent linear blocks.
The chart and factorization are supplied and certified; their existence for
arbitrary polyhedra is not asserted.

**Formalization Note** Dimension and row partitions are explicit equivalences.
Stationary steps permit padding to exactly $n-d$ steps, with natural subtraction.
The certificate checker uses rational data; the theorem permits real coefficients.'''
EXPLANATION = r'''The proof first uses the already-Proved independent-row-block
theorem to route the source polyhedron $P$ in at most $n-d$ ordinary edges.
That theorem derives boundedness of the factors from the nonempty bounded
source and sums their small-excess bounds. The complete row partition and
invertible coordinate map make the sum of factor excesses equal to $n-d$.

The supplied weights certify both denominators. Multiplying the source rows
by $\mu_i\ge0$ gives $-c\cdot x\le\sum_i\mu_i b_i<1$ on $P$.
Similarly the target weights give $c\cdot y\le\sum_i\nu_i b_i<1$ on $Q$.
Thus $1+c\cdot x$ and $1-c\cdot y$ are strictly positive on their respective sets.

Define $f(x)=x/(1+c\cdot x)$ and $g(y)=y/(1-c\cdot y)$.
Their inverse identities are proved by direct algebra. The exact slack identity

$$b_i-a'_i\cdot f(x)=\frac{b_i-a_i\cdot x}{1+c\cdot x}$$

proves $f(P)=Q$ using positivity in both directions. No additional halfspace
is silently discarded. The total functions outside these positive domains
are never used in the geometric argument.

For $z=\alpha x+\beta y$, where $\alpha,\beta\ge0$ and
$\alpha+\beta=1$, write $D(t)=1+c\cdot t$. The proof establishes

$$f(z)=\frac{\alpha D(x)}{D(z)}f(x)+\frac{\beta D(y)}{D(z)}f(y).$$

The new coefficients are nonnegative and sum to one; strict positivity is
preserved for interior segment parameters. Applying the same identity to $g$
establishes exact image equalities for closed and open segments. Injectivity
on the convex positive domain then preserves and reflects extreme subsets.
Singletons give vertex preservation, and extreme closed segments give ordinary
edge preservation. Mapping each point of the source walk preserves its length
without any extra steps.

All inverse, segment, extreme-set, edge, slack, and multiplier proofs are
contained in the submitted file. Its only imported theorem is the already-Proved
independent-small-row-block bound. The audit driver keeps that exact input as
an explicit proposition; the platform verifies the unconditional composition.
Projective graph invariance is classical. This contribution formalizes the
specific positive chart and a finite sufficient routing criterion; it does not
prove a uniform polynomial bound for arbitrary carriers or a chart-discovery theorem.'''


def prepare(source: str, out: Path) -> None:
    source = subprocess.check_output(['git', 'rev-parse', source], text=True).strip()
    blobs = {}

    def blob(path: str) -> str:
        raw = subprocess.check_output(['git', 'show', source + ':' + path])
        blobs[path] = {'sha256': hashlib.sha256(raw).hexdigest(),
                      'git_blob': subprocess.check_output(
                          ['git', 'rev-parse', source + ':' + path], text=True).strip()}
        return raw.decode()

    def body(path: str) -> str:
        return '\n'.join(line for line in blob(path).splitlines()
                         if not line.startswith('import ')) + '\n'

    prefix = PREAMBLE + '\n\n'
    for module in ['PolynomialSegmentChartTransport', 'PolynomialPositivePerspective']:
        prefix += body('Solutions/' + module + '.lean') + '\nend\n'
    rows = body('Solutions/PolynomialProjectiveRowBlockRouting.lean')
    prefix += rows.split('/-- Final sufficient routing criterion.', 1)[0]
    prefix += '\nend HirschProjectiveBlocks\nend\n'
    record = json.loads(blob('research/verification/2026-09-12-projective-products/row-blocks.json'))
    assert record['theorem_name'] == DEPENDENCY and record['status'] == 'Proved'
    assert record['mathlib_rev'] == PIN
    declaration = record['formal_statement'].split(DEPENDENCY.split('.')[-1], 1)[1]
    declaration = declaration.split(' := by sorry', 1)[0].strip()
    row_binders, result = declaration.rsplit(' :', 1)
    binders = row_binders + CERTIFICATES
    premise = 'def IndependentSmallRowBlockBound : Prop :=\n  ∀ ' + row_binders + ',\n' + result + '\n'
    proof = ''' := by
  have hdiam := INPUT dims counts a b T e A hrows hbd hne hcount hsmallcount
  exact HirschProjectiveBlocks.hpoly_diamLE_of_shear_multipliers a b c
    weights inverseWeights hweights hnormal hmargin hinverseWeights
    hinverseNormal hinverseMargin (n-d) hdiam
'''
    driver = (prefix + premise + '\ntheorem checked_projective_blocks_adapter\n'
              '    (hblocks : IndependentSmallRowBlockBound)\n' + binders +
              proof.replace('INPUT', 'hblocks') + '\n#print axioms checked_projective_blocks_adapter\n')
    solution = ('import Theorems.Thm_' + DEPENDENCY.replace('.', '_') + '\n' +
                prefix + '\ntheorem solution\n' + binders + proof.replace('INPUT', DEPENDENCY))
    formal = ('namespace Hirsch\ntheorem ' + NAME.split('.')[-1] + '\n' +
              binders + ' := by sorry\nend Hirsch')
    payload = {'theorem_name': NAME,
               'theorem_title': 'Hirsch routing for products hidden by a positive projective chart',
               'formal_statement': formal, 'preamble': PREAMBLE, 'env': PIN,
               'natural_language_statement': NATURAL,
               'source': ('Exact statement, positive chart proof and certificate criterion: '
                          'https://github.com/jjoshua2/prove2me-work/blob/' + source +
                          '/Solutions/PolynomialProjectiveRowBlockRouting.lean . Classical context: '
                          'Gouveia, Macchia, Thomas, Wiebe, The Slack Realization Space of a Polytope '
                          '(2019), Section 2, equation (3) and Lemma 2.3, '
                          'https://arxiv.org/html/1708.04739v4#S2 . '
                          'The finite multiplier and row-block criterion is derived in the cited '
                          'Lean source, not claimed to be a verbatim theorem of that paper.'),
               'tags': ['hirsch-conjecture', 'polytopes', 'diameter-bound', 'projective-geometry']}
    files = {'driver.lean': driver, 'solution.lean': solution,
             'statement.lean': PREAMBLE + '\n' + formal,
             'problem.json': json.dumps(payload, indent=2, ensure_ascii=False) + '\n',
             'explanation.md': EXPLANATION + '\n'}
    out.mkdir(parents=True, exist_ok=True)
    for name, content in files.items():
        (out / name).write_text(content)
    manifest = {'source_commit': source, 'source_files': blobs, 'mathlib_rev': PIN,
                'public_dependencies': {DEPENDENCY: record['theorem_id']},
                'sha256': {name: hashlib.sha256(content.encode()).hexdigest()
                           for name, content in files.items()}}
    (out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', required=True)
    parser.add_argument('--out', type=Path,
                        default=Path('research/publication_packets/projective_small_blocks'))
    args = parser.parse_args()
    prepare(args.source, args.out)
