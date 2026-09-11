#!/usr/bin/env python3
"""Audit a reduction without axioms, then compose already-Proved platform inputs.

The local driver has explicit logical premises, never theorem-stub imports.
The public solution imports only the two live Proved dependencies. Prove2Me
checks their tracked composition against the unconditional target statement.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import re
import types
from pathlib import Path
from publish_affine_diameter_transport import read_blob, CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB

SOURCE = '2774702c54078cb8efae7bed185ed1b4b93bce5b'
DRIVER_PATH = 'Solutions/PolynomialLowExcessSectionDescent.lean'
DRIVER_BLOB = '794126103cc9d9f60a95eb262d96d282f3e9ad4f'
VERTEX_PATH = 'Solutions/PolynomialVertexSpan.lean'
VERTEX_BLOB = '673e5a68f154b66556d01dd81977107329a3415e'
PACKET = Path('/tmp/low-excess-public')
OUT = Path('low_excess_publication_receipts')
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME = 'Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three'
TITLE = 'Hirsch bound for H-polyhedra with at most three excess rows'
PREAMBLE = 'import Mathlib\nimport Definitions.Def_Hirsch_model\nopen scoped RealInnerProductSpace\nopen Set Hirsch'
BINDERS = '''    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + 3) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d)'''
FORMAL = 'namespace Hirsch\ntheorem hpoly_diameter_le_excess_of_rows_le_dim_add_three\n' + BINDERS + ' := by sorry\nend Hirsch'
NATURAL = '''Let P be a bounded H-polyhedron in ambient R^d described by n real linear inequalities. If n is at most d+3, then its padded vertex-edge graph diameter is at most n-d (natural subtraction). The description may have redundant inequalities or zero normals, and P may be empty or lower dimensional. No strict feasibility or irredundancy is assumed. In particular, at most two excess describing rows gives diameter at most two. This is the classical small-excess consequence of low-dimensional Hirsch, not a uniform polynomial bound for arbitrary excess.'''
EXPLANATION = '''## Statement

For a bounded n-row H-polyhedron P in ambient dimension d,

$$n\le d+3\quad\Longrightarrow\quad\operatorname{DiamLE}(P,n-d).$$

Empty sets, redundant inequalities, and zero normals are included. The proof is dimension descent with constant row excess, using the established low-dimensional Hirsch theorem and equality-section reduction.

## A nonzero common tight row

The nonzero tight row normals at a vertex span the ambient direction space: a direction orthogonal to all active rows would permit a sufficiently small feasible perturbation in both signs, contradicting extremality. Evaluation on the nonzero tight rows is therefore injective, so there are at least d distinct such rows at each vertex. If n<2d, the two sets of nonzero tight rows for any vertex pair must intersect. Counting nonzero rows, rather than arbitrary tight rows, excludes tautologies from the intersection argument.

## Induction on dimension

When d<=3, the established low-dimensional Hirsch bound gives n-d. An empty feasible set has no extreme endpoints and its diameter assertion is vacuous.

For d>3, the hypothesis n<=d+3 implies n<2d. Choose a nonzero row tight at both endpoints. Both endpoints remain extreme in its equality section. The established facet-reduction theorem charts this equality section in ambient dimension d-1 and deletes the selected inequality, leaving n-1 describing rows. Its induction premise is valid because

$$(n-1)\le(d-1)+3,\qquad (n-1)-(d-1)=n-d.$$

The reduced polyhedron is bounded; if it is empty, its diameter assertion is again vacuous. Apply the induction hypothesis and transport its edge/stay walk to the parent polyhedron. Both original endpoints already lie in the selected section, so there is no access segment, no added step, and no multiplicative cost. The transported walk has the same n-d budget.

The public proof imports only the already-Proved dimension-three and facet-reduction theorems. All other geometry and the induction are contained in the submitted source. This argument stops at a universally small base dimension only when the row excess is at most three; it does not establish Polynomial Hirsch for arbitrary excess.'''
DEPENDENCIES = {
    'Hirsch.dimension_three_bound': {
        'id': 'cf588038-4ee8-4c90-b034-348c28d0da21',
        'formal': '''namespace Hirsch

theorem dimension_three_bound (d n : ℕ) (hd : d ≤ 3)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n - d) := by sorry

end Hirsch''',
    },
    'Hirsch.facet_reduction': {
        'id': '11b3500a-b9f8-4b44-94aa-d71354441ddb',
        'formal': '''namespace Hirsch

theorem facet_reduction (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)) (hai : a i ≠ 0)
    (hbd : Bornology.IsBounded (Hpoly a b)) (B : ℕ)
    (IH : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i})
    (hv : v ∈ Set.extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch''',
    },
}


def body(path: str, blob: str) -> str:
    text = read_blob(SOURCE, path, blob).decode('utf-8')
    return '\n'.join(line for line in text.splitlines() if not line.strip().startswith('import ')) + '\n'


def expected_packets() -> tuple[bytes, bytes]:
    prefix = PREAMBLE + '\n\n' + body(VERTEX_PATH, VERTEX_BLOB) + '\n' + body(DRIVER_PATH, DRIVER_BLOB)
    adapter = '''
open scoped RealInnerProductSpace
open Set Hirsch

theorem checked_low_excess_adapter
    (hbase : HirschLowExcess.LowDimensionalHirsch)
    (hfacet : HirschLowExcess.FacetWalkReduction)
''' + BINDERS + ''' := by
  exact HirschLowExcess.hpoly_diameter_le_excess_from_proved_inputs
    hbase hfacet d n a b hrows hbd

#print axioms checked_low_excess_adapter
'''
    imports = '\n'.join('import Theorems.Thm_' + name.replace('.', '_') for name in DEPENDENCIES)
    solution = imports + '\n' + prefix + '''
open scoped RealInnerProductSpace
open Set Hirsch

theorem solution
''' + BINDERS + ''' := by
  exact HirschLowExcess.hpoly_diameter_le_excess_from_proved_inputs
    Hirsch.dimension_three_bound Hirsch.facet_reduction d n a b hrows hbd
'''
    return (prefix + adapter).encode('utf-8'), solution.encode('utf-8')


def prepare() -> None:
    driver, solution = expected_packets()
    PACKET.mkdir(parents=True, exist_ok=True)
    (PACKET / 'driver.lean').write_bytes(driver)
    (PACKET / 'solution.lean').write_bytes(solution)
    manifest = {
        'source_commit': SOURCE,
        'driver_git_blob': DRIVER_BLOB,
        'vertex_span_git_blob': VERTEX_BLOB,
        'driver_sha256': hashlib.sha256(driver).hexdigest(),
        'solution_sha256': hashlib.sha256(solution).hexdigest(),
        'target': NAME,
        'public_dependencies': {name: item['id'] for name, item in DEPENDENCIES.items()},
        'evidence_boundary': 'driver with explicit premises is locally auditable; unconditional composition is checked by Prove2Me against already-Proved imports',
    }
    (PACKET / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2), flush=True)


def publish() -> None:
    driver, solution = expected_packets()
    for filename, expected in [('driver.lean', driver), ('solution.lean', solution)]:
        if (PACKET / filename).read_bytes() != expected:
            raise RuntimeError('frozen packet mismatch: ' + filename)
    audit = PACKET / 'driver-audit-passed.sha256'
    if not audit.is_file() or audit.read_text().strip() != hashlib.sha256(driver).hexdigest():
        raise RuntimeError('kernel/axiom audit of the driver is missing')
    text = read_blob(CLIENT_COMMIT, CLIENT_PATH, CLIENT_BLOB).decode('utf-8')
    slot = '"Normalized two-moment slices have graph diameter at most two"'
    if text.count(slot) != 1:
        raise RuntimeError('reviewed client title slot changed')
    client = types.ModuleType('reviewed_low_excess_publisher')
    exec(compile(text.replace(slot, repr(TITLE), 1), CLIENT_PATH, 'exec'), client.__dict__)
    client.VERSION = '0.10.1'
    client.SOURCE, client.SOURCE_RUN = SOURCE, os.environ.get('GITHUB_RUN_ID', 'unknown')
    client.THEOREM_NAME, client.SOLUTION = NAME, PACKET / 'solution.lean'
    client.SOLUTION_SHA256 = hashlib.sha256(solution).hexdigest()
    client.OUT, client.PREAMBLE, client.FORMAL = OUT, PREAMBLE, FORMAL
    client.NATURAL, client.EXPLANATION = NATURAL, EXPLANATION
    api = client.API(os.environ.get('PROVE2ME_API_KEY', ''))
    for name, expected in DEPENDENCIES.items():
        record = api.request('/theorems/' + expected['id'])
        if (record.get('theorem_name') != name or record.get('status') != 'Proved'
                or record.get('mathlib_rev') != PIN
                or client.norm(record.get('formal_statement')) != client.norm(expected['formal'])):
            raise RuntimeError('Proved dependency identity/type/status mismatch: ' + name)
        client.save(OUT / (name.replace('.', '_') + '.json'), record)
    def link_mission(api, mission, result):
        mid, tid = mission['id'], result['theorem_id']
        offset = 0
        while True:
            page = api.request(f'/missions/{mid}/comments?limit=100&offset={offset}')
            rows = page.get('comments', [])
            for c in rows:
                if any(r.get('type') == 'theorem' and r.get('id') == tid for r in c.get('references', [])):
                    client.save(OUT / 'mission-comment.json', c)
                    return c
            offset += len(rows)
            if not rows or offset >= int(page.get('total', offset + 1)):
                break
        post = (f'Published [Hirsch for at most three excess describing rows](p2m:theorem/{tid})'
                + (f' with [accepted proof](p2m:solution/{result["submission_id"]})' if result.get('submission_id') else '')
                + ': every bounded n-row H-polyhedron in ambient dimension d with n<=d+3 '
                'has padded diameter <=n-d, including empty/degenerate sets and redundant/zero rows. '
                'This is a short classical small-excess consequence of the already-Proved low-dimensional '
                'Hirsch and facet-reduction results, not a new general diameter bound. '
                'For d>3, n<2d forces a shared NONZERO tight row; reducing to its equality section '
                'preserves n-d and costs no extra access steps. The proof explicitly excludes zero '
                'tautologies from the shared-row count and uses the actual ambient-walk conclusion '
                'of facet_reduction. In particular n<=d+2 now gives diameter <=2 WITHOUT needing '
                'positive slack-weight existence. This removes that existence theorem as a prerequisite '
                'for the diameter-only low-excess base case; exact slack normalization remains useful '
                'for explicit portal coordinates. The common-face M_min corollary can use an equivalent '
                'small subpresentation plus coordinate transport. General high-dimensional face diameter, '
                'ridge-visible access, whole-walk circuit-to-edge refinement, and Polynomial Hirsch '
                'remain Open. No new conjectural child was created.')
        comment = api.request(f'/missions/{mid}/comments', {'body_md': post, 'tags': ['reference', 'strategy']}, 'POST')
        client.save(OUT / 'mission-comment.json', comment)
        refs = {(r.get('type'), r.get('id')) for r in comment.get('references', [])}
        if ('theorem', tid) not in refs:
            raise RuntimeError('mission theorem reference unresolved')
        if result.get('submission_id') and ('solution', result['submission_id']) not in refs:
            raise RuntimeError('mission proof reference unresolved')
        return comment
    client.link_mission = link_mission
    client.main()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['prepare', 'publish'])
    args = parser.parse_args()
    prepare() if args.mode == 'prepare' else publish()
