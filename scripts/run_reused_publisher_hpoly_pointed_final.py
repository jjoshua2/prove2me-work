#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_hpoly_pointed', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'hpoly_pointed_publish_receipts'
pub.NAME = 'Hirsch.simultaneous_clip_diameter_from_pointed_finite_hpoly'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_pointed_finite_hpoly_clip_diameter.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution',
        'theorem simultaneous_clip_diameter_from_pointed_finite_hpoly', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Simultaneous clipping diameter bound for a pointed finite H-polyhedron'
        p['natural_language_statement'] = (
            'Let Q be a nonempty finite H-polyhedron in Euclidean space which contains no affine line. Suppose its old '
            'vertex-edge graph has padded diameter at most D. Intersect Q with finitely many additional linear halfspaces, '
            'and assume the final clipped set is compact. If the face where added inequality i is tight has intrinsic graph '
            'diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. '
            'The proof derives the no-common-row-kernel characterization of pointedness, proves the old H-vertex set is '
            'finite, chooses a canonical summed-normal far cap internally, classifies every new cap vertex as a horizon '
            'vertex adjacent to an old vertex, and applies the verified strict-centre-free exterior clipping transfer.'
        )
        p['source'] = 'Kernel-verified pointed finite-H-polyhedron cap construction and clipping transfer in jjoshua2/prove2me-work.'
        p['tags'] = ['polyhedra', 'graph-diameter', 'hirsch-conjecture', 'pointed-polyhedron', 'clipping', 'far-cap']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'For a nonempty finite H-polyhedron, absence of an affine line is equivalent to the row normals having no nonzero '
        'common-kernel direction. Extreme vertices are finite because the finite set of active row indices determines an '
        'extreme vertex injectively. Compactness of the final clip and finiteness of the old vertices therefore provide a '
        'cap level above both. Cap using minus the sum of all H-row normals. The cap is compact; old edges survive. At a new '
        'horizon vertex, the old active rows have a one-dimensional common kernel. Following an inward direction to the first '
        'new tight old inequality reaches an old vertex, and the intervening segment is an actual cap edge. Thus every cap '
        'vertex is old or horizon-adjacent to old. The horizon lies outside the final clip, so the strict-centre-free exterior '
        'routing theorem yields D + 1 + sum B_i.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'hpoly_pointed_packet/solution.lean').read_text())

pub.main()
