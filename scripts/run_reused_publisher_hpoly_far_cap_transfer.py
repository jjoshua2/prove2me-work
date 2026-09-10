#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_hpoly_far_cap', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'hpoly_far_cap_publish_receipts'
pub.NAME = 'Hirsch.simultaneous_clip_diameter_from_finite_hpoly_far_cap'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_finite_hpoly_far_cap_diameter.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution',
        'theorem simultaneous_clip_diameter_from_finite_hpoly_far_cap', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Canonical far-cap transfer for simultaneous clipping of a finite pointed H-polyhedron'
        p['natural_language_statement'] = (
            'Let Q be the finite H-polyhedron A_j x <= b_j in Euclidean space, with no nonzero direction annihilated by every '
            'row normal. Let its vertex-edge graph have padded diameter at most D. Use the canonical cap normal equal to minus '
            'the sum of all H-row normals, and choose a level T at least as large as its value on every old vertex and strictly '
            'larger than its value on every point of the final simultaneous clip. If final cut face i has intrinsic graph '
            'diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. The '
            'proof constructs the compact cap, proves old edges survive, classifies every new cap vertex as a horizon vertex '
            'adjacent to an old vertex, and applies the strict-centre-free exterior-route clipping transfer.'
        )
        p['source'] = 'Kernel-verified canonical finite-H-polyhedron far-cap construction and transfer in jjoshua2/prove2me-work.'
        p['tags'] = ['polyhedra', 'graph-diameter', 'hirsch-conjecture', 'clipping', 'far-cap', 'h-polyhedron']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'Define the cap normal as minus the sum of the finite H-row normals and cap Q at level T. The no-common-kernel '
        'hypothesis makes the capped H-polyhedron compact. Old vertices and old graph edges below T survive. At a genuinely '
        'new horizon vertex, the old active rows have a one-dimensional common kernel; an inward direction in that kernel '
        'hits a previously inactive old inequality at a positive minimum time. The hit point is an old H-polyhedron vertex, '
        'and the intervening segment is an actual edge of the capped polyhedron. Thus every cap vertex is old or is a horizon '
        'vertex adjacent to an old one. Since the final clipped set lies strictly below T, capping does not change it and the '
        'horizon is exterior. Apply the verified strict-centre-free exterior-cap routing theorem to obtain D + 1 + sum B_i.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'hpoly_far_cap_packet/solution.lean').read_text())

pub.main()
