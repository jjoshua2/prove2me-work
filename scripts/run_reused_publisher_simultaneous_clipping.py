#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_simclip', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'simultaneous_clipping_publish_receipts'
pub.NAME = 'Hirsch.simultaneous_clipping_diameter_bound'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_simultaneous_clipping_diameter_bound.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution', 'theorem simultaneous_clipping_diameter_bound', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Simultaneous halfspace clipping charges only final cut-face diameters'
        p['natural_language_statement'] = (
            'Let Q be a compact convex polytope with padded graph diameter at most D, and intersect it simultaneously with a '
            'finite family of halfspaces. If the intrinsic graph diameter of each supporting equality face in the FINAL clipped '
            'polytope is at most B_i, then every two extreme vertices of the final clipped polytope are joined by a padded graph '
            'walk of length at most D + sum_i B_i. The endpoints need not be extreme vertices of Q, and no strict-centre '
            'hypothesis appears in the theorem statement.'
        )
        p['source'] = 'Kernel-checked Lean theorem from jjoshua2/prove2me-work PR #53, isolated from the later unfinished horizon-cap module.'
        p['tags'] = ['polyhedra', 'graph-diameter', 'hirsch-conjecture', 'clipping', 'repair-networks']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'If the final intersection has a point strict for every added cut, lift each final endpoint to an outer extreme vertex and '
        'radially retract the endpoint spokes and an outer D-step walk. The resulting connected trace is covered by clipped old '
        'edge pieces and the final cut faces; finite closed-face routing and face-preserving vertex selection charge the outer '
        'walk by D and each final cut face once. If no common strict point exists, convex averaging shows some cut is equality on '
        'the whole final polytope, whose assumed B_i budget directly bounds the answer.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'public_simultaneous_clipping_packet/solution.lean').read_text())

pub.main()
