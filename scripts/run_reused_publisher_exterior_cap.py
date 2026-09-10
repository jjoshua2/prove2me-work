#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_exterior_cap', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'exterior_cap_publish_receipts'
pub.NAME = 'Hirsch.simultaneous_clip_diameter_of_exterior_cap'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_exterior_cap_clip_diameter.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution', 'theorem simultaneous_clip_diameter_of_exterior_cap', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Exterior-cap witness transfers an outer route to a simultaneously clipped polytope'
        p['natural_language_statement'] = (
            'Let a compact convex outer polytope R have a distinguished set V of old vertices whose graph diameter is at most D, '
            'and an exterior cap G such that every other outer extreme vertex lies on G and is adjacent to an old vertex. '
            'Assume a common strict centre for finitely many cuts, that the cap lies outside the final clipped polytope, and that '
            'each final cut face has intrinsic graph diameter at most B_i. Then the final clipped polytope has padded graph '
            'diameter at most D + 1 + sum_i B_i. The exterior cap and strict centre are explicit hypotheses; this theorem does '
            'not assert existence of such a cap for every pointed H-polyhedron.'
        )
        p['source'] = 'Kernel-verified Lean theorem from jjoshua2/prove2me-work PR #52.'
        p['tags'] = ['polyhedra', 'graph-diameter', 'hirsch-conjecture', 'clipping', 'repair-networks']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'Truncate the pointed outer geometry by an explicit compact exterior cap. Old vertices route within D steps; every cap '
        'vertex is adjacent to an old vertex, so old/cap attachments cost at most one extra outer edge. A fixed radial retraction '
        'from the strict centre sends the exterior cap and clipped outer traces into the union of the final cut faces. The '
        'face-preserving repair machinery charges each distinct final cut face once, giving total padded diameter D + 1 + sum B_i.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'exterior_cap_offline_packet/solution.lean').read_text())

pub.main()
