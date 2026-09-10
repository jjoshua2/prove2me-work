#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_exterior_cap_no_strict', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'exterior_cap_no_strict_publish_receipts'
pub.NAME = 'Hirsch.simultaneous_clip_diameter_of_exterior_cap_without_strict_centre'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_exterior_cap_clip_diameter_no_strict.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution',
        'theorem simultaneous_clip_diameter_of_exterior_cap_without_strict_centre', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Exterior-cap simultaneous clipping needs no separately supplied strict centre'
        p['natural_language_statement'] = (
            'Let R be a compact convex outer polytope with an exterior convex cap G and a set V of old vertices. Assume old '
            'vertices route within D graph edges and every other outer extreme vertex lies on G adjacent to an old vertex. '
            'For finitely many simultaneous cuts, assume G lies outside the final clipped polytope and each final cut face has '
            'intrinsic graph diameter at most B_i. Then the final clipped polytope has padded graph diameter at most '
            'D + 1 + sum_i B_i. No strict feasible centre is an input: either finite convex averaging produces one, or one '
            'cut is equality on the whole final polytope and its face budget closes the bound directly.'
        )
        p['source'] = 'Kernel-verified Lean strengthening of the exterior-cap clipping theorem in jjoshua2/prove2me-work.'
        p['tags'] = ['polyhedra','graph-diameter','hirsch-conjecture','clipping','repair-networks']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'Apply the finite strict-centre dichotomy to the final clipped polytope. If no cut is universal, choose for each cut a '
        'point where it is strict and repeatedly average these finitely many witnesses; convexity preserves feasibility and '
        'produces one point strict for every cut. The already verified exterior-cap radial theorem then gives D+1+sum B_i. '
        'If some cut is equality everywhere, the final polytope equals that final cut face, so its assumed B_i diameter bound '
        'pads directly to D+1+sum B_i. The empty final polytope is vacuous.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'exterior_cap_no_strict_packet/solution.lean').read_text())

pub.main()
