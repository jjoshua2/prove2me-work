#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
base = ROOT / '_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec = importlib.util.spec_from_file_location('basepub_exterior_route_no_strict', base)
pub = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pub)

pub.ROOT = ROOT
pub.OUT = ROOT / 'exterior_route_no_strict_publish_receipts'
pub.NAME = 'Hirsch.clip_diameter_from_exterior_routes_without_strict_centre'
pub.PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
'''

source = (ROOT / 'Solutions/Sol_Hirsch_exterior_route_clip_diameter_no_strict.lean').read_text()
sig = 'theorem solution' + source.split('theorem solution', 1)[1].split(' := by', 1)[0]
pub.FORMAL = (
    'namespace Hirsch\n\n'
    + sig.replace('theorem solution',
        'theorem clip_diameter_from_exterior_routes_without_strict_centre', 1)
    + ' := by sorry\n\nend Hirsch'
)

orig_request = pub.API.request

def request(self, path, data=None, method='GET', content_type='application/json'):
    if path == '/submit-problem' and data:
        p = data['problems'][0]
        p['theorem_title'] = 'Exterior shortcuts plus final cut-face budgets transfer diameter without a strict centre'
        p['natural_language_statement'] = (
            'Let R be a compact convex outer polytope and G a convex exterior region contained in R but disjoint from the final '
            'simultaneously clipped polytope. Assume every pair of outer extreme vertices has a padded D-step route whose steps '
            'are either true R-edges or arbitrary jumps with both endpoints in G. If final cut face i has intrinsic graph '
            'diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + sum_i B_i. No strict '
            'feasible centre is assumed: finite averaging produces one unless a cut is equality everywhere, in which case its '
            'face budget bounds the whole final polytope directly.'
        )
        p['source'] = 'Kernel-verified generic exterior-route transfer in jjoshua2/prove2me-work.'
        p['tags'] = ['polyhedra','graph-diameter','hirsch-conjecture','clipping','repair-networks']
    return orig_request(self, path, data, method, content_type)

pub.API.request = request

orig_verify = pub.API.verify

def verify(self, tid, proof, explanation):
    return orig_verify(
        self,
        tid,
        proof,
        'Use the finite strict-centre dichotomy on the final clipped polytope. In the strict case, continuously retract the '
        'supplied outer edge/exterior-jump routes into the final polytope; every exterior jump is covered by final cut faces, '
        'so connected closed-face routing charges each B_i once. In the universal-cut case, the final polytope itself equals '
        'one final cut face and its B_i budget pads to D+sum B_i. The empty case is vacuous.'
    )

pub.API.verify = verify

proofdir = ROOT / 'public_geodesic_face_cover_packet'
proofdir.mkdir(exist_ok=True)
(proofdir / 'solution.lean').write_text((ROOT / 'exterior_route_no_strict_packet/solution.lean').read_text())

pub.main()
