#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_start',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'interval_start_portal_publish_receipts'; pub.NAME='Hirsch.face_interval_cover_route_bound_of_start_containment'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n'''
s=(ROOT/'Solutions/Sol_Hirsch_face_interval_start_containment_route_bound.lean').read_text(); sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem face_interval_cover_route_bound_of_start_containment',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']='Start containment supplies portals for crossing extreme-face interval repair'; p['natural_language_statement']='A finite extreme-face interval cover routes its endpoint vertices within the sum of the face diameter budgets when every later interval start that occurs before an earlier interval ends lies in the earlier supporting face. The later start is then automatically a shared parent-vertex portal between the two overlapping faces.'; p['source']='Verified Lean theorem from jjoshua2/prove2me-work PR #48.'; p['tags']=['polyhedra','graph-diameter','hirsch-conjecture','path-repair','intervals']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,'For overlapping intervals, compare their start indices. The later start lies in its own supporting face and, by start-containment, in the earlier still-active face, so it is a genuine shared parent-vertex portal. The previously verified portal-backed interval-cover theorem then concatenates intrinsic extreme-face routes with total budget equal to the sum of the face diameter budgets.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True); (proofdir/'solution.lean').write_text((ROOT/'public_interval_start_portal_packet/solution.lean').read_text())
pub.main()
