#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_active',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'interval_active_containment_publish_receipts'; pub.NAME='Hirsch.face_interval_cover_route_bound_of_active_containment'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n'''
s=(ROOT/'Solutions/Sol_Hirsch_face_interval_active_containment_route_bound.lean').read_text(); sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem face_interval_cover_route_bound_of_active_containment',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']='Whole active-interval face containment supplies crossing repair portals'; p['natural_language_statement']='For a finite extreme-face interval cover, if every listed interval is valid and every checkpoint throughout that interval lies in its supporting face, then the endpoint vertices admit a padded route with budget equal to the sum of the face diameter budgets. Overlap portals are automatic because the later interval start lies in both active faces.'; p['source']='Verified Lean theorem from jjoshua2/prove2me-work PR #48.'; p['tags']=['polyhedra','graph-diameter','hirsch-conjecture','path-repair','intervals']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,'Whole-interval containment implies start-containment: whenever a later interval begins before an earlier interval ends, its start checkpoint lies in the earlier supporting face and in its own supporting face. The verified start-containment interval theorem then supplies the route with total budget equal to the sum of the face diameter budgets.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True); (proofdir/'solution.lean').write_text((ROOT/'public_interval_active_containment_packet/solution.lean').read_text())
pub.main()
