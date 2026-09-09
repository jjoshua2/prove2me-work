#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_cut',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'repair_network_cut_publish_receipts'; pub.NAME='Hirsch.extreme_face_cut_route_bound'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n'''
s=(ROOT/'Solutions/Sol_Hirsch_extreme_face_cut_route_bound.lean').read_text(); sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem extreme_face_cut_route_bound',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']='Extreme-face repair networks route when every separating cut is bridged'; p['natural_language_statement']='For a finite family of extreme faces with diameter budgets, if every partition separating the endpoint face labels has a genuine parent vertex shared across the cut, then the endpoint vertices admit a padded parent walk with budget equal to the sum of the face budgets.'; p['source']='Verified Lean theorem from jjoshua2/prove2me-work PR #41.'; p['tags']=['polyhedra','graph-diameter','hirsch-conjecture','repair-network']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,'The cut condition is equivalent to connectivity of the finite face-intersection network. Choose a simple path of face labels and concatenate intrinsic extreme-face routes through shared parent vertices; a simple label path charges each face at most once.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True); (proofdir/'solution.lean').write_text((ROOT/'public_repair_network_cut_packet/solution.lean').read_text())
pub.main()
