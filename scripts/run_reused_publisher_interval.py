#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT
pub.OUT=ROOT/'interval_repair_publish_receipts'
pub.NAME='Hirsch.face_interval_cover_route_bound'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n'''
s=(ROOT/'Solutions/Sol_Hirsch_face_interval_cover_route_bound.lean').read_text()
sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem face_interval_cover_route_bound',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]
        p['theorem_title']='Portal-backed crossing interval repair through extreme faces'
        p['natural_language_statement']='If repair intervals cover every old step and every chronological overlap is backed by a genuine shared parent vertex between the corresponding extreme faces, the endpoints admit a padded parent walk whose budget is the sum of the face diameter budgets.'
        p['source']='Verified Lean theorem from jjoshua2/prove2me-work PR #39.'
        p['tags']=['polyhedra','graph-diameter','hirsch-conjecture','path-repair']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation):
    return orig_verify(self,tid,proof,'Interval overlap gives a connected region-intersection graph because every overlap has an actual shared parent vertex. Concatenate intrinsic extreme-face walks along a simple region path, paying each face budget once.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True)
(proofdir/'solution.lean').write_text((ROOT/'public_interval_repair_packet/solution.lean').read_text())
pub.main()
