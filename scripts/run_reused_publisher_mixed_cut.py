#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_mixedcut',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'mixed_repair_cut_publish_receipts'; pub.NAME='Hirsch.mixed_repair_route_or_cut'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators\nopen Set\n'''
s=(ROOT/'Solutions/Sol_Hirsch_mixed_repair_route_or_cut.lean').read_text(); sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem mixed_repair_route_or_cut',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']='Mixed repair network gives a route or an explicit closed cut'; p['natural_language_statement']='Given finitely many locally routable regions together with finitely many surviving bidirectional edges, either their supplied repair network routes the endpoints within the sum of all region budgets plus the number of surviving edges, or there is an explicit vertex subset separating the endpoints that is closed under every region and every supplied edge.'; p['source']='Verified generic theorem isolated from jjoshua2/prove2me-work PR #42.'; p['tags']=['graph-diameter','hirsch-conjecture','path-repair','cut-certificate']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,'Form the mixed family consisting of the locally routable regions and two-point regions for surviving bidirectional edges. Finite reachability yields either a simple region route, which concatenates to the stated bounded walk, or the set of vertices reachable through supplied regions, which is a closed separating cut.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True); (proofdir/'solution.lean').write_text((ROOT/'portal_cut_packet/solution.lean').read_text())
pub.main()
