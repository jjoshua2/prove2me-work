#!/usr/bin/env python3
from __future__ import annotations
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_cube',base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'cube_obstruction_publish_receipts'; pub.NAME='Hirsch.crossing_cube_endpoint_certificate_insufficient'
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen Set\n'''
s=(ROOT/'Solutions/Sol_Hirsch_crossing_cube_endpoint_obstruction.lean').read_text(); sig='theorem solution'+s.split('theorem solution',1)[1].split(' := by',1)[0]
pub.FORMAL='namespace Hirsch\n\n'+sig.replace('theorem solution','theorem crossing_cube_endpoint_certificate_insufficient',1)+' := by sorry\n\nend Hirsch'
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']='Crossing endpoint-only repair certificates fail on Boolean cubes'; p['natural_language_statement']='For every Boolean cube dimension d at least six there are two unit-cost repair regions and a four-checkpoint crossing sequence whose two repair intervals cover all three old step slots, but the opposite cube endpoints admit no padded route of length five. Thus chronological crossing plus endpoint-local repair certificates alone cannot imply the loose L plus sum-of-budgets repair bound.'; p['source']='Verified Lean obstruction from jjoshua2/prove2me-work PR #41.'; p['tags']=['graph-diameter','hirsch-conjecture','counterexample','path-repair','cube']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,'Represent cube vertices by subsets of coordinates and edges by inserting or deleting one coordinate. Two opposite parallel edges give the two unit-cost repair regions. Their crossing chronological intervals cover all old step positions, but the all-zero to all-one route changes at most one coordinate per graph step, so dimension at least six rules out the proposed five-step repair.')
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True); (proofdir/'solution.lean').write_text((ROOT/'public_cube_obstruction_packet/solution.lean').read_text())
pub.main()
