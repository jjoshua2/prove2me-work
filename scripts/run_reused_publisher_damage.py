#!/usr/bin/env python3
from __future__ import annotations
import importlib.util, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
label=sys.argv[1]
SPECS={
 'ordered_exact':('Hirsch.ordered_damage_repair_exact','Exact ordered damage repair with surviving gaps','Marked ordered damage intervals may contain destroyed steps; only the gaps between them must survive. Replacing each damaged interval through its certified extreme face gives exact padded budget L minus removed interval length plus the sum of replacement face budgets.','The ordered intervals are disjoint. Keep each surviving gap, replace every marked interval by an intrinsic extreme-face walk, concatenate the pieces, and pad to the exact budget.'),
 'mixed_regions':('Hirsch.route_of_faces_and_surviving_edges','Routing from face regions and surviving edges','If every consecutive checkpoint pair is covered either by one certified extreme face or by one listed surviving parent edge, then a genuine parent walk has budget equal to the sum of all face diameter budgets plus the number of listed surviving edges.','Build the finite region graph using certified faces and two-point surviving-edge regions, take a simple region path between the endpoint regions, then concatenate local routes and charge each indexed region once.')}
name,title,natural,explain=SPECS[label]
base=ROOT/'_publisher_source/scripts/publish_public_geodesic_face_cover.py'
spec=importlib.util.spec_from_file_location('basepub_'+label,base); pub=importlib.util.module_from_spec(spec); spec.loader.exec_module(pub)
pub.ROOT=ROOT; pub.OUT=ROOT/'damage_repair_publish_receipts'/label; pub.NAME=name
pub.PREAMBLE='''import Mathlib\nimport Definitions.Def_Hirsch_model\n\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n'''
statement=(ROOT/f'damage_progress_packet/{label}_statement.lean.txt').read_text()
pub.FORMAL=statement[statement.index('theorem Hirsch.'):].strip()
orig_req=pub.API.request
def request(self,path,data=None,method='GET',content_type='application/json'):
    if path=='/submit-problem' and data:
        p=data['problems'][0]; p['theorem_title']=title; p['natural_language_statement']=natural; p['source']='Verified Lean theorem from jjoshua2/prove2me-work PR #40.'; p['tags']=['polyhedra','graph-diameter','hirsch-conjecture','path-repair']
    return orig_req(self,path,data,method,content_type)
pub.API.request=request
orig_verify=pub.API.verify
def verify(self,tid,proof,explanation): return orig_verify(self,tid,proof,explain)
pub.API.verify=verify
proofdir=ROOT/'public_geodesic_face_cover_packet'; proofdir.mkdir(exist_ok=True)
(proofdir/'solution.lean').write_text((ROOT/f'damage_progress_packet/{label}.lean').read_text())
pub.main()
