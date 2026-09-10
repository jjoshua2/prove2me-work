#!/usr/bin/env python3
from __future__ import annotations
import json, os, time, urllib.parse, urllib.request
from pathlib import Path

BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
OUT = Path("publication_backlog_audit")

PROVED_NAMES = [
    "Hirsch.santos_counterexample",
    "Hirsch.balanced_hpoly_transfer",
    "Hirsch.diameter_bound_of_target_face_access",
    "Hirsch.nonzero_supporting_row_of_distinct_extremes",
    "Hirsch.vertex_tight_rows_span",
    "Hirsch.target_face_access_of_local_neutral_rank",
    "Hirsch.given_supporting_face_access_of_boundary_residual_rank",
    "Hirsch.vertex_exposing_redundant_row_extension",
    "Hirsch.given_supporting_face_access_of_boundary_product_factors",
    "Hirsch.cut_face_access_of_outer_diameter",
    "Hirsch.clipped_diameter_le_outer_add_cut_face",
    "Hirsch.cut_face_access_of_unbounded_outer_diameter",
    "Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one",
    "Hirsch.box_slice_diameter_le_dimension",
    "Hirsch.cubic_circuit_walk_bound",
    "HirschCircuit.rowMap_injective_of_bounded",
    "HirschCircuit.rowCircuitWalk_mono",
    "HirschCircuit.exists_positive_maximal_nonnegative_step",
    "Hirsch.reentry_splice_through_extreme_face",
    "Hirsch.geodesic_face_disjoint_tail_bound",
    "Hirsch.geodesic_face_cover_diameter_bound",
    "Hirsch.common_face_dimension_tradeoff",
    "Hirsch.common_face_effective_count_le_rows_minus_common",
    "Hirsch.common_face_diameter_of_effective_rows",
    "Hirsch.separated_common_face_split",
    "Hirsch.face_interval_cover_route_bound",
    "Hirsch.ordered_damage_repair_exact",
    "Hirsch.route_of_faces_and_surviving_edges",
    "Hirsch.extreme_face_cut_route_bound",
    "Hirsch.mixed_repair_route_or_cut",
    "Hirsch.crossing_cube_endpoint_certificate_insufficient",
    "Hirsch.face_interval_cover_route_bound_of_start_containment",
    "Hirsch.face_interval_cover_route_bound_of_active_containment",
    "Hirsch.compact_extreme_face_contains_parent_vertex",
    "Hirsch.feasible_point_has_face_preserving_parent_vertex",
    "Hirsch.closed_extreme_faces_shared_point_has_parent_vertex",
    "Hirsch.feasible_face_covered_sequence_route_bound",
    "Hirsch.face_preserving_vertex_selection",
    "Hirsch.face_interval_cover_route_bound_of_feasible_start_containment",
    "Hirsch.face_interval_cover_route_bound_of_feasible_active_containment",
    "Hirsch.simultaneous_clip_diameter_of_exterior_cap",
]
OPEN_NAMES = ["Hirsch.polynomial_edge_refinement_of_circuit_walks"]
EXPECTED_IDS = {
    "conformal_decomposition_publication": ("05726681-715c-408a-b44c-d73dac856b20", "Proved"),
    "Hirsch_circuit_slack_model": ("26b46900-d139-4f6c-b2e7-5088faed7b9e", "Definition"),
    "Hirsch_common_face_geometry": ("dc9161e6-0dae-4da5-ab82-91b871e2409e", "Definition"),
}

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): raise RuntimeError("redirect disabled")
class API:
    def __init__(self,key):
        self.key=key; self.token=""; self.expires=0.; self.version=None
        self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+"/agent/refresh",data=json.dumps({"api_key":self.key}).encode(),headers={"Content-Type":"application/json"},method="POST")
        with self.opener.open(req,timeout=45) as r: d=json.load(r)
        self.token=d["access_token"]; self.expires=float(d.get("expires_at",time.time()+3500)); self.version=d.get("version")
    def get(self,path):
        if not self.token or time.time()+60>=self.expires: self.refresh()
        req=urllib.request.Request(BASE+path,headers={"Authorization":"Bearer "+self.token})
        with self.opener.open(req,timeout=60) as r: return json.load(r)

def lookup_name(api,name):
    q=urllib.parse.urlencode({"env":PIN,"theorem_name":name,"limit":20,"offset":0})
    items=api.get("/theorems?"+q).get("theorems",[])
    return [x for x in items if x.get("theorem_name")==name and not x.get("deprecated_at")]

def main():
    key=os.environ.get("PROVE2ME_API_KEY","").strip()
    if not key: raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api=API(key); rows={}; failures=[]
    for name in PROVED_NAMES:
        items=lookup_name(api,name)
        rows[name]=[{k:x.get(k) for k in ("theorem_id","theorem_name","theorem_title","status","mathlib_rev","deprecated_at")} for x in items]
        if len(items) != 1: failures.append(f"{name}: expected exactly one live theorem, found {len(items)}")
        elif items[0].get("status") != "Proved": failures.append(f"{name}: expected Proved, got {items[0].get('status')}")
    for name in OPEN_NAMES:
        items=lookup_name(api,name)
        rows[name]=[{k:x.get(k) for k in ("theorem_id","theorem_name","theorem_title","status","mathlib_rev","deprecated_at")} for x in items]
        if len(items) != 1: failures.append(f"{name}: expected exactly one live theorem, found {len(items)}")
        elif items[0].get("status") != "Open": failures.append(f"{name}: expected Open frontier, got {items[0].get('status')}")
    by_id={}
    for label,(tid,expected) in EXPECTED_IDS.items():
        item=api.get("/theorems/"+tid)
        by_id[label]={k:item.get(k) for k in ("theorem_id","theorem_name","theorem_title","status","mathlib_rev","deprecated_at")}
        if item.get("status") != expected: failures.append(f"{label} {tid}: expected {expected}, got {item.get('status')}")
    OUT.mkdir(exist_ok=True)
    result={"platform_version":api.version,"env":PIN,"expected_proved_count":len(PROVED_NAMES),"expected_open_count":len(OPEN_NAMES),"theorems":rows,"by_id":by_id,"failures":failures,"audit":"PASSED" if not failures else "FAILED"}
    (OUT/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    if failures: raise RuntimeError("publication audit failed: " + "; ".join(failures))
    return 0

if __name__=="__main__": raise SystemExit(main())
