#!/usr/bin/env python3
from __future__ import annotations
import json, os, time, urllib.parse, urllib.request
from pathlib import Path

BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
OUT = Path("publication_backlog_audit")
NAMES = [
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
    "Hirsch.polynomial_edge_refinement_of_circuit_walks",
    "Hirsch.reentry_splice_through_extreme_face",
    "Hirsch.geodesic_face_disjoint_tail_bound",
]

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): raise RuntimeError("redirect disabled")
class API:
    def __init__(self,key): self.key=key; self.token=""; self.expires=0.; self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+"/agent/refresh",data=json.dumps({"api_key":self.key}).encode(),headers={"Content-Type":"application/json"},method="POST")
        with self.opener.open(req,timeout=45) as r: d=json.load(r)
        self.token=d["access_token"]; self.expires=float(d.get("expires_at",time.time()+3500)); self.version=d.get("version")
    def get(self,path):
        if not self.token or time.time()+60>=self.expires: self.refresh()
        req=urllib.request.Request(BASE+path,headers={"Authorization":"Bearer "+self.token})
        with self.opener.open(req,timeout=60) as r: return json.load(r)

def main():
    key=os.environ.get("PROVE2ME_API_KEY","").strip()
    if not key: raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api=API(key); rows={}
    for name in NAMES:
        q=urllib.parse.urlencode({"env":PIN,"theorem_name":name,"limit":20,"offset":0})
        items=api.get("/theorems?"+q).get("theorems",[])
        rows[name]=[{k:x.get(k) for k in ("theorem_id","theorem_name","theorem_title","status","mathlib_rev","deprecated_at")} for x in items if x.get("theorem_name")==name]
    OUT.mkdir(exist_ok=True)
    result={"platform_version":api.version,"env":PIN,"theorems":rows}
    (OUT/"audit.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
    return 0
if __name__=="__main__": raise SystemExit(main())
