#!/usr/bin/env python3
from __future__ import annotations
import datetime, json, os, re, time, urllib.parse, urllib.request, uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "public_geodesic_publish_receipts"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch
"""

SPECS = [
  {
    "name": "Hirsch.reentry_splice_through_extreme_face",
    "title": "Replace a path reentry segment by an intrinsic extreme-face path",
    "proof": ROOT / "public_geodesic_packet/reentry_solution.lean",
    "formal": r'''namespace Hirsch

theorem reentry_splice_through_extreme_face
    (d L B s t : ℕ)
    (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hF : IsExtreme ℝ P F)
    (hFD : DiamLE F B)
    (u v : EuclideanSpace ℝ (Fin d))
    (w : ℕ → EuclideanSpace ℝ (Fin d))
    (hw0 : w 0 = u) (hwL : w L = v)
    (hwstep : ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1)))
    (hst : s ≤ t) (htL : t ≤ L)
    (hsP : w s ∈ extremePoints ℝ P)
    (htP : w t ∈ extremePoints ℝ P)
    (hsF : w s ∈ F) (htF : w t ∈ F) :
    ∃ w' : ℕ → EuclideanSpace ℝ (Fin d),
      w' 0 = u ∧ w' (s + B + (L - t)) = v ∧
      ∀ j < s + B + (L - t),
        w' j = w' (j + 1) ∨ Adj P (w' j) (w' (j + 1)) := by sorry

end Hirsch''',
    "natural": "If a padded graph walk in P visits an extreme face F at indices s≤t and F has intrinsic graph diameter at most B, replace the entire segment between those visits by a walk inside F. The resulting parent walk has exact padded budget s+B+(L-t), independent of how often the original segment left and re-entered F.",
    "explanation": "Edges of an extreme face are parent edges. Use the face diameter to connect the two selected visits inside F, retain the original prefix through s and suffix after t, and concatenate the three padded walks. The final budget is s+B+(L-t).",
  },
  {
    "name": "Hirsch.geodesic_face_disjoint_tail_bound",
    "title": "Order-sensitive extreme-face tail bound for graph diameter",
    "proof": ROOT / "public_geodesic_packet/tail_solution.lean",
    "formal": r'''namespace Hirsch

theorem geodesic_face_disjoint_tail_bound
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P (B + K) := by sorry

end Hirsch''',
    "natural": "Suppose every selected extreme face has intrinsic graph diameter at most B. For every start vertex u, suppose at most K vertices share no selected face with u. If the vertex graph is connected, then the whole graph has padded diameter at most B+K.",
    "explanation": "Choose a shortest padded walk from u to v. Two visits to the same selected face can be spliced through that face, so their index gap is at most B. Hence every path vertex after index B shares no selected face with u and belongs to the exceptional set T. A shortest path cannot repeat a vertex, so the tail contributes at most |T|≤K steps. Pad the resulting shortest walk to B+K.",
  },
]

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs): raise RuntimeError("authenticated redirects disabled")
class API:
    def __init__(self,key): self.key=key; self.token=""; self.expires=0.; self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+"/agent/refresh",data=json.dumps({"api_key":self.key}).encode(),headers={"Content-Type":"application/json"},method="POST")
        with self.opener.open(req,timeout=45) as r: d=json.load(r)
        self.token=d["access_token"]; self.expires=float(d.get("expires_at",time.time()+3500)); self.version=d.get("version")
    def request(self,path,data=None,method="GET",content_type="application/json"):
        if not self.token or time.time()+60>=self.expires: self.refresh()
        body=json.dumps(data).encode() if data is not None and not isinstance(data,bytes) else data
        req=urllib.request.Request(BASE+path,data=body,headers={"Authorization":"Bearer "+self.token,"Content-Type":content_type},method=method)
        with self.opener.open(req,timeout=90) as r: return json.load(r)
    def verify(self,theorem_id,proof,explanation):
        boundary="----Prove2Me"+uuid.uuid4().hex; parts=[]
        for name,value in [("theorem_id",theorem_id),("proof_type","prove"),("explanation",explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n')
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request("/verify","".join(parts).encode(),"POST","multipart/form-data; boundary="+boundary)

def norm(x): return re.sub(r"\s+","",x or "")
def save(name,obj): OUT.mkdir(exist_ok=True); (OUT/name).write_text(json.dumps(obj,indent=2)+"\n")
def rows(api,name):
    q=urllib.parse.urlencode({"env":PIN,"theorem_name":name,"limit":20,"offset":0}); return api.request("/theorems?"+q).get("theorems",[])
def wait_job(api,jid,timeout=420):
    end=time.monotonic()+timeout
    while True:
        x=api.request("/publish-jobs/"+jid)
        if x.get("status") in {"PUBLISHED","FAILED","ERROR"} or time.monotonic()>end: return x
        time.sleep(6)
def wait_verdict(api,sid,timeout=600):
    end=time.monotonic()+timeout; terminal={"ACCEPTED","SKETCH_ACCEPTED","CE","WA","SORRY","FAILED","ERROR"}
    while True:
        x=api.request("/verify?"+urllib.parse.urlencode({"submission_id":sid}))
        if x.get("status") in terminal or time.monotonic()>end: return x
        time.sleep(6)

def publish(api,spec):
    matches=rows(api,spec["name"])
    if matches:
        if len(matches)!=1: raise RuntimeError("name collision: "+spec["name"])
        th=api.request("/theorems/"+matches[0]["theorem_id"])
        if norm(th.get("formal_statement"))!=norm(spec["formal"]): raise RuntimeError("statement collision: "+spec["name"])
        tid=th["theorem_id"]
    else:
        q=api.request("/submit-problem",{"env":PIN,"private":False,"problems":[{"theorem_name":spec["name"],"theorem_title":spec["title"],"formal_statement":spec["formal"],"natural_language_statement":spec["natural"],"preamble":PREAMBLE,"source":"Verified Polynomial Hirsch graph-geometry helper developed in the September 2026 formalization; see jjoshua2/prove2me-work PR #27.","tags":["polyhedra","graph-diameter","hirsch-conjecture","extreme-faces"]}]},"POST")
        if q.get("errors") or len(q.get("jobs",[]))!=1: raise RuntimeError("publish queue failed: "+spec["name"])
        job=wait_job(api,q["jobs"][0]["job_id"]); save(spec["name"].replace(".","_")+"-publish.json",job)
        if job.get("status")!="PUBLISHED": raise RuntimeError("publication failed: "+spec["name"])
        tid=job["theorem_id"]
    th=api.request("/theorems/"+tid)
    if th.get("status")=="Proved": return {"theorem_id":tid,"status":"Proved","skipped":True}
    if th.get("status")!="Open": raise RuntimeError("unexpected status: "+str(th.get("status")))
    proof=spec["proof"].read_text(); q=api.verify(tid,proof,spec["explanation"]); sid=q["submission_id"]
    verdict=wait_verdict(api,sid); save(spec["name"].replace(".","_")+"-verdict.json",verdict)
    after=api.request("/theorems/"+tid).get("status")
    if verdict.get("status")!="ACCEPTED" or after!="Proved": raise RuntimeError(f"verify failed {spec['name']}: {verdict.get('status')} / {after}")
    return {"theorem_id":tid,"submission_id":sid,"verdict":"ACCEPTED","status":"Proved"}

def main():
    key=os.environ.get("PROVE2ME_API_KEY","").strip()
    if not key: raise RuntimeError("PROVE2ME_API_KEY unavailable")
    api=API(key); result={"started_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),"env":PIN,"results":{}}
    for spec in SPECS: result["results"][spec["name"]]=publish(api,spec); save("status.json",result)
    print(json.dumps(result,indent=2)); return 0
if __name__=="__main__":
    try: raise SystemExit(main())
    except Exception as e:
        OUT.mkdir(exist_ok=True); save("failure.json",{"error_type":type(e).__name__,"error":str(e)[:700]})
        raise
