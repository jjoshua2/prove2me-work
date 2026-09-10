#!/usr/bin/env python3
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.parse
import urllib.request
import uuid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "checkpoint_backlog_publication_receipts"
BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
PREAMBLE = """import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
"""

ACTIVE = r'''import Solutions.PolynomialIntervalStartPortals

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  exact HirschRegionRoute.route_of_face_interval_cover_of_active_containment
    P F B hF hD s t w L hvalid hbound hverts hcover hactive

#print axioms solution
'''

COMPACT_FACE = r'''import Solutions.PolynomialFacePreservingCheckpoints

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hclosed : IsClosed F)
    (hne : F.Nonempty) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F := by
  exact HirschRegionRoute.compact_face_point_has_parent_vertex P F hP hF hclosed hne

#print axioms solution
'''

PRESERVE_POINT = r'''import Solutions.PolynomialFacePreservingCheckpoints

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P) :
    ∃ v, v ∈ extremePoints ℝ P ∧ ∀ i, x ∈ F i → v ∈ F i := by
  exact HirschRegionRoute.exists_vertex_preserving_face_memberships
    P F hP hF hclosed x hx

#print axioms solution
'''

SHARED_PORTAL = r'''import Solutions.PolynomialFacePreservingCheckpoints

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (x : EuclideanSpace ℝ (Fin d)) (hxF : x ∈ F) (hxG : x ∈ G) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G := by
  exact HirschRegionRoute.compact_faces_shared_point_portal
    P F G hP hF hG hFc hGc x hxF hxG

#print axioms solution
'''

FEASIBLE_SEQUENCE = r'''import Solutions.PolynomialFacePreservingCheckpoints

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ P)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  exact HirschRegionRoute.route_of_feasible_face_covered_sequence
    P F B hP hF hclosed hD w L hfeas h0 hL hcover

#print axioms solution
'''

FEASIBLE_ACTIVE = r'''import Solutions.PolynomialFacePreservingCheckpoints

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

noncomputable section

theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i) (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by
  exact HirschRegionRoute.route_of_face_interval_cover_of_feasible_active_containment
    P F B hP hF hclosed hD s t w L hvalid hbound h0 hL hcover hactive

#print axioms solution
'''

SPECS = [
    dict(label="active_containment", name="Hirsch.face_interval_cover_route_bound_of_active_containment",
         short="face_interval_cover_route_bound_of_active_containment", wrapper=ACTIVE,
         title="Active-containment interval routing through extreme faces",
         natural="If each valid interval of a finite checkpoint sequence stays inside its supporting extreme face throughout the interval, the endpoint vertices are joined by a padded parent-edge walk whose length is at most the sum of the supplied intrinsic face-diameter budgets.",
         explanation="Whole-interval containment implies the start-containment portal condition: whenever a later interval starts while an earlier one is active, that later start is a parent vertex lying in both faces. The verified start-containment routing theorem then pays each face budget once."),
    dict(label="compact_face_vertex", name="Hirsch.compact_extreme_face_contains_parent_vertex",
         short="compact_extreme_face_contains_parent_vertex", wrapper=COMPACT_FACE,
         title="A nonempty closed extreme face of a compact parent contains a parent vertex",
         natural="Every nonempty closed extreme subset of a compact Euclidean parent contains a point that is extreme in the parent and lies in the subset.",
         explanation="The closed extreme subset is compact as a closed subset of the compact parent. Krein-Milman gives an extreme point of that subset, and extremality of the subset promotes it to an extreme point of the parent."),
    dict(label="preserve_point", name="Hirsch.feasible_point_has_face_preserving_parent_vertex",
         short="feasible_point_has_face_preserving_parent_vertex", wrapper=PRESERVE_POINT,
         title="A feasible point can be rounded to a parent vertex preserving all closed-face memberships",
         natural="For a compact parent and any family of closed extreme faces, every feasible point has a parent extreme vertex that lies in every supplied face containing the point; the face family need not be finite.",
         explanation="Intersect the parent with every supplied closed extreme face containing the point. The intersection remains nonempty, closed, compact, and extreme. A parent extreme point of that intersection preserves all those memberships simultaneously."),
    dict(label="shared_portal", name="Hirsch.closed_extreme_faces_shared_point_has_parent_vertex",
         short="closed_extreme_faces_shared_point_has_parent_vertex", wrapper=SHARED_PORTAL,
         title="Intersecting closed extreme faces of a compact parent share a parent vertex",
         natural="If two closed extreme faces of a compact Euclidean parent share any point, even a nonvertex point, they share a parent extreme vertex.",
         explanation="The intersection of the two closed extreme faces is again closed and extreme in the compact parent and is nonempty by the supplied witness. Applying the compact-face vertex theorem gives a parent extreme vertex in both faces."),
    dict(label="feasible_sequence", name="Hirsch.feasible_face_covered_sequence_route_bound",
         short="feasible_face_covered_sequence_route_bound", wrapper=FEASIBLE_SEQUENCE,
         title="Feasible face-covered checkpoints route with one charge per face",
         natural="For a feasible checkpoint sequence in a compact parent, if each consecutive checkpoint pair lies in one supplied closed extreme face and the global endpoints are parent vertices, then there is a padded parent-edge route with total length at most the sum of the supplied face-diameter budgets. Intermediate checkpoints need not be vertices.",
         explanation="Choose one face-membership-preserving parent vertex for every feasible checkpoint, fixing the endpoint vertices. Consecutive rounded checkpoints remain in the same covering face, so the verified face-covered-sequence theorem connects them while charging each finite face label at most once."),
    dict(label="feasible_active", name="Hirsch.face_interval_cover_route_bound_of_feasible_active_containment",
         short="face_interval_cover_route_bound_of_feasible_active_containment", wrapper=FEASIBLE_ACTIVE,
         title="Active-containment routing with nonvertex marked checkpoints",
         natural="If each valid repair interval stays inside its closed extreme face throughout the interval, the marked checkpoints may be nonvertices: only the two global endpoints must already be parent vertices, and a padded route exists with length at most the sum of the face budgets.",
         explanation="Active containment supplies all interval endpoint memberships and the start-containment incidences. Simultaneous face-preserving rounding converts every marked feasible checkpoint to a parent vertex without losing any face membership, after which the active/start-containment routing theorem gives the same total budget."),
]

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")

class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0
        self.opener = urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req = urllib.request.Request(BASE + "/agent/refresh", data=json.dumps({"api_key": self.key}).encode(), headers={"Content-Type":"application/json"}, method="POST")
        with self.opener.open(req, timeout=45) as r:
            d = json.load(r)
        self.token = d["access_token"]
        self.expires = float(d.get("expires_at", time.time() + 3500))
    def request(self, path: str, data=None, method="GET", content_type="application/json"):
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(BASE + path, data=body, headers={"Authorization":"Bearer " + self.token, "Content-Type":content_type}, method=method)
        with self.opener.open(req, timeout=90) as r:
            return json.load(r)
    def verify(self, tid: str, proof: str, explanation: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        parts=[]
        for name,value in [("theorem_id",tid),("proof_type","prove"),("explanation",explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n')
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request("/verify", "".join(parts).encode(), "POST", "multipart/form-data; boundary=" + boundary)

def norm(s):
    return re.sub(r"\s+", "", s or "")

def save(name, obj):
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(obj, indent=2) + "\n", encoding="utf-8")

def safe(name):
    return name.replace(".", "_")

def wait_job(api, jid, timeout=300):
    end=time.monotonic()+timeout
    while True:
        x=api.request("/publish-jobs/"+jid)
        if x.get("status") in {"PUBLISHED","FAILED","ERROR"}: return x
        if time.monotonic() >= end: raise TimeoutError("publication timeout")
        time.sleep(4)

def wait_verdict(api, sid, timeout=600):
    end=time.monotonic()+timeout
    terminal={"ACCEPTED","SKETCH_ACCEPTED","CE","WA","SORRY","FAILED","ERROR"}
    while True:
        x=api.request("/verify?"+urllib.parse.urlencode({"submission_id":sid}))
        if x.get("status") in terminal: return x
        if time.monotonic() >= end: raise TimeoutError("verification timeout")
        time.sleep(4)

def bundle(spec):
    wrapper=spec["wrapper"]
    first=next(line for line in wrapper.splitlines() if line.startswith("import Solutions."))
    target=first.split()[1]
    seen=set(); visiting=set(); imports=set(); pieces=[]
    def visit(module):
        if module in seen: return
        if module in visiting: raise RuntimeError("cycle: "+module)
        visiting.add(module)
        path=ROOT/(module.replace(".","/")+".lean")
        text=path.read_text(encoding="utf-8")
        body=[]
        for line in text.splitlines():
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith("Solutions."): visit(dep)
                    elif dep.startswith("Mathlib") or dep == "Definitions.Def_Hirsch_model": imports.add(dep)
                    else: raise RuntimeError(f"unexpected import {dep} in {module}")
            elif not line.startswith("#print axioms "):
                body.append(line)
        joined="\n".join(body)
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", joined, re.M):
            raise RuntimeError("forbidden proof construct: "+module)
        joined += "\nend\n" * len(re.findall(r"^noncomputable section\s*$", joined, re.M))
        pieces.append(f"-- BEGIN {path.relative_to(ROOT)}\n{joined}\n")
        visiting.remove(module); seen.add(module)
    visit(target)
    wrapper_body="\n".join(line for line in wrapper.splitlines() if not line.startswith("import ") and not line.startswith("#print axioms "))
    proof="\n".join("import "+x for x in sorted(imports)) + "\n\n" + "\n".join(pieces) + "\n" + wrapper_body + "\n#print axioms solution\n"
    packet=ROOT/("public_backlog_"+spec["label"])
    packet.mkdir(exist_ok=True)
    (packet/"solution.lean").write_text(proof, encoding="utf-8")
    return packet, proof

def formal(spec):
    text=spec["wrapper"]
    sig="theorem solution" + text.split("theorem solution",1)[1].split(" := by",1)[0]
    return "namespace Hirsch\n\n" + sig.replace("theorem solution", "theorem "+spec["short"],1) + " := by sorry\n\nend Hirsch"

def rows(api,name):
    q=urllib.parse.urlencode({"env":PIN,"theorem_name":name,"limit":20,"offset":0})
    return [x for x in api.request("/theorems?"+q).get("theorems",[]) if x.get("theorem_name")==name]

def publish(api,spec,proof):
    f=formal(spec); matches=rows(api,spec["name"])
    if matches:
        if len(matches)!=1: raise RuntimeError("theorem collision: "+spec["name"])
        th=api.request("/theorems/"+matches[0]["theorem_id"])
        if norm(th.get("formal_statement")) != norm(f): raise RuntimeError("existing theorem differs: "+spec["name"])
        tid=th["theorem_id"]
    else:
        q=api.request("/submit-problem", {"env":PIN,"private":False,"problems":[{
            "theorem_name":spec["name"],"theorem_title":spec["title"],"formal_statement":f,
            "natural_language_statement":spec["natural"],"preamble":PREAMBLE,
            "source":"Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.",
            "tags":["polyhedra","hirsch-conjecture","path-repair","extreme-faces"]}]}, "POST")
        save(safe(spec["name"])+"-queued.json",q)
        if q.get("errors") or len(q.get("jobs",[])) != 1: raise RuntimeError("problem did not queue: "+spec["name"])
        job=wait_job(api,q["jobs"][0]["job_id"]); save(safe(spec["name"])+"-job.json",job)
        if job.get("status") != "PUBLISHED": raise RuntimeError("problem publication failed: "+spec["name"])
        tid=job["theorem_id"]
    th=api.request("/theorems/"+tid)
    if th.get("status") == "Proved": return {"theorem_id":tid,"status":"Proved","verification":"SKIPPED_ALREADY_PROVED"}
    if th.get("status") != "Open": raise RuntimeError("unexpected status for "+spec["name"]+": "+str(th.get("status")))
    q=api.verify(tid,proof,spec["explanation"]); sid=q["submission_id"]; save(safe(spec["name"])+"-proof-queued.json",q)
    verdict=wait_verdict(api,sid); save(safe(spec["name"])+"-verdict.json",verdict)
    status=api.request("/theorems/"+tid).get("status")
    if verdict.get("status") != "ACCEPTED" or status != "Proved": raise RuntimeError(f"verification failed {spec['name']}: {verdict.get('status')} / {status}")
    return {"theorem_id":tid,"submission_id":sid,"verdict":"ACCEPTED","status":"Proved"}

def main():
    key=os.environ.get("PROVE2ME_API_KEY","").strip()
    if not key: raise RuntimeError("PROVE2ME_API_KEY unavailable")
    result={"started_at":dt.datetime.now(dt.timezone.utc).isoformat(),"source_commit":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),"results":{}}
    compiled={}
    for spec in SPECS:
        packet,proof=bundle(spec)
        log=packet/"lean.log"
        p=subprocess.run(["lake","env","lean",str(packet/"solution.lean")],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        log.write_text(p.stdout,encoding="utf-8")
        if p.returncode != 0: raise RuntimeError(f"standalone Lean failed for {spec['name']}\n"+p.stdout[-5000:])
        audit=subprocess.run(["python3","scripts/check_lean_axiom_log.py",str(log),"solution"],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (packet/"axiom-audit.log").write_text(audit.stdout,encoding="utf-8")
        if audit.returncode != 0: raise RuntimeError(f"axiom audit failed for {spec['name']}\n"+audit.stdout[-3000:])
        compiled[spec["name"]]={"proof":proof,"sha256":hashlib.sha256(proof.encode()).hexdigest()}
    api=API(key)
    for spec in SPECS:
        r=publish(api,spec,compiled[spec["name"]]["proof"])
        r["solution_sha256"]=compiled[spec["name"]]["sha256"]
        result["results"][spec["name"]]=r
        save("status.json",result)
    print(json.dumps(result,indent=2))
    return 0

if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as e:
        save("failure.json",{"error_type":type(e).__name__,"error":str(e)[:3000]})
        raise
