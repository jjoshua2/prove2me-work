#!/usr/bin/env python3
"""Publish the immutable, independently compiled bounded clipping proof.

The script accepts only the artifact from GitHub Actions run 34485975796,
validates source/run/proof hashes and the successful standalone-audit manifest,
then collision-safely registers/verifies the public theorem on Prove2Me.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.parse
import urllib.request
import uuid

BASE = "https://prove2.me/api/v1"
PIN = "c5ea00351c28e24afc9f0f84379aa41082b1188f"
SOURCE_COMMIT = "446304d56513437aad9c0a02fc1d202e41783259"
SOURCE_RUN = "34485975796"
EXPECTED_SOLUTION_SHA256 = "fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f"
NAME = "Hirsch.simultaneous_clipping_diameter_of_compact_outer"
SHORT_NAME = "simultaneous_clipping_diameter_of_compact_outer"

PREAMBLE = """import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch
"""
TITLE = "Simultaneous clipping diameter from final cut-face budgets"
NATURAL = (
    "Let Q be a compact convex set in finite-dimensional Euclidean space with padded graph "
    "diameter at most D. Intersect Q simultaneously with a finite family of halfspaces. If, "
    "for every added inequality i, the corresponding exposed face of the final intersection "
    "has intrinsic padded graph diameter at most B_i, then the final intersection has padded "
    "graph diameter at most D + sum_i B_i. The endpoints may be vertices created by the cuts. "
    "The face budgets are for the final intersection, not for intermediate one-cut polytopes."
)
EXPLANATION = (
    "The proof uses one fixed simultaneous radial retraction into the final clipped set. New "
    "final vertices attach to suitable outer vertices through traces supported by the same final "
    "cut-face family. An outer D-step edge/stay route is retracted as well; portions not on final "
    "cut faces lie in clipped old edges of intrinsic cost at most one. A finite closed-face cover "
    "of the connected retracted trace yields a route through actual parent-vertex portals, so each "
    "final cut face is charged at most once. A strict common centre is either constructed, or a "
    "universally tight cut face already equals the final set and directly supplies the bound."
)
TAGS = ["polyhedra", "hirsch-conjecture", "graph-diameter", "clipping", "path-repair"]

FORMAL = r"""namespace Hirsch

theorem simultaneous_clipping_diameter_of_compact_outer
    {d : ℕ} {ι : Type*} [Fintype ι]
    (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hQc : IsCompact Q) (hQ : Convex ℝ Q)
    (a : ι → EuclideanSpace ℝ (Fin d)) (b : ι → ℝ)
    (D : ℕ) (B : ι → ℕ) (hD : DiamLE Q D)
    (hFaces : ∀ i,
      DiamLE ((Q ∩ {x | ∀ j, ⟪a j, x⟫ ≤ b j}) ∩ {z | ⟪a i, z⟫ = b i}) (B i)) :
    DiamLE (Q ∩ {x | ∀ i, ⟪a i, x⟫ ≤ b i}) (D + ∑ i, B i) := by sorry

end Hirsch"""


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError("authenticated redirects disabled")


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ""
        self.expires = 0.0
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self) -> None:
        req = urllib.request.Request(
            BASE + "/agent/refresh",
            data=json.dumps({"api_key": self.key}).encode(),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        with self.opener.open(req, timeout=45) as r:
            data = json.load(r)
        if data.get("version") != "0.9.9":
            raise RuntimeError("unexpected Prove2Me version: " + str(data.get("version")))
        self.token = data["access_token"]
        self.expires = float(data.get("expires_at", time.time() + 3500))

    def request(self, path: str, data=None, method: str = "GET", content_type: str = "application/json"):
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path,
            data=body,
            headers={"Authorization": "Bearer " + self.token, "Content-Type": content_type},
            method=method,
        )
        with self.opener.open(req, timeout=90) as r:
            return json.load(r)

    def verify(self, theorem_id: str, proof: str):
        boundary = "----Prove2Me" + uuid.uuid4().hex
        chunks=[]
        for key,value in [("theorem_id",theorem_id),("proof_type","prove"),("explanation",EXPLANATION)]:
            chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{key}"\r\n\r\n{value}\r\n')
        chunks.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
            f'Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n'
        )
        return self.request("/verify", "".join(chunks).encode(), "POST", "multipart/form-data; boundary=" + boundary)


def norm(s: str | None) -> str:
    return re.sub(r"\s+", "", s or "")


def save(out: Path, name: str, data) -> None:
    out.mkdir(parents=True, exist_ok=True)
    (out/name).write_text(json.dumps(data, indent=2, sort_keys=True)+"\n", encoding="utf-8")


def locate(root: Path, name: str) -> Path:
    hits=list(root.rglob(name))
    if len(hits)!=1:
        raise RuntimeError(f"expected exactly one {name}, found {len(hits)}")
    return hits[0]


def validate(root: Path) -> tuple[dict,str]:
    mp=locate(root,"bounded-manifest.json")
    sp=locate(root,"bounded-solution.lean")
    manifest=json.loads(mp.read_text(encoding="utf-8"))
    proof=sp.read_text(encoding="utf-8")
    digest=hashlib.sha256(proof.encode()).hexdigest()
    expected={
        "status": "SOURCE_ADAPTER_AND_STANDALONE_COMPILED_AND_AUDITED",
        "source_commit": SOURCE_COMMIT,
        "actions_run_id": SOURCE_RUN,
        "solution_sha256": EXPECTED_SOLUTION_SHA256,
    }
    for k,v in expected.items():
        if str(manifest.get(k)) != v:
            raise RuntimeError(f"artifact mismatch for {k}: {manifest.get(k)!r}")
    if digest != EXPECTED_SOLUTION_SHA256:
        raise RuntimeError("verified proof hash mismatch")
    if re.search(r"\b(sorry|admit|native_decide)\b|^\s*(axiom|opaque)\s", proof, re.M):
        raise RuntimeError("verified proof contains forbidden unchecked declaration")
    log=locate(root,"standalone.log").read_text(encoding="utf-8")
    if "'solution' depends on axioms: [propext, Classical.choice, Quot.sound]" not in log:
        raise RuntimeError("standalone axiom receipt does not match expected standard axioms")
    return manifest, proof


def theorem_rows(api: API):
    qs=urllib.parse.urlencode({"env":PIN,"theorem_name":NAME,"limit":20,"offset":0})
    return [r for r in api.request("/theorems?"+qs).get("theorems",[]) if r.get("theorem_name")==NAME]


def poll_publish(api:API, job_id:str, timeout=240):
    end=time.monotonic()+timeout
    while time.monotonic()<end:
        x=api.request("/publish-jobs/"+job_id)
        if x.get("status") in {"PUBLISHED","FAILED","ERROR"}: return x
        time.sleep(4)
    raise TimeoutError("publication job timed out")


def poll_verify(api:API, sid:str, timeout=600):
    end=time.monotonic()+timeout
    terminal={"ACCEPTED","SKETCH_ACCEPTED","CE","WA","SORRY","FAILED","ERROR"}
    while time.monotonic()<end:
        x=api.request("/verify?"+urllib.parse.urlencode({"submission_id":sid}))
        if x.get("status") in terminal: return x
        time.sleep(4)
    raise TimeoutError("proof verification timed out")


def main() -> int:
    p=argparse.ArgumentParser(); p.add_argument("--artifact-root",type=Path,required=True); p.add_argument("--out",type=Path,default=Path("prove2me_bounded_clipping_receipts")); args=p.parse_args()
    key=os.environ.get("PROVE2ME_API_KEY","").strip()
    if not key: raise RuntimeError("PROVE2ME_API_KEY unavailable")
    manifest,proof=validate(args.artifact_root)
    out=args.out
    summary={"started_at":dt.datetime.now(dt.timezone.utc).isoformat(),"source_commit":SOURCE_COMMIT,"source_run":SOURCE_RUN,"solution_sha256":EXPECTED_SOLUTION_SHA256,"theorem_name":NAME,"artifact_validation":"PASSED"}
    save(out,"validated-artifact.json",manifest)
    api=API(key)
    rows=theorem_rows(api)
    if rows:
        if len(rows)!=1: raise RuntimeError(f"theorem-name collision: {len(rows)} rows")
        theorem=api.request("/theorems/"+rows[0]["theorem_id"])
        if norm(theorem.get("formal_statement")) != norm(FORMAL): raise RuntimeError("existing theorem name has different formal statement")
        tid=theorem["theorem_id"]; summary["registration"]="REUSED"
    else:
        queued=api.request("/submit-problem",{"env":PIN,"private":False,"problems":[{"theorem_name":NAME,"theorem_title":TITLE,"formal_statement":FORMAL,"natural_language_statement":NATURAL,"preamble":PREAMBLE,"source":"Kernel- and standalone-verified proof from jjoshua2/prove2me-work PR #53 commit "+SOURCE_COMMIT+", Actions run "+SOURCE_RUN+".","tags":TAGS}]},"POST")
        save(out,"problem-queued.json",queued)
        if queued.get("errors") or len(queued.get("jobs",[]))!=1: raise RuntimeError("problem publication did not queue exactly one job")
        job=poll_publish(api,queued["jobs"][0]["job_id"]); save(out,"problem-job.json",job)
        if job.get("status")!="PUBLISHED": raise RuntimeError("problem publication failed: "+str(job.get("status")))
        tid=job["theorem_id"]; summary["registration"]="PUBLISHED"
    summary["theorem_id"]=tid
    theorem=api.request("/theorems/"+tid); save(out,"theorem-before-verify.json",theorem)
    if theorem.get("status")=="Proved":
        summary.update(status="Proved",verification="SKIPPED_ALREADY_PROVED"); save(out,"status.json",summary); print(json.dumps(summary,indent=2)); return 0
    if theorem.get("status")!="Open": raise RuntimeError("unexpected theorem status: "+str(theorem.get("status")))
    queued=api.verify(tid,proof); save(out,"proof-queued.json",queued)
    sid=queued.get("submission_id")
    if not sid: raise RuntimeError("verification did not return submission_id")
    summary["submission_id"]=sid
    verdict=poll_verify(api,sid); save(out,"proof-verdict.json",verdict)
    final=api.request("/theorems/"+tid); save(out,"theorem-final.json",final)
    summary.update(verdict=verdict.get("status"),status=final.get("status")); save(out,"status.json",summary); print(json.dumps(summary,indent=2))
    if summary["verdict"]!="ACCEPTED" or summary["status"]!="Proved": raise RuntimeError("Prove2Me did not accept bounded clipping proof")
    return 0

if __name__=="__main__":
    try: raise SystemExit(main())
    except Exception as exc:
        save(Path("prove2me_bounded_clipping_receipts"),"failure.json",{"error_type":type(exc).__name__,"error":str(exc)[:1200]})
        raise
