#!/usr/bin/env python3
from __future__ import annotations
import datetime, json, os, re, time, urllib.parse, urllib.request, uuid
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'public_geodesic_face_cover_receipts'
BASE='https://prove2.me/api/v1'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
NAME='Hirsch.geodesic_face_cover_diameter_bound'
PREAMBLE='''import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace BigOperators
open Set Hirsch
attribute [local instance] Classical.propDecidable
'''
FORMAL=r'''namespace Hirsch

theorem geodesic_face_cover_diameter_bound
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by sorry

end Hirsch'''

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): raise RuntimeError('authenticated redirects disabled')
class API:
    def __init__(self,key): self.key=key; self.token=''; self.expires=0.; self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+'/agent/refresh',data=json.dumps({'api_key':self.key}).encode(),headers={'Content-Type':'application/json'},method='POST')
        with self.opener.open(req,timeout=45) as r: d=json.load(r)
        self.token=d['access_token']; self.expires=float(d.get('expires_at',time.time()+3500))
    def request(self,path,data=None,method='GET',content_type='application/json'):
        if not self.token or time.time()+60>=self.expires: self.refresh()
        body=json.dumps(data).encode() if data is not None and not isinstance(data,bytes) else data
        req=urllib.request.Request(BASE+path,data=body,headers={'Authorization':'Bearer '+self.token,'Content-Type':content_type},method=method)
        with self.opener.open(req,timeout=90) as r: return json.load(r)
    def verify(self,tid,proof,explanation):
        boundary='----Prove2Me'+uuid.uuid4().hex; parts=[]
        for name,value in [('theorem_id',tid),('proof_type','prove'),('explanation',explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n')
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request('/verify',''.join(parts).encode(),'POST','multipart/form-data; boundary='+boundary)

def norm(s): return re.sub(r'\s+','',s or '')
def save(name,obj): OUT.mkdir(exist_ok=True); (OUT/name).write_text(json.dumps(obj,indent=2)+"\n")
def rows(api):
    q=urllib.parse.urlencode({'env':PIN,'theorem_name':NAME,'limit':20,'offset':0})
    return [x for x in api.request('/theorems?'+q).get('theorems',[]) if x.get('theorem_name')==NAME]
def wait_job(api,jid,timeout=420):
    end=time.monotonic()+timeout
    while True:
        x=api.request('/publish-jobs/'+jid)
        if x.get('status') in {'PUBLISHED','FAILED','ERROR'} or time.monotonic()>end: return x
        time.sleep(6)
def wait_verdict(api,sid,timeout=600):
    end=time.monotonic()+timeout; terminal={'ACCEPTED','SKETCH_ACCEPTED','CE','WA','SORRY','FAILED','ERROR'}
    while True:
        x=api.request('/verify?'+urllib.parse.urlencode({'submission_id':sid}))
        if x.get('status') in terminal or time.monotonic()>end: return x
        time.sleep(6)

def main():
    key=os.environ.get('PROVE2ME_API_KEY','').strip()
    if not key: raise RuntimeError('PROVE2ME_API_KEY unavailable')
    api=API(key); result={'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'env':PIN}
    matches=rows(api)
    if matches:
        if len(matches)!=1: raise RuntimeError('theorem name collision')
        th=api.request('/theorems/'+matches[0]['theorem_id'])
        if norm(th.get('formal_statement'))!=norm(FORMAL): raise RuntimeError('existing theorem differs')
        tid=th['theorem_id']
    else:
        q=api.request('/submit-problem',{'env':PIN,'private':False,'problems':[{
          'theorem_name':NAME,
          'theorem_title':'Extreme-face incidence cover bounds parent graph diameter',
          'formal_statement':FORMAL,
          'natural_language_statement':'Let a connected vertex graph be covered by a finite family of extreme faces. If each vertex lies in at least q>0 selected faces and selected face i has intrinsic graph diameter at most B_i, then the parent padded diameter is at most (sum_i(B_i+1))/q - 1. The proof counts visits of a shortest path to faces and remains valid when the path leaves and later re-enters a face.',
          'preamble':PREAMBLE,
          'source':'Verified graph-geometry theorem from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #27.',
          'tags':['polyhedra','graph-diameter','hirsch-conjecture','extreme-faces']}]},'POST')
        save('problem-queued.json',q)
        if q.get('errors') or len(q.get('jobs',[]))!=1: raise RuntimeError('publication did not queue')
        job=wait_job(api,q['jobs'][0]['job_id']); save('problem-job.json',job)
        if job.get('status')!='PUBLISHED': raise RuntimeError('problem publication failed')
        tid=job['theorem_id']
    result['theorem_id']=tid
    th=api.request('/theorems/'+tid)
    if th.get('status')=='Proved': result.update(status='Proved',skipped=True); save('status.json',result); print(json.dumps(result,indent=2)); return 0
    if th.get('status')!='Open': raise RuntimeError('unexpected theorem status')
    proof=(ROOT/'public_geodesic_face_cover_packet/solution.lean').read_text()
    explanation='Choose a shortest padded parent walk. Reentry splicing through an extreme face shows that visits to face i occupy at most B_i+1 indices. Double-count path-index/face incidences: every path index contributes at least q incidences, while face i contributes at most B_i+1. Therefore q(L+1) <= sum_i(B_i+1). Divide by q, subtract one, and pad the shortest walk to the stated diameter budget.'
    q=api.verify(tid,proof,explanation); sid=q['submission_id']; result['submission_id']=sid; save('proof-queued.json',q)
    verdict=wait_verdict(api,sid); save('proof-verdict.json',verdict)
    result['verdict']=verdict.get('status'); result['status']=api.request('/theorems/'+tid).get('status'); save('status.json',result); print(json.dumps(result,indent=2))
    if result['verdict']!='ACCEPTED' or result['status']!='Proved': raise RuntimeError('verification failed')
    return 0

if __name__=='__main__':
    try: raise SystemExit(main())
    except Exception as e:
        OUT.mkdir(exist_ok=True); save('failure.json',{'error_type':type(e).__name__,'error':str(e)[:700]}); raise
