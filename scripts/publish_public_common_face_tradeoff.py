#!/usr/bin/env python3
from __future__ import annotations
import datetime, json, os, re, time, urllib.parse, urllib.request, uuid
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'public_common_face_publish_receipts'
BASE='https://prove2.me/api/v1'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
DEF_NAME='Hirsch_common_face_geometry'
THEOREM_NAME='Hirsch.common_face_dimension_tradeoff'
PREAMBLE='''import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch
'''
FORMAL=r'''namespace Hirsch

theorem common_face_dimension_tradeoff
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    HirschCommonFace.commonFaceDim a b u x +
      HirschCommonFace.commonFaceDim a b v x ≤ d + (n - 2 * d) := by sorry

end Hirsch'''
EXPLANATION='''Rows nonzero and tight at u and x define one common-direction kernel, and rows tight at v and x define the other. Their intersection can only vary through rows active at neither endpoint. Endpoint extremality and separation bound the number of those neutral rows by n-2d. The submodule dimension formula then gives dim F(u,x)+dim F(v,x) <= d+(n-2d). At exact balance n=2d the two dimensions sum to at most d.'''

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): raise RuntimeError('authenticated redirects disabled')
class API:
    def __init__(self,key): self.key=key; self.token=''; self.expires=0.; self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+'/agent/refresh',data=json.dumps({'api_key':self.key}).encode(),headers={'Content-Type':'application/json'},method='POST')
        with self.opener.open(req,timeout=45) as r: d=json.load(r)
        self.token=d['access_token']; self.expires=float(d.get('expires_at',time.time()+3500)); self.version=d.get('version')
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
def rows(api,name):
    q=urllib.parse.urlencode({'env':PIN,'theorem_name':name,'limit':20,'offset':0}); return [x for x in api.request('/theorems?'+q).get('theorems',[]) if x.get('theorem_name')==name]
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
    definition=(ROOT/'Definitions/Def_Hirsch_common_face_geometry.lean').read_text()
    defs=rows(api,DEF_NAME)
    if defs:
        if len(defs)!=1 or defs[0].get('status')!='Definition': raise RuntimeError('definition collision')
        full=api.request('/theorems/'+defs[0]['theorem_id']); server=full.get('definition') or full.get('definitions') or full.get('formal_statement') or ''
        if norm(server)!=norm(definition): raise RuntimeError('existing definition differs')
        did=full['theorem_id']
    else:
        q=api.request('/submit-definition',{
          'definition_name':DEF_NAME,
          'definition_title':'Minimal common-face direction geometry',
          'definition':definition,
          'natural_language_statement':'Definitions for rows active at both points, endpoint-neutral rows, finite row evaluation, their common-direction kernel, and its finite dimension. These are the minimal public vocabulary for structural Polynomial Hirsch face lemmas.',
          'source':'Formalization infrastructure developed for the Polynomial Hirsch mission; definitions are standard finite-dimensional H-polytope linear algebra.',
          'tags':['hirsch-conjecture','polyhedra','faces','linear-algebra'],
          'env':PIN,'private':False},'POST')
        save('definition-queued.json',q); jid=q.get('job_id') or (q.get('jobs') or [{}])[0].get('job_id')
        if not jid: raise RuntimeError('definition did not queue')
        job=wait_job(api,jid); save('definition-job.json',job)
        if job.get('status')!='PUBLISHED': raise RuntimeError('definition publication failed')
        did=job['theorem_id']
    result['definition_id']=did
    matches=rows(api,THEOREM_NAME)
    if matches:
        if len(matches)!=1: raise RuntimeError('theorem collision')
        th=api.request('/theorems/'+matches[0]['theorem_id'])
        if norm(th.get('formal_statement'))!=norm(FORMAL): raise RuntimeError('existing theorem differs')
        tid=th['theorem_id']
    else:
        q=api.request('/submit-problem',{'env':PIN,'private':False,'problems':[{
          'theorem_name':THEOREM_NAME,
          'theorem_title':'Common-face dimensions overlap only through row excess',
          'formal_statement':FORMAL,
          'natural_language_statement':'For separated extreme endpoints u and v of an n-row H-polytope in dimension d, and any intermediate extreme vertex x, the dimensions of the common-direction spaces determined by (u,x) and (v,x) sum to at most d+(n-2d). In the balanced case n=2d they sum to at most d.',
          'preamble':PREAMBLE,
          'source':'Verified structural lemma from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #30.',
          'tags':['hirsch-conjecture','polyhedra','faces','dimension']}]},'POST')
        save('theorem-queued.json',q)
        if q.get('errors') or len(q.get('jobs',[]))!=1: raise RuntimeError('theorem did not queue')
        job=wait_job(api,q['jobs'][0]['job_id']); save('theorem-job.json',job)
        if job.get('status')!='PUBLISHED': raise RuntimeError('theorem publication failed')
        tid=job['theorem_id']
    result['theorem_id']=tid
    th=api.request('/theorems/'+tid)
    if th.get('status')=='Proved': result.update(status='Proved',skipped=True); save('status.json',result); print(json.dumps(result,indent=2)); return 0
    if th.get('status')!='Open': raise RuntimeError('unexpected theorem status')
    proof=(ROOT/'public_common_face_packet/solution.lean').read_text()
    q=api.verify(tid,proof,EXPLANATION); sid=q['submission_id']; result['submission_id']=sid; save('proof-queued.json',q)
    verdict=wait_verdict(api,sid); save('proof-verdict.json',verdict)
    result['verdict']=verdict.get('status'); result['status']=api.request('/theorems/'+tid).get('status'); save('status.json',result); print(json.dumps(result,indent=2))
    if result['verdict']!='ACCEPTED' or result['status']!='Proved': raise RuntimeError('verification failed')
    return 0

if __name__=='__main__':
    try: raise SystemExit(main())
    except Exception as e:
        OUT.mkdir(exist_ok=True); save('failure.json',{'error_type':type(e).__name__,'error':str(e)[:700]}); raise
