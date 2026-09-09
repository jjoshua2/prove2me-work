#!/usr/bin/env python3
from __future__ import annotations
import datetime, json, os, re, time, urllib.parse, urllib.request, uuid
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'public_common_face_publish_receipts'
BASE='https://prove2.me/api/v1'
PIN='c5ea00351c28e24afc9f0f84379aa41082b1188f'
DEF_NAME='Hirsch_common_face_geometry'
PREAMBLE='''import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch
'''
SPECS=[
  {
    'name':'Hirsch.common_face_dimension_tradeoff',
    'title':'Common-face dimensions overlap only through row excess',
    'proof':ROOT/'public_common_face_packet/tradeoff_solution.lean',
    'formal':r'''namespace Hirsch

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

end Hirsch''',
    'natural':'For separated extreme endpoints u and v of an n-row H-polytope in dimension d, and any intermediate extreme vertex x, the dimensions of the common-direction spaces determined by (u,x) and (v,x) sum to at most d+(n-2d). In the balanced case n=2d they sum to at most d.',
    'explanation':'Rows nonzero and tight at u and x define one common-direction kernel, and rows tight at v and x define the other. Their intersection can only vary through rows active at neither endpoint. Endpoint extremality and separation bound the number of those neutral rows by n-2d. The submodule dimension formula then gives the claimed sum bound.',
    'source':'Verified structural lemma from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #30.',
  },
  {
    'name':'Hirsch.common_face_effective_count_le_rows_minus_common',
    'title':'Common rows do not contribute effective common-face inequalities',
    'proof':ROOT/'public_common_face_packet/effective_count_solution.lean',
    'formal':r'''namespace Hirsch

theorem common_face_effective_count_le_rows_minus_common
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    HirschCommonFace.commonFaceEffectiveCount a b p q ≤
      n - (HirschCommonFace.commonSourceRows a b p q).card := by sorry

end Hirsch''',
    'natural':'Every nonzero row active at both defining points becomes a zero normal after restriction to their common-direction space. Therefore common rows and effective restricted rows are disjoint, and the effective row count is at most the total number of describing rows minus the number of common rows.',
    'explanation':'A common row annihilates the common-direction subspace by definition. In orthonormal coordinates its restricted normal therefore has zero self inner product and is zero. Thus common rows cannot belong to the effective-row set; finite-set cardinality gives effectiveCount <= n-commonRowCount.',
    'source':'Verified effective-row count lemma from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #33.',
  },
  {
    'name':'Hirsch.common_face_diameter_of_effective_rows',
    'title':'Transfer a balanced diameter theorem to a common face with few effective rows',
    'proof':ROOT/'public_common_face_packet/effective_diameter_solution.lean',
    'formal':r'''namespace Hirsch

theorem common_face_diameter_of_effective_rows
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : HirschCommonFace.commonFaceEffectiveCount a b u x ≤
      2 * HirschCommonFace.commonFaceDim a b u x)
    (hbalanced : ∀
      (a' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) →
        EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u x)))
      (b' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (HirschCommonFace.commonFaceA a b u x)
      (HirschCommonFace.commonFaceB a b u x)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x))) :
    DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B := by sorry

end Hirsch''',
    'natural':'If the canonical coordinate H-presentation of a common face has at most twice its dimension many nonzero restricted row normals, then any uniform diameter theorem for exactly balanced presentations of that dimension applies to the common face.',
    'explanation':'Delete exactly the zero restricted-normal inequalities; their right-hand sides are nonnegative because the source point is feasible, so they are tautologies. Enumerate the remaining effective rows and pad with 0<=1 tautologies up to exactly twice the common-face dimension. The resulting H-polytope is unchanged, so the supplied balanced diameter theorem transfers back.',
    'source':'Verified effective-row common-face model from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #28.',
  },
]

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
def safe_name(name): return name.replace('.','_')
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

def publish_theorem(api,spec):
    name=spec['name']; matches=rows(api,name)
    if matches:
        if len(matches)!=1: raise RuntimeError('theorem collision: '+name)
        th=api.request('/theorems/'+matches[0]['theorem_id'])
        if norm(th.get('formal_statement'))!=norm(spec['formal']): raise RuntimeError('existing theorem differs: '+name)
        tid=th['theorem_id']
    else:
        q=api.request('/submit-problem',{'env':PIN,'private':False,'problems':[{
          'theorem_name':name,'theorem_title':spec['title'],'formal_statement':spec['formal'],
          'natural_language_statement':spec['natural'],'preamble':PREAMBLE,'source':spec['source'],
          'tags':['hirsch-conjecture','polyhedra','faces','linear-algebra']}]},'POST')
        save(safe_name(name)+'-queued.json',q)
        if q.get('errors') or len(q.get('jobs',[]))!=1: raise RuntimeError('theorem did not queue: '+name)
        job=wait_job(api,q['jobs'][0]['job_id']); save(safe_name(name)+'-job.json',job)
        if job.get('status')!='PUBLISHED': raise RuntimeError('theorem publication failed: '+name)
        tid=job['theorem_id']
    th=api.request('/theorems/'+tid)
    if th.get('status')=='Proved': return {'theorem_id':tid,'status':'Proved','skipped':True}
    if th.get('status')!='Open': raise RuntimeError('unexpected theorem status: '+name)
    q=api.verify(tid,spec['proof'].read_text(),spec['explanation']); sid=q['submission_id']; save(safe_name(name)+'-proof-queued.json',q)
    verdict=wait_verdict(api,sid); save(safe_name(name)+'-proof-verdict.json',verdict)
    status=api.request('/theorems/'+tid).get('status')
    if verdict.get('status')!='ACCEPTED' or status!='Proved': raise RuntimeError(f'verification failed {name}: {verdict.get("status")} / {status}')
    return {'theorem_id':tid,'submission_id':sid,'verdict':'ACCEPTED','status':'Proved'}

def main():
    key=os.environ.get('PROVE2ME_API_KEY','').strip()
    if not key: raise RuntimeError('PROVE2ME_API_KEY unavailable')
    api=API(key); result={'started_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'env':PIN,'results':{}}
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
          'definition_title':'Common-face direction and coordinate geometry',
          'definition':definition,
          'natural_language_statement':'Public definitions for common active rows, endpoint-neutral rows, common-direction kernels and dimensions, canonical common-face coordinates, effective restricted rows, and sparse subpresentations.',
          'source':'Formalization infrastructure developed for the Polynomial Hirsch mission; definitions are standard finite-dimensional H-polytope linear algebra.',
          'tags':['hirsch-conjecture','polyhedra','faces','linear-algebra'],
          'env':PIN,'private':False},'POST')
        save('definition-queued.json',q); jid=q.get('job_id') or (q.get('jobs') or [{}])[0].get('job_id')
        if not jid: raise RuntimeError('definition did not queue')
        job=wait_job(api,jid); save('definition-job.json',job)
        if job.get('status')!='PUBLISHED': raise RuntimeError('definition publication failed')
        did=job['theorem_id']
    result['definition_id']=did
    for spec in SPECS:
        result['results'][spec['name']]=publish_theorem(api,spec)
        save('status.json',result)
    print(json.dumps(result,indent=2)); return 0

if __name__=='__main__':
    try: raise SystemExit(main())
    except Exception as e:
        OUT.mkdir(exist_ok=True); save('failure.json',{'error_type':type(e).__name__,'error':str(e)[:700]}); raise
