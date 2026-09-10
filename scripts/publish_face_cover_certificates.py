#!/usr/bin/env python3
"""Idempotently publish and verify four completely audited, independent lemmas.

Uses the repository's explicit Prove2Me permission. Never edits the mission's
Open dependency graph; no conjectural children, inferred verdicts, or secrets
in artifacts. Credentials are sent only to the fixed API base, without redirects.
"""
from __future__ import annotations
import argparse, datetime, hashlib, json, os, re, time, urllib.error, urllib.parse, urllib.request, uuid
from pathlib import Path
from build_face_cover_publication import SOURCE, SOURCE_RUN, PIN, LEAN, check_proof

BASE='https://prove2.me/api/v1'
EXPECTED_VERSION='0.9.9'
FRONTIER='099c6686-560c-48fc-b2c2-18b6a620a06e'
ALLOWED={'propext','Classical.choice','Quot.sound'}

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs):raise RuntimeError('authenticated redirects disabled')

class API:
    def __init__(self,key):
        self.key=key;self.token='';self.expires=0;self.version=None
        self.opener=urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req=urllib.request.Request(BASE+'/agent/refresh',data=json.dumps({'api_key':self.key}).encode(),
           headers={'Content-Type':'application/json','Accept':'application/json'},method='POST')
        with self.opener.open(req,timeout=45) as response:data=json.load(response)
        self.token=data['access_token'];self.expires=float(data.get('expires_at',time.time()+3500));self.version=data.get('version')
        if self.version!=EXPECTED_VERSION:raise RuntimeError('API version differs from reviewed 0.9.9 contract')
    def request(self,path,data=None,method='GET',content_type='application/json'):
        if not path.startswith('/') or path.startswith('//') or '://' in path:raise ValueError('API-relative path required')
        if not self.token or time.time()+60>=self.expires:self.refresh()
        body=json.dumps(data).encode() if data is not None and not isinstance(data,bytes) else data
        req=urllib.request.Request(BASE+path,data=body,headers={'Authorization':'Bearer '+self.token,
             'Content-Type':content_type,'Accept':'application/json'},method=method)
        with self.opener.open(req,timeout=90) as response:return json.load(response)
    def verify(self,tid,proof,explanation):
        boundary='----Prove2Me'+uuid.uuid4().hex;parts=[]
        for name,val in [('theorem_id',tid),('proof_type','prove'),('explanation',explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{val}\r\n')
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request('/verify',''.join(parts).encode(),'POST','multipart/form-data; boundary='+boundary)


def save(out,name,obj):
    out.mkdir(parents=True,exist_ok=True);(out/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def norm(t):return re.sub(r'\s+','',t or '')
def summary(t):return {k:t.get(k) for k in ('theorem_id','theorem_name','status','mathlib_rev')}

def poll(api,path,terminal,out,filename,seconds=600):
    deadline=time.monotonic()+seconds
    while True:
        data=api.request(path);save(out,filename,data)
        if data.get('status') in terminal:return data
        if time.monotonic()>deadline:raise TimeoutError('Pending platform job; identifiers retained in receipts')
        time.sleep(5)

def checked_packet(packet):
    man=json.loads((packet/'manifest.json').read_text());ver=json.loads((packet/'verification.json').read_text())
    if (man['source_commit'],man['source_run'],man['mathlib_rev'],man['lean_toolchain'])!=(SOURCE,SOURCE_RUN,PIN,LEAN):raise ValueError('wrong source/pin')
    if ver['status']!='PASSED' or ver['manifest_sha256']!=digest(packet/'manifest.json'):raise ValueError('missing or stale final verification')
    if ver['source_commit']!=SOURCE or ver['mathlib_rev']!=PIN:raise ValueError('wrong verification pin')
    indexed={r['name']:r for r in ver['entries']}
    if len(indexed)!=4 or len(man['entries'])!=4:raise ValueError('expected exactly four independent declarations')
    for entry in man['entries']:
        r=indexed[entry['name']];p=packet/(entry['key']+'.lean');s=packet/(entry['key']+'.statement.lean')
        if digest(p)!=r['solution_sha256'] or digest(p)!=entry['solution_sha256']:raise ValueError('proof changed after verification')
        if digest(s)!=r['statement_sha256'] or digest(s)!=entry['statement_sha256']:raise ValueError('statement changed after verification')
        if r['standalone_compilation']!='PASSED' or set(r['axioms'])-ALLOWED:raise ValueError('invalid axiom audit')
        check_proof(p.read_text())
        if entry['name'] in p.read_text():raise ValueError('proof unexpectedly mentions its public target')
    return man

def get_existing(api,name):
    q=urllib.parse.urlencode({'env':PIN,'theorem_name':name,'limit':50,'offset':0})
    found=[r for r in api.request('/theorems?'+q).get('theorems',[]) if r.get('theorem_name')==name]
    if len(found)>1:raise ValueError('ambiguous pinned theorem name')
    return api.request('/theorems/'+found[0]['theorem_id']) if found else None

def process(api,entry,packet,out):
    out=out/entry['key'];out.mkdir(parents=True,exist_ok=True)
    theorem=get_existing(api,entry['name'])
    registration='REUSED' if theorem else 'PUBLISHED'
    if theorem is None:
        payload={'env':PIN,'private':False,'problems':[{
            'theorem_name':entry['name'],'theorem_title':entry['title'],
            'formal_statement':entry['formal_statement'],'preamble':entry['preamble'],
            'natural_language_statement':entry['natural'],
            'source':f'https://github.com/jjoshua2/prove2me-work/blob/{SOURCE}/{entry["root"].replace(".","/")}.lean ; declaration {entry["checked"]}; pinned CI run {SOURCE_RUN}.',
            'tags':['polyhedra','graph-diameter','formalization','face-cover']} ]}
        save(out,'registration-request.json',payload)
        queued=api.request('/submit-problem',payload,'POST');save(out,'registration-queued.json',queued)
        if queued.get('errors') or len(queued.get('jobs',[]))!=1:raise RuntimeError('registration did not queue one job')
        job=poll(api,'/publish-jobs/'+queued['jobs'][0]['job_id'],{'PUBLISHED','FAILED','ERROR'},out,'registration-verdict.json')
        if job.get('status')!='PUBLISHED':raise RuntimeError('statement registration failed; see receipt')
        theorem=api.request('/theorems/'+job['theorem_id'])
    save(out,'theorem-before.json',theorem)
    if theorem.get('mathlib_rev')!=PIN or norm(theorem.get('formal_statement'))!=norm(entry['formal_statement']):raise ValueError('existing/live theorem type or pin mismatch')
    record={'name':entry['name'],'theorem_id':theorem['theorem_id'],'registration':registration,
        'solution_sha256':entry['solution_sha256']}
    if theorem.get('status')=='Proved':
        record.update(verdict='ALREADY_PROVED',status='Proved');save(out,'result.json',record);return record
    if theorem.get('status')!='Open':raise ValueError('unexpected theorem status')
    queued=api.verify(theorem['theorem_id'],(packet/(entry['key']+'.lean')).read_text(),entry['explanation'])
    save(out,'proof-queued.json',queued);sid=queued['submission_id']
    verdict=poll(api,'/verify?'+urllib.parse.urlencode({'submission_id':sid}),
        {'ACCEPTED','SKETCH_ACCEPTED','CE','WA','SORRY','FAILED','ERROR'},out,'proof-verdict.json',900)
    final=api.request('/theorems/'+theorem['theorem_id']);save(out,'theorem-final.json',final)
    record.update(submission_id=sid,verdict=verdict.get('status'),status=final.get('status'));save(out,'result.json',record)
    if record['verdict']!='ACCEPTED' or record['status']!='Proved':raise RuntimeError('proof did not receive ACCEPTED and Proved')
    return record

def main():
    p=argparse.ArgumentParser();p.add_argument('--packet',type=Path,default=Path('face_cover_publication_packet'));p.add_argument('--out',type=Path,default=Path('face_cover_publication_receipts'));a=p.parse_args()
    manifest=checked_packet(a.packet);key=os.environ.get('PROVE2ME_API_KEY','').strip()
    if not key:raise RuntimeError('repository publication credential is not present')
    api=API(key);envs=api.request('/environments');save(a.out,'environments.json',envs)
    if not any(e.get('mathlib_rev')==PIN for e in envs.get('environments',[])):raise ValueError('pinned environment unavailable')
    before=api.request('/theorems/'+FRONTIER);save(a.out,'frontier-before.json',summary(before))
    results=[]
    for entry in manifest['entries']:
        record=process(api,entry,a.packet,a.out);results.append(record)
        save(a.out,'progress.json',results);print(json.dumps(record),flush=True)
    after=api.request('/theorems/'+FRONTIER);save(a.out,'frontier-after.json',summary(after))
    result={'source_commit':SOURCE,'source_run':SOURCE_RUN,'platform_version':api.version,'entries':results,
       'frontier_before':summary(before),'frontier_after':summary(after),
       'checked_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'new_conjectural_children':0,'frontier_graph_modified':False}
    save(a.out,'result.json',result);print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    try:main()
    except Exception as exc:
        # Never print request headers, credentials, or authentication response bodies.
        detail={'type':type(exc).__name__,'message':str(exc)[:500]}
        save(Path('face_cover_publication_receipts'),'failure.json',detail)
        print(json.dumps(detail),flush=True);raise SystemExit(2)
