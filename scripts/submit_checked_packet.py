#!/usr/bin/env python3
"""Compile, authenticate, search, and explicitly publish/verify a proof packet.

Credentials are read from PROVE2ME_API_KEY or a gitignored credentials.json.
They are never written into the packet, Git, URLs, logs, or API reports.
"""
from __future__ import annotations
import argparse, hashlib, json, os, pathlib, re, subprocess, time, urllib.error, urllib.parse, urllib.request, uuid
BASE = 'https://prove2.me/api/v1'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
LEAF = '33fc334e-e05b-4090-ac49-f83fd94d9305'

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise RuntimeError('Refusing to redirect an authenticated API request')

class API:
    def __init__(self, key: str):
        self.key, self.token = key, ''
        self.opener = urllib.request.build_opener(NoRedirect)
        self.refresh()
    def refresh(self):
        req=urllib.request.Request(BASE+'/agent/refresh', data=json.dumps({'api_key':self.key}).encode(), headers={'Content-Type':'application/json'}, method='POST')
        with self.opener.open(req,timeout=45) as response:
            body=json.load(response)
        self.token=body['access_token']
        self.version=body.get('version')
    def call(self, path: str, method='GET', payload=None, data=None, content_type=None):
        if not path.startswith('/') or '://' in path:raise ValueError('Invalid API path')
        if payload is not None:
            data=json.dumps(payload).encode();content_type='application/json'
        for attempt in range(2):
            headers={'Authorization':'Bearer '+self.token}
            if content_type:headers['Content-Type']=content_type
            req=urllib.request.Request(BASE+path,data=data,headers=headers,method=method)
            try:
                with self.opener.open(req,timeout=60) as response:return json.load(response)
            except urllib.error.HTTPError as exc:
                if exc.code==401 and attempt==0:self.refresh();continue
                raise RuntimeError(f'Prove2Me HTTP {exc.code} at {path.split("?")[0]}') from None
        raise RuntimeError('Authentication retry failed')
    def search(self, **params):
        params['env']=PIN;params['limit']=200;params['offset']=0
        result=[]
        while True:
            page=self.call('/theorems?'+urllib.parse.urlencode(params))
            rows=page.get('theorems',[]);result.extend(rows)
            if not rows or len(result)>=page.get('total',len(result)):return result
            params['offset']+=len(rows)
    def verify(self, theorem_id, proof, explanation):
        boundary='proof-'+uuid.uuid4().hex; chunks=[]
        for name,value in [('theorem_id',theorem_id),('proof_type','prove'),('explanation',explanation)]:
            chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n'.encode())
        chunks.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain; charset=utf-8\r\n\r\n'.encode()+proof+b'\r\n')
        chunks.append(f'--{boundary}--\r\n'.encode())
        return self.call('/verify','POST',data=b''.join(chunks),content_type='multipart/form-data; boundary='+boundary)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--workspace',type=pathlib.Path,required=True)
    p.add_argument('--packet',type=pathlib.Path,required=True)
    p.add_argument('--credentials',type=pathlib.Path)
    p.add_argument('--submit',action='store_true')
    p.add_argument('--equivalents-reviewed',action='store_true',help='Affirm that the related-theorem search has been reviewed before creating a new result')
    args=p.parse_args();root=args.workspace.resolve();packet=args.packet.resolve()
    problem=json.loads((packet/'problem.json').read_text());target=problem['problems'][0]
    if problem.get('env')!=PIN:raise RuntimeError('Unexpected environment pin')
    proof_path=packet/'solution.lean';proof=proof_path.read_bytes()
    checked=json.loads((packet/'verification.json').read_text())['solution.lean']
    if hashlib.sha256(proof).hexdigest()!=checked['sha256']:raise RuntimeError('Proof hash differs from checked packet')
    lake=pathlib.Path.home()/'.elan/bin/lake'
    run=subprocess.run([str(lake),'env','lean','-DautoImplicit=false',str(proof_path)],cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (packet/'local-recheck.log').write_text(run.stdout)
    if run.returncode:raise RuntimeError('Lean compilation failed; see local-recheck.log. Nothing was submitted.')
    audit=re.search(r"'solution' depends on axioms:\s*\[([^]]*)\]",run.stdout)
    if not audit:raise RuntimeError('Missing axiom audit')
    ax={t.strip() for t in audit.group(1).split(',') if t.strip()}
    if not ax<={'propext','Classical.choice','Quot.sound'}:raise RuntimeError('Unexpected proof axioms')
    key=os.environ.get('PROVE2ME_API_KEY','').strip()
    if not key:
        credentials=args.credentials or root/'credentials.json'
        if credentials.exists():key=json.loads(credentials.read_text()).get('api_key','').strip()
    if not key:raise RuntimeError('Set PROVE2ME_API_KEY or use the gitignored workspace credentials.json')
    api=API(key);report={'platform_version':api.version,'proof_sha256':checked['sha256']}
    def save():
        text=json.dumps(report,indent=2,ensure_ascii=False)
        for secret in (api.key,api.token):
            if secret:text=text.replace(secret,'[REDACTED]')
        (packet/'api-status.json').write_text(text+'\n')
    leaf=api.call('/theorems/'+LEAF)
    report['leaf']={k:leaf.get(k) for k in ('theorem_id','theorem_name','status','mathlib_rev')}
    related={}
    for query in ['cube','knapsack','halfspace']:
        for row in api.search(q=query):related[row['theorem_id']]=row
    (packet/'related-theorems.json').write_text(json.dumps(list(related.values()),indent=2,ensure_ascii=False)+'\n')
    rows=api.search(theorem_name=target['theorem_name'])
    report['related_results']=len(related);save()
    if not args.submit:
        print(json.dumps(report,indent=2));return
    theorem_id=None
    if rows:
        if len(rows)!=1:raise RuntimeError('Ambiguous exact-name result')
        row=rows[0];theorem_id=row['theorem_id']
        if re.sub(r'\s+','',row['formal_statement'])!=re.sub(r'\s+','',target['formal_statement']):raise RuntimeError('Existing declaration differs; inspect it before submitting')
        if row['status']=='Proved':report['already_proved']=theorem_id;save();print(json.dumps(report,indent=2));return
    else:
        if not args.equivalents_reviewed:raise RuntimeError('Inspect related-theorems.json and rerun with --equivalents-reviewed before creating a new theorem')
        published=api.call('/submit-problem','POST',payload=problem)
        report['publication']=published;save()
        if published.get('errors') or len(published.get('jobs',[]))!=1:raise RuntimeError('Publication did not queue exactly one clean job')
        job=published['jobs'][0]['job_id'];deadline=time.monotonic()+900
        while time.monotonic()<deadline:
            state=api.call('/publish-jobs/'+job);report['publish_status']=state;save()
            if state['status']=='PUBLISHED':theorem_id=state['theorem_id'];break
            if state['status'] in ('FAILED','ERROR'):raise RuntimeError('Publication failed; see api-status.json')
            time.sleep(10)
        if theorem_id is None:raise RuntimeError('Publication remains pending; recorded job ID in api-status.json')
    live=api.call('/theorems/'+theorem_id)
    if live.get('mathlib_rev')!=PIN:raise RuntimeError('Published theorem has unexpected environment')
    explanation_path=packet/'EXPLANATION.md'
    if not explanation_path.exists():raise RuntimeError('Missing mathematical explanation')
    submitted=api.verify(theorem_id,proof,explanation_path.read_text())
    report['submission']=submitted;save();submission_id=submitted['submission_id']
    deadline=time.monotonic()+900
    while time.monotonic()<deadline:
        state=api.call('/verify?'+urllib.parse.urlencode({'submission_id':submission_id}))
        report['verify_status']=state;save()
        if state['status']!='PENDING':
            report['theorem_status']=api.call('/theorems/'+theorem_id).get('status');save()
            print(json.dumps({'theorem_id':theorem_id,'submission_id':submission_id,'status':state['status'],'theorem_status':report['theorem_status']},indent=2))
            if state['status']!='ACCEPTED':raise SystemExit(1)
            return
        time.sleep(10)
    raise RuntimeError('Verification remains pending; recorded submission ID in api-status.json')

if __name__=='__main__':main()
