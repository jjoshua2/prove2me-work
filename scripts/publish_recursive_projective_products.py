#!/usr/bin/env python3
"""One bounded publication stage for the locally audited recursive-product packet.

Preserve receipts and poll existing jobs; never resubmit a pending operation.
Run prove2me_auth.py check first. Credentials are never written or printed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
from urllib.parse import urlencode
from publish_projective_small_blocks import VersionCheckedAPI

P=Path('research/publication_packets/recursive_projective_products')
V=Path('research/verification/2026-09-12-recursive-projective')

def read(name): return json.loads((P/name).read_text())
def save(name,value):
    (P/name).write_text(json.dumps(value,indent=2)+'\n');return value

def run(stage):
    manifest=read('manifest.json')
    for name,digest in manifest['sha256'].items():
        assert hashlib.sha256((P/name).read_bytes()).hexdigest()==digest,name
    assert read('driver-audit.json')['status']=='PASS'
    assert read('driver-audit.json')['sha256']==manifest['sha256']['driver.lean']
    for name in ['statement','solution']:
        assert read(name+'-exit.json')['exit_code']==0
    assert read('composition-typecheck.json')['solution_sha256']==manifest['sha256']['solution.lean']
    api=VersionCheckedAPI(os.environ.get('PROVE2ME_API_KEY') or json.loads(Path('credentials.json').read_text())['api_key'])
    if stage in ['definition','publish']:
        isdef=stage=='definition';key='definition' if isdef else 'publish'
        assert not (P/(key+'-response.json')).exists(),'Receipt exists: poll the existing job.'
        payload=read('definition.json' if isdef else 'problem.json')
        name=payload['definition_name' if isdef else 'theorem_name']
        dup=save(key+'-duplicate-check.json',api.request('/theorems?'+urlencode({'q':name,'env':manifest['mathlib_rev']})))
        assert dup['total']==0,'Existing artifact: compare and reuse before proceeding.'
        if not isdef:
            job=read('definition-job.json');assert job['status']=='PUBLISHED'
            record=save('definition-live.json',api.request('/theorems/'+job['theorem_id']))
            assert record['mathlib_rev']==manifest['mathlib_rev']
            assert record['status']=='Definition'
            assert record['definition']==read('definition.json')['definition']
            for dep,tid in manifest['public_dependencies'].items():
                live=save('dependency-small-excess.json',api.request('/theorems/'+tid))
                expected=json.loads((V/'small-excess.json').read_text())
                assert live['status']=='Proved' and live['mathlib_rev']==manifest['mathlib_rev']
                assert live['formal_statement']==expected['formal_statement'] and live['theorem_name']==dep
        result=save(key+'-response.json',api.request('/submit-definition' if isdef else '/submit-problem',payload,'POST'))
        print(json.dumps(result))
    elif stage in ['poll-definition','poll-publish']:
        key=stage.removeprefix('poll-');response=read(key+'-response.json')
        job=response.get('job_id') or response['jobs'][0]['job_id']
        result=save(key+'-job.json',api.request('/publish-jobs/'+job))
        print(json.dumps({k:result.get(k) for k in ['id','status','theorem_id','error_message']}))
    elif stage=='submit':
        assert not (P/'verify-response.json').exists(),'Verification receipt exists: poll it.'
        job=read('publish-job.json');assert job['status']=='PUBLISHED'
        live=save('target-before.json',api.request('/theorems/'+job['theorem_id']))
        assert live['mathlib_rev']==manifest['mathlib_rev']
        assert ' '.join(live['formal_statement'].split())==' '.join(read('problem.json')['formal_statement'].split())
        result=save('verify-response.json',api.verify(job['theorem_id'],(P/'solution.lean').read_text(),(P/'explanation.md').read_text()))
        print(json.dumps(result))
    elif stage=='poll-verify':
        response=read('verify-response.json');sid=response.get('submission_id') or response['id']
        result=save('verification.json',api.request('/verify?'+urlencode({'submission_id':sid})))
        print(json.dumps(result))
        if result['status']=='ACCEPTED':
            tid=read('publish-job.json')['theorem_id']
            live=save('target-after.json',api.request('/theorems/'+tid));assert live['status']=='Proved'
            save('decompositions.json',api.request('/theorems/'+tid+'/decompositions'))
            proof=save('accepted-source-readback.json',api.request('/submissions/'+sid+'/solution'))
            assert proof['content']==(P/'solution.lean').read_text()
            save('accepted-source-hash.json',{'status':'PASS','submission_id':sid,'sha256':hashlib.sha256(proof['content'].encode()).hexdigest()})
            print('Proved; accepted source matches frozen packet.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('stage',choices=['definition','poll-definition','publish','poll-publish','submit','poll-verify'])
    run(p.parse_args().stage)
