#!/usr/bin/env python3
"""Probe by default; publish only after an explicit reviewed flag and local proof audit."""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'circuit_leaf_packet'
BASE = 'https://prove2.me/api/v1'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
LEAF = '33fc334e-e05b-4090-ac49-f83fd94d9305'

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError('Authenticated redirects disabled')

class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ''
        self.expires = 0.0
        self.opener = urllib.request.build_opener(NoRedirect)
    def refresh(self):
        req = urllib.request.Request(BASE+'/agent/refresh',
            data=json.dumps({'api_key':self.key}).encode(),
            headers={'Content-Type':'application/json'}, method='POST')
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data['access_token']
        self.expires = float(data.get('expires_at', time.time()+3500))
        self.version = data.get('version')
    def request(self, path: str, data=None, method='GET', content_type='application/json'):
        if not path.startswith('/') or path.startswith('//'):
            raise ValueError('Relative API path required')
        if not self.token or time.time()+60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(BASE+path, data=body,
            headers={'Authorization':'Bearer '+self.token, 'Content-Type':content_type}, method=method)
        with self.opener.open(req, timeout=60) as response:
            return json.load(response)
    def verify(self, proof: str, explanation: str):
        boundary = '----Prove2Me'+uuid.uuid4().hex
        parts = []
        for name, value in [('theorem_id', LEAF), ('proof_type','prove'), ('explanation', explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n')
        parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\nContent-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request('/verify', ''.join(parts).encode(), 'POST', 'multipart/form-data; boundary='+boundary)


def write(name, data):
    (OUT/name).write_text(json.dumps(data, indent=2, ensure_ascii=False)+'\n')

def rows(api, **filters):
    found = []
    offset = 0
    while True:
        query = {'env':PIN, 'limit':200, 'offset':offset, **filters}
        result = api.request('/theorems?'+urllib.parse.urlencode(query))
        page = result.get('theorems', [])
        found.extend(page)
        offset += len(page)
        if not page or offset >= result.get('total', offset):
            return found

def wait(api, path, terminal, seconds=240):
    stop = time.monotonic()+seconds
    while True:
        item = api.request(path)
        if item.get('status') in terminal or time.monotonic() >= stop:
            return item
        time.sleep(8)

def normal(text):
    return re.sub(r'\s+', '', text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--publish-reviewed', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(exist_ok=True)
    key = os.environ.get('PROVE2ME_API_KEY', '').strip()
    if not key and (ROOT/'credentials.json').is_file():
        key = json.loads((ROOT/'credentials.json').read_text()).get('api_key','').strip()
    state = {'fetched_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'credential_present':bool(key), 'authenticated':False, 'submitted':False}
    if not key:
        state['reason']='No repository secret or gitignored credentials file is available.'
        write('api-state.json', state)
        print(json.dumps(state))
        return
    api = API(key)
    try:
        leaf = api.request('/theorems/'+LEAF)
        state['authenticated']=True
        state['api_version']=api.version
        state['leaf']={k:leaf.get(k) for k in ('theorem_id','theorem_name','status','mathlib_rev')}
        write('live-leaf.json', leaf)
        related = {}
        for q in ['circuit','Natura','irredundant']:
            for item in rows(api, q=q):
                related[item['theorem_id']]=item
        write('related-theorems.json', list(related.values()))
        state['related_count']=len(related)
        write('api-state.json', state)
        print('AUTHENTICATED_FRONTIER', json.dumps(state))
        if not args.publish_reviewed:
            return
        if leaf.get('status') != 'Open' or leaf.get('mathlib_rev') != PIN:
            raise RuntimeError('Leaf is no longer Open in the pinned environment')
        audit = json.loads((OUT/'verification.json').read_text())
        if not audit.get('exact_parent_signature_match'):
            raise RuntimeError('Missing exact signature audit')
        proof = (OUT/'solution.lean').read_bytes()
        if hashlib.sha256(proof).hexdigest() != audit['proofs']['solution.lean']['sha256']:
            raise RuntimeError('Proof bytes changed after compilation')
        definition = json.loads((OUT/'definition.json').read_text())
        children = json.loads((OUT/'children.json').read_text())
        state['publication']={}
        prior = rows(api, theorem_name=definition['definition_name'])
        if prior:
            if len(prior) != 1 or prior[0].get('status') != 'Definition':
                raise RuntimeError('Definition-name collision requires review')
            full = api.request('/theorems/'+prior[0]['theorem_id'])
            code = full.get('formal_statement') or full.get('definition') or full.get('definitions') or ''
            if normal(code) != normal(definition['definition']):
                raise RuntimeError('Existing definition differs or its code could not be compared')
            state['publication']['definition']=full['theorem_id']
        else:
            queued = api.request('/submit-definition', definition, 'POST')
            write('definition-queued.json', queued)
            item = wait(api, '/publish-jobs/'+queued['job_id'], {'PUBLISHED','FAILED','ERROR'})
            write('definition-status.json', item)
            if item.get('status') != 'PUBLISHED':
                raise RuntimeError('Definition publication is not PUBLISHED')
            state['publication']['definition']=item['theorem_id']
        state['publication']['children']={}
        for child in children['problems']:
            name = child['theorem_name']
            prior = rows(api, theorem_name=name)
            if prior:
                if len(prior) != 1 or normal(prior[0]['formal_statement']) != normal(child['formal_statement']):
                    raise RuntimeError('Existing child has a different signature')
                state['publication']['children'][name]=prior[0]['theorem_id']
                continue
            queued = api.request('/submit-problem', {'env':PIN,'private':False,'problems':[child]}, 'POST')
            write(name.replace('.','_')+'-queued.json', queued)
            if queued.get('errors') or len(queued.get('jobs',[])) != 1:
                raise RuntimeError('Child publication did not return exactly one job')
            item = wait(api, '/publish-jobs/'+queued['jobs'][0]['job_id'], {'PUBLISHED','FAILED','ERROR'})
            write(name.replace('.','_')+'-status.json', item)
            if item.get('status') != 'PUBLISHED':
                raise RuntimeError('Child publication is not PUBLISHED')
            state['publication']['children'][name]=item['theorem_id']
            write('api-state.json', state)
        queued = api.verify(proof.decode(), (OUT/'explanation.md').read_text())
        write('sketch-queued.json', queued)
        state['submitted']=True
        state['submission_id']=queued['submission_id']
        write('api-state.json', state)
        verdict = wait(api, '/verify?'+urllib.parse.urlencode({'submission_id':queued['submission_id']}),
            {'ACCEPTED','SKETCH_ACCEPTED','CE','WA','SORRY','FAILED','ERROR'}, seconds=280)
        write('sketch-verdict.json', verdict)
        state['verdict']=verdict.get('status')
        state['leaf_after']=api.request('/theorems/'+LEAF).get('status')
    except urllib.error.HTTPError as error:
        state['http_error']=error.code
    except Exception as error:
        state['error_type']=type(error).__name__
        # Never serialize request headers, keys, or tokens into logs or artifacts.
        if isinstance(error, RuntimeError):
            state['error']=str(error)
    write('api-state.json', state)
    print('CIRCUIT_LEAF_API_STATE', json.dumps(state))

if __name__ == '__main__':
    main()
