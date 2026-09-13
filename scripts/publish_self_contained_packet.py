#!/usr/bin/env python3
"""Perform one publication stage for a frozen, fully audited standalone proof.

Only packets with no imported public theorem dependencies are supported.
Existing jobs are polled, never duplicated. Credentials stay inside the API client.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
from urllib.parse import urlencode
from publish_projective_small_blocks import VersionCheckedAPI

def run(p, stage):
    def read(name):
        return json.loads((p / name).read_text())
    def save(name, value):
        (p / name).write_text(json.dumps(value, indent=2) + '\n')
        return value
    manifest = read('manifest.json')
    assert manifest['public_dependencies'] == {}
    for name, digest in manifest['sha256'].items():
        assert hashlib.sha256((p / name).read_bytes()).hexdigest() == digest, name
    evidence = read('packet-audit.json')
    assert evidence['status'] == 'PASS'
    for name in ['driver.lean', 'solution.lean', 'statement.lean']:
        assert evidence['sha256'][name] == manifest['sha256'][name]
        assert evidence['exit_codes'][name] == 0
    api = VersionCheckedAPI(os.environ.get('PROVE2ME_API_KEY') or json.loads(Path('credentials.json').read_text())['api_key'])
    problem = read('problem.json')
    if stage == 'definition':
        assert manifest.get('definition_name')
        assert not (p / 'definition-response.json').exists(), 'Poll the existing definition.'
        payload = read('definition.json')
        dup = save('definition-duplicate-check.json', api.request('/theorems?' + urlencode({'q': payload['definition_name'], 'env': manifest['mathlib_rev']})))
        assert dup['total'] == 0
        result = save('definition-response.json', api.request('/submit-definition', payload, 'POST'))
    elif stage == 'poll-definition':
        response = read('definition-response.json')
        job = response.get('job_id') or response['jobs'][0]['job_id']
        result = save('definition-job.json', api.request('/publish-jobs/' + job))
    elif stage == 'publish':
        if manifest.get('definition_name'):
            job = read('definition-job.json')
            assert job['status'] == 'PUBLISHED'
            live = save('definition-live.json', api.request('/theorems/' + job['theorem_id']))
            assert live['status'] == 'Definition' and live['mathlib_rev'] == manifest['mathlib_rev']
            assert live['definition'] == read('definition.json')['definition']
        assert not (p / 'publish-response.json').exists(), 'Poll the existing publication.'
        dup = save('duplicate-check.json', api.request('/theorems?' + urlencode({'q': problem['theorem_name'], 'env': manifest['mathlib_rev']})))
        assert dup['total'] == 0, 'Compare and reuse the existing theorem.'
        result = save('publish-response.json', api.request('/submit-problem', problem, 'POST'))
    elif stage == 'poll-publish':
        response = read('publish-response.json')
        job = response.get('job_id') or response['jobs'][0]['job_id']
        result = save('publish-job.json', api.request('/publish-jobs/' + job))
    elif stage == 'submit':
        assert not (p / 'verify-response.json').exists(), 'Poll the existing verification.'
        job = read('publish-job.json')
        assert job['status'] == 'PUBLISHED'
        live = save('target-before.json', api.request('/theorems/' + job['theorem_id']))
        assert live['mathlib_rev'] == manifest['mathlib_rev']
        assert live['theorem_name'] == problem['theorem_name']
        assert ' '.join(live['formal_statement'].split()) == ' '.join(problem['formal_statement'].split())
        result = save('verify-response.json', api.verify(job['theorem_id'], (p / 'solution.lean').read_text(), (p / 'explanation.md').read_text()))
    else:
        response = read('verify-response.json')
        sid = response.get('submission_id') or response['id']
        result = save('verification.json', api.request('/verify?' + urlencode({'submission_id': sid})))
        if result['status'] == 'ACCEPTED':
            tid = read('publish-job.json')['theorem_id']
            live = save('target-after.json', api.request('/theorems/' + tid))
            assert live['status'] == 'Proved'
            proof = save('accepted-source-readback.json', api.request('/submissions/' + sid + '/solution'))
            assert proof['content'] == (p / 'solution.lean').read_text()
            save('accepted-source-hash.json', {'status': 'PASS', 'submission_id': sid, 'sha256': hashlib.sha256(proof['content'].encode()).hexdigest()})
    print(json.dumps({k: v for k, v in result.items() if k in ['id', 'status', 'theorem_id', 'submission_id', 'job_id', 'jobs', 'error_message', 'message']}))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('stage', choices=['definition', 'poll-definition', 'publish', 'poll-publish', 'submit', 'poll-verify'])
    args = parser.parse_args()
    run(args.packet, args.stage)
