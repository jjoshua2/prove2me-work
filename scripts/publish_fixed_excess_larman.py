#!/usr/bin/env python3
"""Publish/poll the frozen fixed-excess packet, preserving redacted receipts.

Run prove2me_auth.py check first. Each invocation performs one bounded API
stage; pending jobs are polled by a later invocation, never resubmitted.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
from urllib.parse import urlencode
from publish_verified_exterior_cap import API

PACKET = Path('research/publication_packets/fixed_excess_larman')
INPUTS = Path('research/verification/2026-09-12-exact-support')


def read(name):
    return json.loads((PACKET / name).read_text())


def save(name, value):
    (PACKET / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    return value


def run(stage):
    manifest = read('manifest.json')
    for filename, expected in manifest['sha256'].items():
        assert hashlib.sha256((PACKET / filename).read_bytes()).hexdigest() == expected, filename
    assert read('driver-audit.json')['status'] == 'PASS'
    assert read('driver-audit.json')['sha256'] == manifest['sha256']['driver.lean']
    assert read('composition-typecheck.json')['status'] == 'PASS'
    assert read('composition-typecheck.json')['solution_sha256'] == manifest['sha256']['solution.lean']
    key = os.environ.get('PROVE2ME_API_KEY') or json.loads(Path('credentials.json').read_text())['api_key']
    api = API(key)
    payload = read('problem.json')
    if stage == 'publish':
        if (PACKET / 'publish-response.json').exists():
            raise RuntimeError('Publish receipt already exists; poll the existing job.')
        for name, short in [('Hirsch.larman_bound', 'larman'), ('Hirsch.facet_reduction', 'facet')]:
            expected = json.loads((INPUTS / (short + '.json')).read_text())
            live = api.request('/theorems/' + manifest['public_dependencies'][name])
            assert live['theorem_name'] == name and live['status'] == 'Proved'
            assert live['mathlib_rev'] == manifest['mathlib_rev']
            assert live['formal_statement'] == expected['formal_statement']
            save('dependency-' + short + '.json', live)
        query = urlencode({'theorem_name': payload['theorem_name'], 'env': manifest['mathlib_rev']})
        existing = save('duplicate-check.json', api.request('/theorems?' + query))
        assert existing['total'] == 0, 'Existing theorem: reuse after checking its exact statement.'
        result = save('publish-response.json', api.request('/submit-problem', payload, 'POST'))
        print(json.dumps(result))
    elif stage == 'poll-publish':
        response = read('publish-response.json')
        jobs = response.get('jobs', [])
        job = response.get('job_id') or jobs[0]['job_id']
        result = save('publish-job.json', api.request('/publish-jobs/' + job))
        print(json.dumps({k: result.get(k) for k in ['id', 'status', 'theorem_id', 'error_message']}))
    elif stage == 'submit':
        if (PACKET / 'verify-response.json').exists():
            raise RuntimeError('Verification receipt already exists; poll the existing submission.')
        job = read('publish-job.json')
        assert job['status'] == 'PUBLISHED'
        target = save('target-before.json', api.request('/theorems/' + job['theorem_id']))
        assert target['theorem_name'] == payload['theorem_name']
        assert target['mathlib_rev'] == manifest['mathlib_rev']
        assert ' '.join(target['formal_statement'].split()) == ' '.join(payload['formal_statement'].split())
        result = save('verify-response.json', api.verify(job['theorem_id'],
            (PACKET / 'solution.lean').read_text(), (PACKET / 'explanation.md').read_text()))
        print(json.dumps(result))
    elif stage == 'poll-verify':
        response = read('verify-response.json')
        sid = response.get('submission_id') or response['id']
        result = save('verification.json', api.request('/verify?' + urlencode({'submission_id': sid})))
        print(json.dumps(result))
        if result['status'] == 'ACCEPTED':
            tid = read('publish-job.json')['theorem_id']
            target = save('target-after.json', api.request('/theorems/' + tid))
            assert target['status'] == 'Proved'
            save('decompositions.json', api.request('/theorems/' + tid + '/decompositions'))
            print('Authenticated theorem readback: Proved')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['publish', 'poll-publish', 'submit', 'poll-verify'])
    run(parser.parse_args().stage)
