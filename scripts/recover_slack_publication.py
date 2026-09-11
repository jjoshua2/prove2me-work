#!/usr/bin/env python3
"""Recover the existing audited slack submission, never register or resubmit."""
from __future__ import annotations
import datetime
import hashlib
import json
import os
import subprocess
import time
import types
from pathlib import Path
import publish_slack_normal_relations as packet

RESTORED = Path('_slack_recovery')
OUT = Path('slack_publication_recovery_receipts')
PROOF_HASH = '248851588b10bad874626a17463e9c11b542ac3898146abdbb03530fceb57c27'
FRONTIER = '73beca40-31bc-42d5-8350-5ec9ac28bd3e'
MISSION_ID = '6078cb2d-3594-44b1-a01a-fd452ddae274'


def unique(name: str) -> Path:
    paths = list(RESTORED.rglob(name))
    if len(paths) != 1:
        raise RuntimeError('expected exactly one restored ' + name)
    return paths[0]


def read(name: str):
    return json.loads(unique(name).read_text())


def save(name: str, value) -> None:
    OUT.mkdir(exist_ok=True)
    (OUT / name).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def verify_artifact() -> None:
    expected, _ = packet.expected_packet()
    actual = unique('solution.lean').read_bytes()
    if actual != expected or hashlib.sha256(actual).hexdigest() != PROOF_HASH:
        raise RuntimeError('restored proof differs from exact audited bytes')
    if unique('audit-passed.sha256').read_text().strip() != PROOF_HASH:
        raise RuntimeError('restored audit marker differs')
    subprocess.run(['python3', 'scripts/check_lean_axiom_log.py', str(unique('standalone-axioms.log')),
                    'solution', 'HirschSlackMoment.hpoly_and_row_faces_diamLE_two_of_normal_relations'], check=True)
    # Only small result receipts are printed; no keys or tokens are in these files.
    for name in ['registration-queued.json', 'registration-verdict.json', 'proof-queued.json', 'proof-verdict.json']:
        paths = list(RESTORED.rglob(name))
        if len(paths) == 1:
            print('RECOVERED ' + name + ' ' + paths[0].read_text(), flush=True)


def recover() -> None:
    verify_artifact()
    key = os.environ.get('PROVE2ME_API_KEY', '').strip()
    if not key:
        raise RuntimeError('Prove2Me credential absent')
    text, _ = packet.read_source(packet.CLIENT_COMMIT, packet.CLIENT_PATH, packet.CLIENT_BLOB)
    client = types.ModuleType('reviewed_slack_recovery_client')
    exec(compile(text, packet.CLIENT_PATH, 'exec'), client.__dict__)
    client.VERSION = '0.10.1'
    api = client.API(key)
    before = api.request('/theorems/' + FRONTIER)
    save('frontier-before.json', client.theorem_summary(before))
    paths = list(RESTORED.rglob('proof-queued.json'))
    if len(paths) != 1:
        # Do not make a new registration if the prior one is merely queued.
        queued = read('registration-queued.json')
        jobid = queued['jobs'][0]['job_id']
        status = api.request('/publish-jobs/' + jobid)
        save('registration-status.json', status)
        print('REGISTRATION_ONLY ' + json.dumps(status), flush=True)
        return
    sid = read('proof-queued.json')['submission_id']
    theorem = read('theorem-before-proof.json')
    tid = theorem['theorem_id']
    if theorem.get('theorem_name') != packet.NAME or client.norm(theorem.get('formal_statement')) != client.norm(packet.FORMAL):
        raise RuntimeError('restored target identity/type mismatch')
    status = None
    for attempt in range(13):
        status = api.request('/verify?submission_id=' + sid)
        save('proof-verdict.json', status)
        print('EXISTING_SUBMISSION ' + json.dumps(status), flush=True)
        if status.get('status') != 'PENDING':
            break
        if attempt < 12:
            time.sleep(5)
    current = api.request('/theorems/' + tid)
    save('theorem-final.json', current)
    if current.get('mathlib_rev') != packet.PIN if hasattr(packet, 'PIN') else current.get('mathlib_rev') != 'c5ea00351c28e24afc9f0f84379aa41082b1188f':
        raise RuntimeError('live theorem environment mismatch')
    if current.get('theorem_name') != packet.NAME or client.norm(current.get('formal_statement')) != client.norm(packet.FORMAL):
        raise RuntimeError('live target identity/type mismatch')
    comment = None
    if status.get('status') == 'ACCEPTED' and current.get('status') == 'Proved':
        offset = 0
        while True:
            page = api.request(f'/missions/{MISSION_ID}/comments?limit=100&offset={offset}')
            rows = page.get('comments', [])
            comment = next((c for c in rows if any(r.get('type') == 'theorem' and r.get('id') == tid for r in c.get('references', []))), None)
            if comment:
                break
            offset += len(rows)
            if not rows or offset >= int(page.get('total', offset + 1)):
                break
        if comment is None:
            body = (f'Published [positive-normal-relation diameter certificate](p2m:theorem/{tid}) '
                    f'with [accepted standalone proof](p2m:solution/{sid}): n=d+2, a reference vertex, '
                    'positive c, nonconstant t, sum c_i a_i=0, sum t_i c_i a_i=0 and sum c_i b_i=1 '
                    'give intrinsic diameter <=2 for the H-polyhedron AND every original row-support face. '
                    'The proof establishes the exact slack image by rank-nullity and transports actual '
                    'vertices/edges, not just feasible paths. Existence of these positive relation '
                    'witnesses from boundedness alone remains a separate formalization. A separate '
                    'small-excess section-descent proof is being checked; it may obtain the diameter-only '
                    'corollary without needing those witnesses. No general circuit carrier is assumed '
                    'to have excess two. The root and general circuit-to-edge refinement remain Open. '
                    'This post recovers the same submission after its monitoring job was canceled; '
                    'no duplicate proof, theorem, or conjectural child was submitted.')
            comment = api.request(f'/missions/{MISSION_ID}/comments', {'body_md': body, 'tags': ['reference', 'strategy']}, 'POST')
        save('mission-comment.json', comment)
        refs = {(r.get('type'), r.get('id')) for r in comment.get('references', [])}
        if ('theorem', tid) not in refs or ('solution', sid) not in refs:
            raise RuntimeError('recovered mission references unresolved')
    after = api.request('/theorems/' + FRONTIER)
    save('frontier-after.json', client.theorem_summary(after))
    receipt = {
        'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'original_run': '34618047572', 'original_artifact': '10272241257',
        'solution_sha256': PROOF_HASH, 'theorem_id': tid, 'submission_id': sid,
        'verdict': status.get('status'), 'live_status': current.get('status'),
        'mission_comment_id': comment.get('id') if comment else None,
        'frontier_before': client.theorem_summary(before), 'frontier_after': client.theorem_summary(after),
        'duplicate_submission': False, 'graph_mutation': False,
    }
    save('receipt.json', receipt)
    print(json.dumps(receipt, indent=2), flush=True)


if __name__ == '__main__':
    import sys
    verify_artifact() if sys.argv[1:] == ['check-artifact'] else recover()
