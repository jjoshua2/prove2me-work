#!/usr/bin/env python3
"""Publish two independently compiled circuit-step results to Prove2Me.

Fail-closed: pinned platform version/environment, collision-safe theorem reuse,
exact formal-statement comparison, ACCEPTED + live Proved requirement, and an
unchanged Polynomial-Hirsch frontier. Credentials are sent only to prove2.me.
"""
from __future__ import annotations

import datetime
import hashlib
import json
import os
import re
import time
import urllib.parse
import urllib.request
import uuid
from pathlib import Path

BASE = 'https://prove2.me/api/v1'
VERSION = '0.9.9'
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
SOURCE = '2ef303016d5edbed0bb339fc7341b4f019ada400'
SOURCE_RUN = '34553646058'
FRONTIER = '73beca40-31bc-42d5-8350-5ec9ac28bd3e'
OUT = Path('circuit_step_publication_receipts')

PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_circuit_slack_model
open scoped RealInnerProductSpace
open Set Hirsch'''

ENTRIES = [
    {
        'key': 'carrier',
        'name': 'Hirsch.maximal_row_circuit_step_common_face_bound',
        'title': 'Maximal row-circuit step common-face bound',
        'proof': Path('/tmp/circuit-public/carrier.lean'),
        'sha256': 'ad1bcdc39d8a8f3dd0993b1af9262647ba27f87b3abf5f9a17b9345993b6cd12',
        'formal': '''namespace Hirsch
theorem maximal_row_circuit_step_common_face_bound
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (z x y : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b))
    (hstep : RowCircuitStep a b x y) :
    HirschCommonFace.commonFaceDim a b x y + d ≤
      n + HirschCommonFace.commonFaceDim a b x x := by sorry
end Hirsch''',
        'natural': '''Let an n-row H-polyhedron in ambient dimension d contain at least one extreme vertex z. For any maximal row-circuit step x→y, neither endpoint need be a vertex. If h is the coordinate dimension of the smallest common carrier of x and y and p is the coordinate dimension of the smallest face containing x, then h + d ≤ n + p. Thus maximality removes the destination-face correction term from the general nonvertex circuit-localization inequality.''',
        'explanation': '''Maximality supplies a row that is tight at the destination and strictly increases along the step direction. This row vanishes on the destination self-carrier but not on the full step carrier, so the destination carrier is a strict subspace and its dimension q satisfies q+1≤h. The verified nonvertex circuit-localization inequality gives 2h+d≤n+p+q+1; substituting q+1≤h yields h+d≤n+p.''',
        'tags': ['polyhedra', 'circuit-diameter', 'graph-diameter', 'formalization'],
    },
    {
        'key': 'swap',
        'name': 'Hirsch.row_circuit_step_swap_iff_tight_blockers',
        'title': 'Exact tight-row criterion for swapping two circuit steps',
        'proof': Path('/tmp/circuit-public/swap.lean'),
        'sha256': '49103bd1d83928d2c28b903ed79ec2b098ca9fd55eaf5af491bd128071de2e5e',
        'formal': '''namespace Hirsch
theorem row_circuit_step_swap_iff_tight_blockers
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y z : EuclideanSpace ℝ (Fin d))
    (hxy : RowCircuitStep a b x y) (hyz : RowCircuitStep a b y z) :
    let w := x + (z - y)
    (RowCircuitStep a b x w ∧ RowCircuitStep a b w z) ↔
      w ∈ Hpoly a b ∧
      (∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, w⟫ = b i ∧ 0 < ⟪a i, z - y⟫) ∧
      (∃ j : Fin n, a j ≠ 0 ∧ ⟪a j, z⟫ = b j ∧ 0 < ⟪a j, y - x⟫) := by sorry
end Hirsch''',
        'natural': '''Suppose x→y→z are two normalized maximal row-circuit steps. Set w=x+(z−y), which swaps the order of the two displacement vectors. Then x→w→z consists of maximal row-circuit steps exactly when w is feasible and each swapped segment has a destination-tight describing row whose value strictly increases along that segment. The criterion allows overlapping row supports; disjoint support is not necessary.''',
        'explanation': '''For the forward direction, every maximal finite-H-presentation circuit step has a destination-tight row with positive directional derivative, applied to x→w and w→z. Their displacements simplify to z−y and y−x. Conversely, feasibility of w plus the two tight increasing blockers certifies maximality beyond normalized length one for each swapped segment, while the circuit directions are exactly the two original circuit displacements.''',
        'tags': ['polyhedra', 'circuits', 'formalization', 'circuit-walk'],
    },
]


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise RuntimeError('authenticated redirects disabled')


class API:
    def __init__(self, key: str):
        self.key = key
        self.token = ''
        self.expires = 0.0
        self.version = None
        self.opener = urllib.request.build_opener(NoRedirect)

    def refresh(self):
        req = urllib.request.Request(
            BASE + '/agent/refresh',
            data=json.dumps({'api_key': self.key}).encode(),
            headers={'Content-Type': 'application/json', 'Accept': 'application/json'},
            method='POST')
        with self.opener.open(req, timeout=45) as response:
            data = json.load(response)
        self.token = data['access_token']
        self.expires = float(data.get('expires_at', time.time() + 3500))
        self.version = data.get('version')
        if self.version != VERSION:
            raise RuntimeError(f'platform version {self.version!r} differs from reviewed {VERSION}')

    def request(self, path: str, data=None, method='GET', content_type='application/json'):
        if not path.startswith('/') or path.startswith('//') or '://' in path:
            raise ValueError('API-relative path required')
        if not self.token or time.time() + 60 >= self.expires:
            self.refresh()
        body = json.dumps(data).encode() if data is not None and not isinstance(data, bytes) else data
        req = urllib.request.Request(
            BASE + path, data=body,
            headers={'Authorization': 'Bearer ' + self.token,
                     'Content-Type': content_type, 'Accept': 'application/json'},
            method=method)
        with self.opener.open(req, timeout=90) as response:
            return json.load(response)

    def verify(self, theorem_id: str, proof: str, explanation: str):
        boundary = '----Prove2Me' + uuid.uuid4().hex
        parts = []
        for name, value in [('theorem_id', theorem_id), ('proof_type', 'prove'),
                            ('explanation', explanation)]:
            parts.append(f'--{boundary}\r\nContent-Disposition: form-data; name="{name}"\r\n\r\n{value}\r\n')
        parts.append(
            f'--{boundary}\r\nContent-Disposition: form-data; name="file"; filename="solution.lean"\r\n'
            f'Content-Type: text/plain\r\n\r\n{proof}\r\n--{boundary}--\r\n')
        return self.request('/verify', ''.join(parts).encode(), 'POST',
                            'multipart/form-data; boundary=' + boundary)


def save(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def norm(text: str | None):
    return re.sub(r'\s+', '', text or '')


def digest(path: Path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_summary(t):
    return {k: t.get(k) for k in ('theorem_id', 'theorem_name', 'status', 'mathlib_rev')}


def poll(api: API, path: str, terminal: set[str], receipt: Path, timeout: int):
    deadline = time.monotonic() + timeout
    while True:
        data = api.request(path)
        save(receipt, data)
        if data.get('status') in terminal:
            return data
        if time.monotonic() > deadline:
            raise TimeoutError('platform job still pending; identifiers retained in receipt')
        time.sleep(5)


def existing(api: API, name: str):
    query = urllib.parse.urlencode({'env': PIN, 'theorem_name': name, 'limit': 50, 'offset': 0})
    rows = api.request('/theorems?' + query).get('theorems', [])
    matches = [r for r in rows if r.get('theorem_name') == name]
    if len(matches) > 1:
        raise RuntimeError(f'ambiguous theorem name {name}')
    return api.request('/theorems/' + matches[0]['theorem_id']) if matches else None


def process(api: API, entry: dict):
    out = OUT / entry['key']
    out.mkdir(parents=True, exist_ok=True)
    if digest(entry['proof']) != entry['sha256']:
        raise RuntimeError(f"frozen proof hash mismatch for {entry['key']}")
    theorem = existing(api, entry['name'])
    registration = 'REUSED' if theorem else 'PUBLISHED'
    if theorem is None:
        payload = {
            'env': PIN, 'private': False,
            'problems': [{
                'theorem_name': entry['name'], 'theorem_title': entry['title'],
                'formal_statement': entry['formal'], 'preamble': PREAMBLE,
                'natural_language_statement': entry['natural'],
                'source': f'https://github.com/jjoshua2/prove2me-work/commit/{SOURCE} ; independently compiled standalone from Actions run {SOURCE_RUN}.',
                'tags': entry['tags'],
            }],
        }
        save(out / 'registration-request.json', payload)
        queued = api.request('/submit-problem', payload, 'POST')
        save(out / 'registration-queued.json', queued)
        if queued.get('errors') or len(queued.get('jobs', [])) != 1:
            raise RuntimeError('registration did not queue exactly one problem')
        job = poll(api, '/publish-jobs/' + queued['jobs'][0]['job_id'],
                   {'PUBLISHED', 'FAILED', 'ERROR'}, out / 'registration-verdict.json', 900)
        if job.get('status') != 'PUBLISHED':
            raise RuntimeError('statement registration failed')
        theorem = api.request('/theorems/' + job['theorem_id'])
    save(out / 'theorem-before.json', theorem)
    if theorem.get('mathlib_rev') != PIN or norm(theorem.get('formal_statement')) != norm(entry['formal']):
        raise RuntimeError('live theorem type or environment mismatch')
    record = {'name': entry['name'], 'theorem_id': theorem['theorem_id'],
              'registration': registration, 'solution_sha256': entry['sha256']}
    if theorem.get('status') == 'Proved':
        record.update(verdict='ALREADY_PROVED', status='Proved')
        save(out / 'result.json', record)
        return record
    if theorem.get('status') != 'Open':
        raise RuntimeError('unexpected theorem status ' + str(theorem.get('status')))
    queued = api.verify(theorem['theorem_id'], entry['proof'].read_text(), entry['explanation'])
    save(out / 'proof-queued.json', queued)
    submission_id = queued['submission_id']
    verdict = poll(api, '/verify?' + urllib.parse.urlencode({'submission_id': submission_id}),
                   {'ACCEPTED', 'SKETCH_ACCEPTED', 'CE', 'WA', 'SORRY', 'FAILED', 'ERROR'},
                   out / 'proof-verdict.json', 1200)
    final = api.request('/theorems/' + theorem['theorem_id'])
    save(out / 'theorem-final.json', final)
    record.update(submission_id=submission_id, verdict=verdict.get('status'), status=final.get('status'))
    save(out / 'result.json', record)
    if record['verdict'] != 'ACCEPTED' or record['status'] != 'Proved':
        raise RuntimeError('proof did not receive ACCEPTED and live Proved')
    return record


def main():
    key = os.environ.get('PROVE2ME_API_KEY', '').strip()
    if not key:
        raise RuntimeError('PROVE2ME_API_KEY repository credential is absent')
    for entry in ENTRIES:
        if not entry['proof'].is_file() or digest(entry['proof']) != entry['sha256']:
            raise RuntimeError('proof packet missing or changed before authentication')
    api = API(key)
    envs = api.request('/environments')
    save(OUT / 'environments.json', envs)
    if not any(e.get('mathlib_rev') == PIN for e in envs.get('environments', [])):
        raise RuntimeError('pinned Mathlib environment unavailable')
    before = api.request('/theorems/' + FRONTIER)
    save(OUT / 'frontier-before.json', theorem_summary(before))
    if before.get('status') != 'Open':
        raise RuntimeError('expected edge-refinement frontier is no longer Open')
    results = []
    for entry in ENTRIES:
        result = process(api, entry)
        results.append(result)
        save(OUT / 'progress.json', results)
        print(json.dumps(result), flush=True)
    after = api.request('/theorems/' + FRONTIER)
    save(OUT / 'frontier-after.json', theorem_summary(after))
    if after.get('status') != 'Open' or after.get('theorem_id') != before.get('theorem_id'):
        raise RuntimeError('edge-refinement frontier changed unexpectedly')
    result = {
        'source_commit': SOURCE, 'source_run': SOURCE_RUN,
        'platform_version': api.version, 'mathlib_rev': PIN,
        'entries': results, 'frontier_before': theorem_summary(before),
        'frontier_after': theorem_summary(after),
        'checked_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'frontier_graph_modified': False, 'new_conjectural_children': 0,
    }
    save(OUT / 'result.json', result)
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as exc:
        save(OUT / 'failure.json', {'type': type(exc).__name__, 'message': str(exc)[:500]})
        print(json.dumps({'type': type(exc).__name__, 'message': str(exc)[:500]}), flush=True)
        raise SystemExit(2)
