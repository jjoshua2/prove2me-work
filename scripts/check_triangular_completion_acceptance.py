#!/usr/bin/env python3
"""Check stored #320 acceptance evidence offline; does not compile Lean or call an API."""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

BASE = Path('research/verification/triangular-completion/accepted-attempt')
PACKET = 'triangular_completion_lower_bound'
HEAD = '7687e9c9ad08d93e6be852ab5950185b9e18469e'
THEOREM = '7be0886c-9c8d-47a1-aa3f-367415e6830f'
SUBMISSION = 'ea54d85a-0fa7-479f-973a-b7ba4059f215'
NAME = 'Hirsch.triangular_all_zonotope_completions_exponential'
ENV = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
EXPECTED = {
    'solution.lean': '0d66d238760cd88b933429d49c0d421a04af8c4c66f13c6ad532feff625b4fb2',
    'driver.lean': '0d66d238760cd88b933429d49c0d421a04af8c4c66f13c6ad532feff625b4fb2',
    'statement.lean': 'ca301ede669b45029e571c7e27b9c262a08e9da31bd08c906ceda83f45d28792',
    'problem.json': '252244220c3676656fa03afc10e3d7e46f9cfc09063f52da12b7a654b60329e2',
    'explanation.md': 'a9ba01d0c6d3f6ae2160cd7a6e0a2dca87734e49e43544c9e0e71022ca08ee37',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def verify(root: Path) -> dict:
    checks: list[str] = []
    def require(condition: bool, label: str) -> None:
        if not condition:
            raise ValueError(label)
        checks.append(label)
    def read(path: Path):
        return json.loads(path.read_text(encoding='utf-8'))
    evidence = root / BASE
    packet = evidence / 'verified/packets' / PACKET
    manifest = read(packet / 'manifest.json')
    artifact = read(evidence / 'verified/artifact.json')
    request = read(evidence / 'resolved.json')
    receipt = read(evidence / 'receipts/publication-receipt.json')
    audit = read(packet / 'packet-audit.json')
    require(manifest['source_commit'] == artifact['head_sha'] == request['head_sha'] == receipt['head_sha'] == HEAD,
            'request/artifact/manifest/receipt bind the same accepted head')
    require(manifest['mathlib_rev'] == ENV and manifest['public_dependencies'] == {},
            'pinned self-contained environment')
    require(request['action'] == 'publish' and str(request['pr']) == '320' and
            request['packets'] == ['research/publication_packets/' + PACKET], 'exact request target')
    require(len(receipt['packets']) == len(artifact['packets']) == 1, 'single packet')
    verdict = receipt['packets'][0]
    require(verdict['status'] == 'ACCEPTED' and verdict['registration'] == 'PUBLISHED' and
            verdict['live_status'] == 'Proved', 'trusted publisher records published/accepted/proved')
    require(verdict['theorem_id'] == THEOREM and verdict['submission_id'] == SUBMISSION and
            verdict['theorem_name'] == NAME and verdict['packet'] == PACKET, 'exact theorem/submission identity')
    require(manifest['sha256'] == artifact['packets'][0]['sha256'] == EXPECTED, 'all expected frozen hashes recorded')
    for name, digest in EXPECTED.items():
        require(hashlib.sha256((packet / name).read_bytes()).hexdigest() == digest, 'hash: ' + name)
    require((packet / 'driver.lean').read_bytes() == (packet / 'solution.lean').read_bytes(), 'driver equals solution')
    require(audit['status'] == 'PASS' and audit['exit_codes'] ==
            {'driver.lean': 0, 'solution.lean': 0, 'statement.lean': 0}, 'three recorded compilation exits are zero')
    require(set(audit['axioms']) == ALLOWED and audit['sha256'] ==
            {name: EXPECTED[name] for name in ('driver.lean', 'solution.lean', 'statement.lean')},
            'recorded audit uses only standard axioms and expected source hashes')
    source = (packet / 'solution.lean').read_text(encoding='utf-8')
    require(not re.search(r'\b(sorry|admit|axiom|sorryAx)\b', source), 'no admission tokens in proof source')
    problem = read(packet / 'problem.json')
    decl = source[source.index('\ntheorem solution ') + 1:]
    actual_type = decl.split(' := by\n', 1)[0]
    target_type = problem['formal_statement'].replace('theorem ' + NAME, 'theorem solution', 1).split(' := by sorry', 1)[0]
    require(actual_type == target_type and problem['env'] == ENV, 'exact public target type and environment')
    for name in ('driver-compile.log', 'solution-compile.log'):
        log = (packet / name).read_text(encoding='utf-8')
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
        expected_names = {'Hirsch.TriangularCompletion.' + s for s in
                          ('hull_eq_body','exposed_line','directions_separate','minimal_eq_body','exponential_completion')} | {'solution'}
        require(len(reports) == 6 and {n for n, _ in reports} == expected_names and
                all(set(a.strip() for a in axioms.split(',')) == ALLOWED for _, axioms in reports),
                'six standard-only proof reports: ' + name)
    require((evidence / 'receipts/publication-receipt.json').read_bytes() ==
            (root / 'research/publication_packets' / PACKET / 'publication-receipt.json').read_bytes(),
            'packet receipt is an unchanged copy of raw receipt')
    return {'kind': 'offline_stored_evidence_integrity_not_new_Lean_or_platform_verification',
            'status': 'PASS', 'checks': checks, 'check_count': len(checks),
            'accepted_head': HEAD, 'theorem_id': THEOREM, 'submission_id': SUBMISSION}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps(verify(args.root), indent=2))
