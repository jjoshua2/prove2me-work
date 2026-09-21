#!/usr/bin/env python3
"""Check stored #322 packet evidence offline, not Lean or the live platform.

The default validates frozen compilation evidence. --publication additionally
requires the stored publisher receipt to record ACCEPTED and Proved. It never
calls the network, runs Lean, or treats a statement-only placeholder as a proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re

PROOF = '3fa9791c65405c57804730cac7481f28ac26f066'
MATHLIB = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
TARGET = 'Hirsch.finite_hull_original_coordinate_routes'
HASHES = {
    'solution.lean': '250ab15136fee24d87a2b77312ecd51bd5cefb2f082b9a57f9771d266da4cfa2',
    'driver.lean': '250ab15136fee24d87a2b77312ecd51bd5cefb2f082b9a57f9771d266da4cfa2',
    'statement.lean': '3b24b67ce9dc8926c591cfacdc734fa57d6913a1e20dbaad9d11110d33869a96',
    'problem.json': 'c30f73bdcf3477442a793a917f4c581a4712859d212ebc7f2de99ad002a741df',
    'explanation.md': '550e6f9be90a622a462f0473afda43e87b0633b96353695e04e681e3683c9634',
}
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
ROOTS = {
    'Hirsch.CoordinateRoute.descend', 'Hirsch.CoordinateRoute.ascend',
    'Hirsch.CoordinateRoute.rank_routes', 'Hirsch.CoordinateRoute.levelRank_bound',
    'finite_coordinate_route_bound', 'Hirsch.HullCoordinate.improving_edge',
    'Hirsch.HullCoordinate.hull_filter_exposed', 'Hirsch.HullCoordinate.vertex_hull',
    'Hirsch.HullCoordinate.original_routes', 'Hirsch.HullCoordinate.zero_one_routes',
    'solution',
}


def check(packet: Path, publication: bool = False) -> dict:
    passed: list[str] = []

    def need(condition: bool, name: str) -> None:
        if not condition:
            raise ValueError(name)
        passed.append(name)

    def load(name: str) -> dict:
        return json.loads((packet / name).read_text(encoding='utf-8'))

    manifest = load('manifest.json')
    audit = load('packet-audit.json')
    need(manifest['source_commit'] == PROOF, 'frozen proof commit')
    need(manifest['mathlib_rev'] == MATHLIB, 'pinned Mathlib revision')
    need(manifest['public_dependencies'] == {}, 'self-contained packet')
    need(manifest['sha256'] == HASHES, 'exact five-file manifest')
    for name, expected in HASHES.items():
        need(hashlib.sha256((packet / name).read_bytes()).hexdigest() == expected,
             'frozen bytes: ' + name)
    need(audit['status'] == 'PASS', 'stored packet audit PASS')
    need(audit['exit_codes'] == {n: 0 for n in ('driver.lean', 'solution.lean', 'statement.lean')},
         'all three stored compilation exit codes')
    need(audit['sha256'] == {n: HASHES[n] for n in ('driver.lean', 'solution.lean', 'statement.lean')},
         'audit hashes bound to frozen inputs')
    need(set(audit['axioms']) == AXIOMS, 'stored audit standard axioms')
    source = (packet / 'solution.lean').read_text(encoding='utf-8')
    need(not re.search(r'\b(sorry|sorryAx|admit|axiom)\b', source), 'no written proof admissions')
    need((packet / 'driver.lean').read_bytes() == (packet / 'solution.lean').read_bytes(),
         'complete driver equals standalone solution')
    problem = load('problem.json')
    need(problem['theorem_name'] == TARGET, 'exact public target name')
    solution_type = source.split('theorem solution ', 1)[1].split(':= by', 1)[0]
    target_type = problem['formal_statement'].split('theorem ' + TARGET + ' ', 1)[1].split(':= by', 1)[0]
    need(solution_type == target_type, 'full public statement text matches target')
    for name in ('driver-compile.log', 'solution-compile.log'):
        log = (packet / name).read_text(encoding='utf-8')
        reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)
        need(len(reports) == 11 and {n for n, _ in reports} == ROOTS,
             'all eleven proof reports: ' + name)
        need(all({a.strip() for a in axioms.split(',')} == AXIOMS for _, axioms in reports)
             and 'sorryAx' not in log and not re.search(r': error(?:\(|:)', log),
             'only standard axioms and no errors: ' + name)
    if publication:
        receipt = load('publication-receipt.json')
        need(receipt['head_sha'] == PROOF, 'publisher proof commit')
        need(len(receipt['packets']) == 1, 'one publisher packet')
        row = receipt['packets'][0]
        need(row['theorem_name'] == TARGET and row['packet'] == 'geometric_coordinate_routes',
             'publisher target identity')
        need(row['status'] == 'ACCEPTED' and row['live_status'] == 'Proved',
             'stored authenticated publisher ACCEPTED and Proved')
        need(bool(row['theorem_id']) and bool(row['submission_id']), 'publisher identifiers present')
    return {'kind': 'offline stored-evidence check, not new Lean or platform verification',
            'publication_receipt_checked': publication, 'passed': len(passed), 'checks': passed}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path,
                        default=Path('research/publication_packets/geometric_coordinate_routes'))
    parser.add_argument('--publication', action='store_true')
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.packet, args.publication), indent=2))
    except (KeyError, IndexError, ValueError, OSError) as exc:
        parser.exit(1, 'FAIL: ' + str(exc) + '\n')
