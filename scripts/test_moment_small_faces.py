#!/usr/bin/env python3
"""Exact independent tests of the constructive moment-face witness.

This is a rational arithmetic regression, not Lean compilation. The producer
multiplies polynomial factors. The auditor evaluates the ORIGINAL H rows and
checks every claimed slack/tightness relation. No approximate tolerance is used.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import random
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'research/publication_packets/moment_small_face_witnesses'


def require(value: bool, message: str) -> None:
    if not value:
        raise ValueError(message)


def rational(x: object) -> Q:
    require(type(x) in (int, str, Q), 'exact rational input required')
    return Q(x)


def coefficients(nodes: list[Q], selected: tuple[int, ...]) -> list[Q]:
    out = [Q(1)]
    for i in selected:
        for _ in range(2):
            new = [Q(0)] * (len(out) + 1)
            for j, v in enumerate(out):
                new[j] -= nodes[i] * v
                new[j + 1] += v
            out = new
    return out


def horner(c: list[Q], t: Q) -> Q:
    out = Q(0)
    for v in reversed(c):
        out = out * t + v
    return out


def original_rows(nodes: list[Q], k: int) -> list[list[Q]]:
    m = len(nodes)
    require(m > 0, 'nonempty parameter set required')
    means = [sum((t ** j for t in nodes), Q(0)) / m for j in range(1, 2*k + 1)]
    return [[t**j - means[j-1] for j in range(1, 2*k+1)] for t in nodes]


def produce(nodes: list[Q], k: int, selected: tuple[int, ...]) -> dict[str, Any]:
    require(type(k) is int and k >= 0, 'invalid degree parameter')
    require(len(set(nodes)) == len(nodes), 'parameters must be distinct')
    require(len(selected) == len(set(selected)), 'selected labels must be distinct')
    require(all(type(i) is int and 0 <= i < len(nodes) for i in selected), 'invalid selected index')
    require(len(selected) <= k and len(selected) < len(nodes), 'small proper subset required')
    p = coefficients(nodes, selected)
    values = [horner(p, t) for t in nodes]
    h = sum(values, Q(0)) / len(nodes)
    require(h > 0, 'normalizer must be positive')
    x = [-(p[j] if j < len(p) else Q(0)) / h for j in range(1, 2*k+1)]
    return {'format': 'moment-small-face-v1', 'nodes': list(map(str, nodes)),
            'k': k, 'selected': list(selected), 'coefficients': list(map(str, p)),
            'normalizer': str(h), 'point': list(map(str, x))}


def audit(packet: dict[str, Any]) -> dict[str, int]:
    require(packet['format'] == 'moment-small-face-v1', 'wrong packet format')
    nodes = list(map(rational, packet['nodes']))
    k = packet['k']
    selected = packet['selected']
    require(type(k) is int and k >= 0, 'invalid dimension')
    require(type(selected) is list and all(type(i) is int and 0 <= i < len(nodes) for i in selected),
            'bad selected labels')
    require(len(set(nodes)) == len(nodes), 'node injection failed')
    require(len(selected) == len(set(selected)), 'duplicate selected labels')
    require(len(selected) <= k and len(selected) < len(nodes), 'not a small proper subset')
    x = list(map(rational, packet['point']))
    h = rational(packet['normalizer'])
    coeff = list(map(rational, packet['coefficients']))
    require(len(x) == 2*k and len(coeff) == 2*len(selected)+1 and coeff[-1] == 1,
            'wrong coordinate count or polynomial degree')
    # Reference evaluations use direct products, not the polynomial producer.
    direct = []
    for t in nodes:
        v = Q(1)
        for j in selected:
            v *= (t - nodes[j])**2
        direct.append(v)
    require(h > 0 and h == sum(direct, Q(0)) / len(nodes), 'false normalizer')
    # Check coefficient identity on enough independent points to pin the polynomial.
    probe = list(dict.fromkeys(nodes + [Q(j, 7) for j in range(2*len(selected)+2)]))
    for t in probe:
        v = Q(1)
        for j in selected:
            v *= (t - nodes[j])**2
        require(horner(coeff, t) == v, 'coefficients do not encode the squared-root product')
    rows = original_rows(nodes, k)
    for i, row in enumerate(rows):
        value = sum((a*b for a, b in zip(row, x)), Q(0))
        require(value == 1 - direct[i]/h, 'original-H slack identity failed')
        require(value <= 1 and ((value == 1) == (i in selected)), 'wrong tight row set')
        if i not in selected:
            require(value < 1, 'unselected row is not strictly slack')
    # Output must be the explicit coefficient witness, not an unrelated feasible point.
    require(x == [-(coeff[j] if j < len(coeff) else Q(0))/h for j in range(1, 2*k+1)],
            'point not bound to polynomial coefficients')
    return {'rows': len(rows), 'strict_rows': len(rows)-len(selected),
            'coefficient_probes': len(probe)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'research/MOMENT_SMALL_FACE_TESTS.json')
    args = parser.parse_args()
    records = []
    total = {'instances': 0, 'original_inequalities': 0, 'strict_inequalities': 0,
             'coefficient_probes': 0, 'empty_face_instances': 0, 'zero_dimension_instances': 0}
    configurations = [([Q(t) for t in range(4*k+1)], k) for k in range(5)]
    configurations += [([Q(-5, 3), Q(-2), Q(0), Q(1, 9), Q(7, 5)], 2),
                       ([Q(2, 7), Q(2, 7)+Q(1, 2**30), Q(2, 7)+Q(1, 2**28)], 2),
                       ([Q(0), Q(1)], 5)]
    for case, (nodes, k) in enumerate(configurations):
        for s in range(min(k, len(nodes)-1)+1):
            for chosen in combinations(range(len(nodes)), s):
                p = produce(nodes, k, chosen)
                r = audit(p)
                total['instances'] += 1
                total['original_inequalities'] += r['rows']
                total['strict_inequalities'] += r['strict_rows']
                total['coefficient_probes'] += r['coefficient_probes']
                total['empty_face_instances'] += s == 0
                total['zero_dimension_instances'] += k == 0
                if not records or (case, s) not in {(a['case'], len(a['packet']['selected'])) for a in records}:
                    records.append({'case': case, 'packet': p})
    # Exact high-dimensional samples: no complete graph or all-face enumeration.
    rng = random.Random(282)
    large = []
    for k in (8, 16, 32):
        nodes = [Q(t) for t in range(4*k+1)]
        chosen = tuple(sorted(rng.sample(range(len(nodes)), k)))
        p = produce(nodes, k, chosen)
        r = audit(p)
        large.append({'dimension': 2*k, 'original_rows': len(nodes), 'selected_tight_rows': k,
                      'strict_remaining_rows': r['strict_rows'], 'full_vertex_graph_enumerated': False,
                      'point_numerator_denominator_bits': max(abs(Q(x).numerator).bit_length()+Q(x).denominator.bit_length()
                                                               for x in p['point'])})
        records.append({'case': f'large_{k}', 'packet': p})
    # Minimality application: all immediate proper subsets of odd (k+1)-sets are certified.
    # This does NOT claim those whole sets are infeasible; that is a separate obligation.
    minimality = []
    for k in (2, 3, 4):
        nodes = [Q(t) for t in range(4*k+1)]
        candidates = list(combinations(range(1, 4*k, 2), k+1))
        proper = set()
        for c in candidates:
            for a in c:
                proper.add(tuple(i for i in c if i != a))
        for chosen in sorted(proper):
            audit(produce(nodes, k, chosen))
        minimality.append({'k': k, 'candidate_incompatible_sets': len(candidates),
                          'distinct_immediate_proper_faces_certified': len(proper),
                          'whole_set_infeasibility_proved_by_this_test': False})
    # Deliberately falsify the inputs and exact output.
    negatives = []
    def reject(name: str, action) -> None:
        try:
            action()
        except (ValueError, KeyError, IndexError, TypeError, ZeroDivisionError):
            negatives.append(name)
        else:
            raise AssertionError('forged case accepted: '+name)
    from copy import deepcopy
    good = produce([Q(t) for t in range(9)], 2, (1, 5))
    edits = [
        ('wrong_point', lambda c: c['point'].__setitem__(0, '99')),
        ('wrong_normalizer', lambda c: c.update(normalizer='0')),
        ('wrong_tight_labels', lambda c: c.update(selected=[1, 6])),
        ('wrong_polynomial', lambda c: c['coefficients'].__setitem__(0, '999')),
        ('duplicate_parameters', lambda c: c['nodes'].__setitem__(1, c['nodes'][0])),
        ('boolean_label', lambda c: c.update(selected=[True, 5])),
        ('floating_coordinate', lambda c: c['point'].__setitem__(0, 0.125)),
    ]
    for name, change in edits:
        p = deepcopy(good)
        change(p)
        reject(name, lambda p=p: audit(p))
    reject('entire_parameter_set', lambda: produce([Q(0), Q(1)], 2, (0, 1)))
    reject('too_many_selected', lambda: produce([Q(0), Q(1), Q(2)], 1, (0, 1)))
    reject('empty_parameter_type', lambda: produce([], 0, ()))
    # The independent checker is runnable without its polynomial-coefficient producer.
    global coefficients
    previous = coefficients
    def disabled(*args, **kwargs):
        raise AssertionError('audit called the witness producer')
    coefficients = disabled
    try:
        for r in records:
            audit(json.loads(json.dumps(r['packet'])))
    finally:
        coefficients = previous
    # Bind the public signature to the Lean source without confusing this check with compilation.
    source = (PACKET / 'solution.lean').read_text()
    problem = json.loads((PACKET / 'problem.json').read_text())
    signature = source.split('\ntheorem solution ', 1)[1].split(' := by\n', 1)[0]
    stated = problem['formal_statement'].split('\ntheorem moment_curve_exact_small_face_witnesses ', 1)[1].split(' := by sorry', 1)[0]
    require(signature == stated, 'statement/solution signature mismatch')
    require(problem['preamble'] == 'import Mathlib\nopen scoped BigOperators', 'unexpected preamble')
    for bad in ('sorry', 'admit', 'native_decide', 'unsafe', 'axiom '):
        require(bad not in source, 'prohibited proof token '+bad)
    output = {'status': 'PASS', 'scope': 'exact rational arithmetic and signature tests, NOT Lean verification',
              'small_tests': total, 'large_samples': large, 'proper_subset_application': minimality,
              'negative_controls': negatives, 'producer_disabled_audits': len(records),
              'public_statement_matches_solution': True, 'lean_compilation_performed': False,
              'sources': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (PACKET/'solution.lean', PACKET/'problem.json', Path(__file__))}}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(output, indent=2, sort_keys=True)+'\n')
    fixtures = ROOT/'fixtures/moment_small_face_examples.json'
    fixtures.parent.mkdir(parents=True, exist_ok=True)
    fixtures.write_text(json.dumps(records, indent=2, sort_keys=True)+'\n')
    print(json.dumps(output, indent=2, sort_keys=True))

if __name__ == '__main__':
    main()
