#!/usr/bin/env python3
"""Exact finite-score itinerary checks. These tests are not Lean verification.
Scalar wall compatibility does not imply geometric adjacency without the
independent-tie exclusion used by PolynomialEnvelopeCrossingEdges.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib, json, random

ROOT = Path(__file__).resolve().parents[1]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def rational(x):
    require(type(x) in (int, str) or isinstance(x, Q), 'exact rational input required')
    return Q(x)

def parse(data):
    out = []
    for factor in data:
        require(bool(factor), 'nonempty factor required')
        f = [tuple(rational(x) for x in line) for line in factor]
        require(all(len(line) == 2 for line in f), 'two scalar coefficients required')
        require(len({a for a, _ in f}) == len(f), 'intercepts must be injective')
        out.append(f)
    return out

def value(line, t):
    return line[0] + t * line[1]

def winners(factors, t):
    choices = []
    for f in factors:
        values = [value(line, t) for line in f]
        ids = [j for j, a in enumerate(values) if a == max(values)]
        require(len(ids) == 1, 'nonunique winner')
        choices.append(ids[0])
    return choices

def verify(data, cert):
    F = parse(data)
    T = [rational(t) for t in cert['samples']]
    W = [rational(t) for t in cert['walls']]
    P = cert['picks']
    require(len(T) == len(P) == len(W) + 1, 'wrong itinerary dimensions')
    require(all(0 < t < 1 for t in T), 'sample outside the open interval')
    require(all(a < b for a, b in zip(T, T[1:])), 'samples not strictly increasing')
    require(P[0] == winners(F, Q(0)) and P[-1] == winners(F, Q(1)), 'endpoint changed')
    checks = 0
    for t, p in zip(T, P):
        require(all(type(j) is int for j in p), 'invalid label type')
        require(p == winners(F, t), 'incorrect sample maximizers')
        checks += sum(map(len, F))
    for j, u in enumerate(W):
        require(T[j] < u < T[j + 1], 'wall not between its samples')
        require(P[j] != P[j+1], 'stationary retained transition')
        for i, f in enumerate(F):
            left, right = value(f[P[j][i]], u), value(f[P[j+1][i]], u)
            require(left == right == max(value(line, u) for line in f), 'not common GLOBAL wall maxima')
            checks += len(f)
    require(len(W) <= sum(len(f) - 1 for f in F), 'additive switch budget failed')
    return {'transitions': len(W), 'budget': sum(len(f) - 1 for f in F), 'score_checks': checks}

def construct(data):
    F = parse(data)
    winners(F, Q(0)); winners(F, Q(1))
    roots = {Q(0), Q(1)}
    for f in F:
        for (a, b), (c, d) in combinations(f, 2):
            if b != d:
                t = (c-a)/(b-d)
                if 0 < t < 1:
                    roots.add(t)
    cuts = sorted(roots)
    samples, picks, walls = [], [], []
    raw_winners = []
    closed_checks = 0
    for l, r in zip(cuts, cuts[1:]):
        t = (l+r)/2
        p = winners(F, t)
        raw_winners.append(p)
        # A separate whole-interval check: each competitor's affine deficit
        # is nonpositive at BOTH endpoints, hence throughout the closed cell.
        for i, f in enumerate(F):
            for z in (l, r):
                require(value(f[p[i]], z) == max(value(line, z) for line in f), 'winner fails cell closure')
                closed_checks += len(f)
        if not picks or p != picks[-1]:
            if picks:
                walls.append(str(l))
            samples.append(str(t)); picks.append(p)
    cert = {'samples': samples, 'picks': picks, 'walls': walls}
    return cert, {**verify(data, cert), 'raw_cells': len(cuts)-1,
                  'discarded_stationary': len(raw_winners)-len(picks), 'closed_score_checks': closed_checks}

def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: serial(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [serial(v) for v in x]
    return x

def main():
    rng = random.Random(243)
    cases = [[], [[(0, 0)]], [[(0, 0), (-1, 0), (-2, 0)]],
        [[(0, 0), (-1, 3), (-3, 6)]],
        [[(0, 0), (-1, 2)], [(2, 0), (1, 2)]],
        [[(0, 0), (-1, 2), (-2, 4)]],
        [[(2, 0), (0, 1), (1, 0)]]]
    for power in (8, 40, 120, 240):
        eps = Q(1, 2**power)
        cases.append([[(0, 0), (-Q(1, 2), 1), (-1-eps, 2)]])
    for _ in range(200):
        fs = []
        for _ in range(rng.randrange(1, 7)):
            k = rng.randrange(1, 9)
            while True:
                intercepts = rng.sample(range(-30, 31), k)
                f = [(Q(a, 7), Q(rng.randrange(-40, 41), 11)) for a in intercepts]
                scores = [a+b for a, b in f]
                if scores.count(max(scores)) == 1: break
            fs.append(f)
        cases.append(fs)
    totals = {'cases': 0, 'transitions': 0, 'raw_cells': 0, 'discarded_stationary': 0,
              'score_checks': 0, 'closed_score_checks': 0}
    witnesses = []
    for data in cases:
        cert, report = construct(data)
        totals['cases'] += 1
        for key in totals:
            if key != 'cases': totals[key] += report[key]
        if len(witnesses) < 11:
            witnesses.append({'input': serial(data), 'certificate': cert, 'report': report})
    rejected = []
    data = [[(0,0),(-1,3),(-3,6)]]
    good, _ = construct(data)
    def reject(name, task):
        try: task()
        except (ValueError, KeyError, IndexError, TypeError): rejected.append(name)
        else: raise AssertionError('accepted negative: '+name)
    bad = deepcopy(good); bad['picks'][0] = [1]
    reject('wrong_endpoint', lambda: verify(data, bad))
    bad = deepcopy(good); bad['walls'][0] = '1/2'
    reject('wrong_wall', lambda: verify(data, bad))
    bad = {'samples':['1/6','5/6'], 'picks':[[0],[2]], 'walls':['1/2']}
    reject('skipped_intermediate_winner', lambda: verify(data, bad))
    bad = deepcopy(good); bad['samples'][0] = '0'
    reject('endpoint_not_interior_sample', lambda: verify(data, bad))
    bad = deepcopy(good); bad['walls'].pop()
    reject('omitted_wall', lambda: verify(data, bad))
    bad = deepcopy(good); bad['samples'].reverse()
    reject('reversed_sample_order', lambda: verify(data, bad))
    bad = deepcopy(good); bad['samples'][0] = 0.1
    reject('floating_input', lambda: verify(data, bad))
    bad = {'samples':['1/3','2/3'], 'picks':[[0],[0]], 'walls':['1/2']}
    reject('stationary_step_counted', lambda: verify([[(0,0)]], bad))
    reject('empty_factor', lambda: construct([[]]))
    reject('duplicate_intercepts', lambda: construct([[(0,0),(0,1)]]))
    reject('tied_final_maximum', lambda: construct([[(0,0),(-1,1)]]))
    source = ROOT/'research/publication_packets/finite_affine_chambers/solution.lean'
    result = {'status':'PASS', 'scope':'Exact scalar regression, NOT Lean compilation or geometric edge verification.',
              'totals':totals,'rejected':len(rejected),'rejected_cases':rejected,
              'independent_simultaneous_tie_is_scalar_only':True,
              'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
              'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'fixtures':witnesses}
    path = ROOT/'research/FINITE_AFFINE_CHAMBERS_TESTS.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'totals':totals,'rejected':len(rejected)},indent=2))

if __name__ == '__main__': main()
