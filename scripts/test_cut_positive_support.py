#!/usr/bin/env python3
"""Exact selection/recovery checks; not Lean verification or a proved Python parser."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib, json
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), Q(0))

def vertices(A, b, d):
    found = set(); systems = 0
    for I in combinations(range(len(A)), d):
        systems += 1; M = sp.Matrix([A[i] for i in I])
        if M.det() == 0:
            continue
        x = tuple(Q(t) for t in M.inv()*sp.Matrix([b[i] for i in I]))
        if all(dot(a, x) <= z for a, z in zip(A, b)):
            found.add(x)
    return sorted(found), systems

def select_support(S, x):
    """Search up to ambient Caratheodory size, without using the active-cut bound."""
    d = len(x)
    for n in range(1, min(len(S), d+1)+1):
        for I in combinations(range(len(S)), n):
            V = [S[i] for i in I]
            M = sp.Matrix([[1]*n] + [[v[j] for v in V] for j in range(d)])
            if M.rank() != n:
                continue
            try:
                w, free = M.gauss_jordan_solve(sp.Matrix([1]+list(x)))
            except ValueError:
                continue
            if not free.rows and all(t > 0 for t in w):
                return list(I), list(map(Q, w))
    raise ValueError('no positive independent support found')

def audit(S, x, C, b, I, w):
    require(len(I) == len(w) and I and len(I) == len(set(I)), 'invalid support labels')
    require(all(type(i) is int and 0 <= i < len(S) for i in I), 'point outside generating set')
    require(all(t > 0 for t in w) and sum(w) == 1, 'positive normalized weights required')
    V = [S[i] for i in I]; n = len(I); d = len(x)
    require(all(sum(t*v[j] for t, v in zip(w, V)) == x[j] for j in range(d)), 'wrong barycentre')
    require(all(dot(c, x) <= z for c, z in zip(C, b)), 'cut infeasible')
    M = sp.Matrix([[1]*n] + [[v[j] for v in V] for j in range(d)])
    require(M.rank() == n, 'support is not affine-independent')
    active = [j for j in range(len(C)) if dot(C[j], x) == b[j]]
    A = sp.Matrix([[1]*n] + [[dot(C[j], v) for v in V] for j in active])
    require(A.rank() == n, 'active images are dependent')
    require(n <= d+1 and n <= len(active)+1, 'dimension or active-cut bound failed')
    recovered, free = A.gauss_jordan_solve(sp.Matrix([1]+[b[j] for j in active]))
    require(not free.rows and list(map(Q, recovered)) == w, 'active values did not recover weights')
    require(not A.nullspace(), 'signed alternative weights are not unique')
    return {'support': n, 'active_cuts': len(active), 'support_points_outside_cut_set':
            sum(not all(dot(c, v) <= z for c, z in zip(C, b)) for v in V)}

def main():
    models = [(2, [], []), (2, [[1, 1]], [Q(3, 2)]),
              (2, [[1, 2], [-1, 1]], [Q(7, 5), Q(1, 4)]),
              (3, [[1, 1, 1]], [Q(7, 5)]),
              (3, [[1, 1, 0], [0, 1, 1]], [1, 1]),
              (3, [[1, 2, 3], [-1, -2, -3]], [Q(13, 4), -Q(13, 4)])]
    counts = {'models': 0, 'original_square_systems': 0, 'cut_vertices': 0,
              'supports_selected': 0, 'active_unique_recoveries': 0,
              'selected_points_outside_cut': 0, 'redundant_generators_cases': 0}
    fixtures = []
    for d, C, b in models:
        C = [tuple(map(Q, row)) for row in C]; b = list(map(Q, b))
        E = [tuple(Q(i == j) for j in range(d)) for i in range(d)]
        A = [tuple(-z for z in row) for row in E]+E+C
        rhs = [Q(0)]*d+[Q(1)]*d+b
        X, systems = vertices(A, rhs, d)
        counts['models'] += 1; counts['original_square_systems'] += systems
        counts['cut_vertices'] += len(X)
        cube = list(product([Q(0), Q(1)], repeat=d))
        for extra in [False, True]:
            S = cube if not extra else [(Q(1, 2),)*d]+cube
            for x in X:
                I, w = select_support(S, x); result = audit(S, x, C, b, I, w)
                counts['supports_selected'] += 1; counts['active_unique_recoveries'] += 1
                counts['selected_points_outside_cut'] += result['support_points_outside_cut_set']
                counts['redundant_generators_cases'] += extra
                fixtures.append({'S': S, 'point': x, 'C': C, 'b': b, 'indices': I, 'weights': w, 'audit': result})
    sharp = []
    for d in [0, 1, 2, 3, 8, 16]:
        S = [tuple(Q(i == j) for j in range(d)) for i in range(d)]+[(Q(0),)*d]
        x = (Q(1, d+1),)*d; C = S[:-1]; b = list(x); w = [Q(1, d+1)]*(d+1)
        result = audit(S, x, C, b, list(range(d+1)), w)
        require(result['support'] == result['active_cuts']+1, 'sharpness failed')
        sharp.append({'dimension': d, **result})
    negative = []
    def reject(name, call):
        try:
            call()
        except ValueError:
            negative.append(name)
        else:
            raise AssertionError('invalid case was accepted: '+name)
    S = [(Q(0),), (Q(1),), (Q(1, 2),)]
    reject('without_extremality', lambda: audit(S, (Q(1, 2),), [], [], [0, 1], [Q(1, 2)]*2))
    reject('zero_weight_unused_point', lambda: audit(S, (Q(0),), [], [], [0, 1], [Q(1), Q(0)]))
    reject('dependent_support', lambda: audit(S, (Q(1, 2),), [(Q(1),)], [Q(1, 2)], [0, 1, 2], [Q(1, 3)]*3))
    reject('wrong_barycentre', lambda: audit(S, (Q(1, 3),), [], [], [0], [Q(1)]))
    reject('wrong_weight_sum', lambda: audit(S, (Q(0),), [], [], [0], [Q(2)]))
    reject('point_not_from_generators', lambda: audit(S, (Q(0),), [], [], [3], [Q(1)]))
    reject('infeasible_cut', lambda: audit(S, (Q(0),), [(Q(1),)], [Q(-1)], [0], [Q(1)]))
    # A redundant active cut changes the card bound but not the recovered support.
    eps_cases = []
    for p in [8, 40, 120, 240]:
        e = Q(1, 2**p); x = (Q(1, 3),); C = [(Q(1),), (Q(2),), (-Q(1),)]; b = [x[0], 2*x[0], -x[0]+e]
        I, w = select_support(S[:2], x)
        result = audit(S[:2], x, C, b, I, w)
        require(result['active_cuts'] == 2 and result['support'] == 2, 'redundant active rows mishandled')
        eps_cases.append(p)
    folder = ROOT/'research/publication_packets/cut_vertex_positive_support'
    data = {'status': 'PASS', 'scope': 'Exact finite supporting tests, not Lean or a formally verified selector.',
            'counts': counts, 'sharp_cases': sharp, 'negative_controls': negative,
            'tiny_inactive_slack_powers': eps_cases,
            'solution_sha256': hashlib.sha256((folder/'solution.lean').read_bytes()).hexdigest(),
            'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    def ser(v):
        if isinstance(v, Q): return str(v)
        if isinstance(v, dict): return {k: ser(w) for k, w in v.items()}
        if isinstance(v, (list, tuple)): return [ser(w) for w in v]
        return v
    (ROOT/'research/CUT_POSITIVE_SUPPORT_TEST.json').write_text(json.dumps(ser(data), indent=2, sort_keys=True)+'\n')
    (ROOT/'fixtures').mkdir(exist_ok=True)
    (ROOT/'fixtures/cut_positive_support.json').write_text(json.dumps(ser(fixtures), indent=2, sort_keys=True)+'\n')
    print(json.dumps(ser(data), indent=2))
if __name__ == '__main__':
    main()
