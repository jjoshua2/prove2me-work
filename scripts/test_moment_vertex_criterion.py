#!/usr/bin/env python3
"""Exact supporting tests for the universal original moment vertex criterion.
The finite tests are not a Lean proof of all-real statements or the Python code.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import random
import sympy as sp


def mul(p, q):
    z = [F(0)]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): z[i+j] += a*b
    return z


def ev(p, t):
    z = F(0)
    for c in reversed(p): z = z*t+c
    return z


def interpolation(nodes, values):
    if not nodes: return [F(0)]
    result = [F(0)]*len(nodes)
    for i, t in enumerate(nodes):
        p, den = [F(1)], F(1)
        for j, s in enumerate(nodes):
            if i != j: p = mul(p, [-s, F(1)]); den *= t-s
        for j, c in enumerate(p): result[j] += values[i]*c/den
    assert all(ev(result, t) == y for t, y in zip(nodes, values))
    return result


def rows(a, d):
    return [[t**j-sum((s**j for s in a), F(0))/len(a)
             for j in range(1, d+1)] for t in a]


def dot(a, x):
    return sum((u*v for u, v in zip(a, x)), F(0))


def recover(a, A, x, values):
    active = [i for i, row in enumerate(A) if dot(row, x) == 1]
    p = interpolation([a[i] for i in active], values)
    c = sum((ev(p, t) for t in a), F(0))/len(a)
    p += [F(0)]*(len(x)+1-len(p))
    z = [p[j+1]+c*x[j] for j in range(len(x))]
    assert all(dot(A[i], z) == y for i, y in zip(active, values))
    return active, z


def finite_margin(A, x, z):
    inactive = [i for i, a in enumerate(A) if dot(a, x) != 1]
    assert all(dot(A[i], x) < 1 for i in inactive)
    e = min([F(1)]+[(1-dot(A[i], x))/(abs(dot(A[i], z))+1) for i in inactive])/2
    plus = [a+e*b for a, b in zip(x, z)]
    minus = [a-e*b for a, b in zip(x, z)]
    assert all(dot(a, plus) <= 1 and dot(a, minus) <= 1 for a in A)
    return e, plus, minus


def run():
    rng = random.Random(293)
    stats = dict(models=0, complete_active_bases=0, original_vertices=0,
                 tested_points=0, feasible_nonvertices=0, infeasible_points=0, infeasible_full_tight_points=0,
                 tight_card_checks=0, independent_rank_checks=0,
                 arbitrary_active_value_recoveries=0, active_value_identities=0,
                 extreme_classification_checks=0, midpoint_kernel_certificates=0)
    records, saved = [], []
    for d, m in ((0, 1), (1, 3), (2, 3), (2, 5), (3, 5), (4, 5), (4, 7), (4, 9)):
        a = [F(t, 5) for t in rng.sample(range(-20, 24), m)]
        A = rows(a, d)
        vertices, intersections = {}, []
        for S in combinations(range(m), d):
            stats['complete_active_bases'] += 1
            M = sp.Matrix([A[i] for i in S]) if d else sp.zeros(0, 0)
            if d and not M.det(): continue
            x = tuple(F(v) for v in M.inv()*sp.ones(d, 1)) if d else ()
            intersections.append(x)
            if all(dot(row, x) <= 1 for row in A):
                vertices[x] = [i for i, row in enumerate(A) if dot(row, x) == 1]
        assert vertices and all(len(S) == d for S in vertices.values())
        points = list(dict.fromkeys(intersections))[:80]
        points.append(tuple([F(0)]*d))
        vv = list(vertices)
        for _ in range(min(12, len(vv)*2)):
            x, y = rng.choice(vv), rng.choice(vv)
            points.append(tuple((u+v)/2 for u, v in zip(x, y)))
        for _ in range(8): points.append(tuple(F(rng.randint(-8, 8), 7) for _ in range(d)))
        points = list(dict.fromkeys(points))
        for x in points:
            tight = [i for i, row in enumerate(A) if dot(row, x) == 1]
            feasible = all(dot(row, x) <= 1 for row in A)
            assert len(tight) <= d
            rank = sp.Matrix([A[i] for i in tight]).rank() if tight else 0
            assert rank == len(tight)
            assert (x in vertices) == (feasible and len(tight) == d)
            stats['tested_points'] += 1
            stats['tight_card_checks'] += 1
            stats['independent_rank_checks'] += 1
            stats['extreme_classification_checks'] += 1
            if not feasible:
                stats['infeasible_points'] += 1
                if len(tight) == d: stats['infeasible_full_tight_points'] += 1
            for _ in range(3):
                values = [F(rng.randrange(-9, 10), 4) for _ in tight]
                I, z = recover(a, A, x, values)
                assert I == tight
                stats['arbitrary_active_value_recoveries'] += 1
                stats['active_value_identities'] += len(I)
            if feasible and len(tight) < d:
                stats['feasible_nonvertices'] += 1
                M = sp.Matrix([A[i] for i in tight]) if tight else sp.zeros(0, d)
                z = tuple(F(t) for t in M.nullspace()[0])
                assert any(z) and all(dot(A[i], z) == 0 for i in tight)
                e, plus, minus = finite_margin(A, x, z)
                assert plus != minus and tuple((u+v)/2 for u, v in zip(plus, minus)) == x
                stats['midpoint_kernel_certificates'] += 1
                if len(saved) < 12:
                    saved.append(dict(d=d, m=m, nodes=list(map(str, a)), point=list(map(str, x)),
                                      kernel=list(map(str, z)), radius=str(e),
                                      plus=list(map(str, plus)), minus=list(map(str, minus))))
        stats['models'] += 1
        stats['original_vertices'] += len(vertices)
        records.append(dict(d=d, m=m, nodes=list(map(str, a)), vertices=len(vertices),
                            tested_points=len(points), active_sets=[S for S in vertices.values()]))
    # Large explicit tight systems. Positivity/feasibility is not required for
    # the right-inverse theorem; actual original evaluations are always checked.
    large = []
    for d in (16, 32):
        a = list(map(F, range(d+3))); A = rows(a, d)
        S = list(range(0, d, 2))
        p = [F(1)]
        for i in S: p = mul(p, [a[i]**2, -2*a[i], F(1)])
        h = sum((ev(p, t) for t in a), F(0))/len(a)
        x = [-p[j+1]/h for j in range(d)]
        assert all(dot(row, x) <= 1 for row in A)
        I = [i for i, row in enumerate(A) if dot(row, x) == 1]
        assert I == S
        values = [F((-1)**j*(j+1), 3) for j in range(len(I))]
        _, z = recover(a, A, x, values)
        large.append(dict(dimension=d, original_rows=len(a), tight_rows=len(I),
                          recovered_values=list(map(str, values)),
                          full_vertex_inventory_enumerated=False))
    # Repeated nodes invalidate the independence and tight-count conclusions.
    a = [F(0), F(0), F(1)]; A = rows(a, 1); x = [F(-3)]
    assert [dot(row, x) for row in A] == [F(1), F(1), F(-2)]
    assert A[0] == A[1]
    assert stats['infeasible_points'] > 0
    # Saved perturbation certificates can be checked without recomputing kernels.
    for s in saved:
        aa = list(map(F, s['nodes'])); AA = rows(aa, s['d']); xx = list(map(F, s['point']))
        zz = list(map(F, s['kernel'])); ee = F(s['radius'])
        assert ee > 0 and any(zz)
        assert list(map(F, s['plus'])) == [u+ee*v for u, v in zip(xx, zz)]
        assert list(map(F, s['minus'])) == [u-ee*v for u, v in zip(xx, zz)]
        assert all(dot(row, list(map(F, s['plus']))) <= 1 and
                   dot(row, list(map(F, s['minus']))) <= 1 for row in AA)
    return dict(status='PASS', seed=293, counts=stats, complete_reference_models=records,
                larger_active_value_samples=large, saved_midpoint_certificates=saved,
                countermodels=[dict(missing_hypothesis='injective nodes', nodes=['0','0','1'],
                                    point=['-3'], repeated_tight_rows=[0,1]),
                               dict(missing_hypothesis='feasibility in the vertex criterion',
                                    verified_infeasible_full_tight_systems=stats['infeasible_full_tight_points'])],
                scope='Exact finite tests and independent full small original-H enumeration. Not a universal proof by samples, a Lean-extracted solver, or a graph-diameter bound.')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args()
    r = run()
    r['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.parent.mkdir(parents=True, exist_ok=True)
    a.out.write_text(json.dumps(r, sort_keys=True, indent=2)+'\n')
    print(json.dumps(r['counts'], sort_keys=True))

if __name__ == '__main__': main()
