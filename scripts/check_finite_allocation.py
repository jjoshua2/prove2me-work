#!/usr/bin/env python3
"""Exact finite regressions for the bounded allocation alternative.

Fourier--Motzkin feasibility and independently enumerated positive null rays
must agree. These tests are not Lean compilation or universal formal proof.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random


def dot(x, y):
    if len(x) != len(y):
        raise ValueError('shape mismatch')
    return sum((a*b for a,b in zip(x,y)), Q(0))


def rref(rows, columns):
    rows = [[Q(x) for x in r] for r in rows]
    if any(len(r) != columns for r in rows):
        raise ValueError('ragged matrix')
    pivots = []
    for j in range(columns):
        p = next((i for i in range(len(pivots),len(rows)) if rows[i][j]),None)
        if p is None:
            continue
        k = len(pivots)
        rows[k],rows[p] = rows[p],rows[k]
        scale = rows[k][j]
        rows[k] = [x/scale for x in rows[k]]
        for i in range(len(rows)):
            if i != k and rows[i][j]:
                s = rows[i][j]
                rows[i] = [x-s*y for x,y in zip(rows[i],rows[k])]
        pivots.append(j)
    return rows[:len(pivots)], pivots


def positive_circuits(C, k):
    n = len(C)
    answer = []
    for size in range(1,min(k+1,n)+1):
        for ids in combinations(range(n),size):
            transposed = [[C[i][j] for i in ids] for j in range(k)]
            rr, pivots = rref(transposed,size)
            free = [j for j in range(size) if j not in pivots]
            if len(free) != 1:
                continue
            v = [Q(0)]*size
            v[free[0]] = 1
            for i,p in enumerate(pivots):
                v[p] = -rr[i][free[0]]
            if all(x < 0 for x in v):
                v = [-x for x in v]
            if not all(x > 0 for x in v):
                continue
            w = [Q(0)]*n
            for i,x in zip(ids,v):
                w[i] = x
            assert all(sum(w[i]*C[i][j] for i in range(n)) == 0 for j in range(k))
            answer.append(w)
    return answer


def fourier_motzkin(C, rhs, k):
    """Eliminate variables; no circuit enumeration or simplex solver is used."""
    if len(C) != len(rhs) or any(len(r) != k for r in C):
        raise ValueError('shape mismatch')
    rows = [(tuple(map(Q,a)),Q(b)) for a,b in zip(C,rhs)]
    for _ in range(k):
        positive = [(a,b) for a,b in rows if a[-1] > 0]
        negative = [(a,b) for a,b in rows if a[-1] < 0]
        nxt = [(a[:-1],b) for a,b in rows if a[-1] == 0]
        for a,b in positive:
            for c,d in negative:
                nxt.append((tuple(x/a[-1]-y/c[-1] for x,y in zip(a[:-1],c[:-1])),b/a[-1]-d/c[-1]))
        # Exact normal normalization, keep strongest RHS for each direction.
        kept = {}
        for a,b in nxt:
            z = next((abs(v) for v in a if v),Q(1))
            a,b = tuple(v/z for v in a),b/z
            kept[a] = min(kept.get(a,b),b)
        rows = list(kept.items())
    return all(b >= 0 for _,b in rows)


def allocation_rows(B, b, t, k):
    if t < 0:
        raise ValueError('scale must be nonnegative')
    if len(B) != len(b) or any(len(row) != k for row in B):
        raise ValueError('shape mismatch')
    C = [list(map(Q,row)) for row in B]
    C += [[Q(-int(i == j)) for j in range(k)] for i in range(k)]
    C += [[Q(1)]*k]
    return C,list(map(Q,b))+[Q(0)]*k+[Q(t)]


def validate_null_test(C, rhs, w, k):
    if len(w) != len(C) or len(rhs) != len(C):
        raise ValueError('multiplier shape')
    if any(not isinstance(v,(int,Q)) or isinstance(v,bool) for v in w):
        raise ValueError('exact rational multipliers required')
    if min(w,default=0) < 0:
        raise ValueError('negative multiplier')
    if any(sum(w[i]*C[i][j] for i in range(len(C))) for j in range(k)):
        raise ValueError('not a null multiplier')
    return dot(w,rhs)


def main():
    rng = random.Random(219)
    counts = dict(instances=0, feasible=0, infeasible=0, circuit_tests=0,
                  independently_checked_minima=0, negative_controls=0)
    for k in range(4):
        for m in range(5):
            for trial in range(14):
                B = [[Q(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(k)] for _ in range(m)]
                b = [Q(rng.randrange(-3,5),2) for _ in range(m)]
                t = Q(trial % 4,2)
                C,rhs = allocation_rows(B,b,t,k)
                circuits = positive_circuits(C,k)
                tests = [validate_null_test(C,rhs,w,k) for w in circuits]
                dual = all(v >= 0 for v in tests)
                primal = fourier_motzkin(C,rhs,k)
                assert primal == dual
                counts['instances'] += 1
                counts['feasible' if primal else 'infeasible'] += 1
                counts['circuit_tests'] += len(circuits)
                # Explicit weighted-simplex minimum from the new proof.
                w = [Q(rng.randrange(5)) for _ in range(m)]
                r = [sum(w[i]*B[i][j] for i in range(m)) for j in range(k)]
                nu = max([Q(0)]+[-v for v in r])
                mu = [v+nu for v in r]
                x = [Q(0)]*k
                if nu:
                    x[r.index(-nu)] = t
                assert all(v >= 0 for v in mu+x) and sum(x) <= t
                assert dot(r,x) == -nu*t
                assert all(r[j]-mu[j]+nu == 0 for j in range(k))
                # All vertices of the allocation simplex suffice independently.
                extreme_values = [Q(0)]+[t*v for v in r]
                assert min(extreme_values) == dot(r,x)
                counts['independently_checked_minima'] += 1
    # Joint infeasibility despite every pair being feasible.
    C = [[Q(-1),Q(0)],[Q(0),Q(-1)],[Q(1),Q(1)]]
    rhs = [Q(-1),Q(-1),Q(1)]
    assert all(fourier_motzkin([C[i] for i in ids],[rhs[i] for i in ids],2)
               for ids in combinations(range(3),2))
    assert not fourier_motzkin(C,rhs,2)
    w = positive_circuits(C,2)[0]
    assert validate_null_test(C,rhs,w,2) < 0
    for mutate in ('negative','not_null','short','float','bool'):
        bad = list(w)
        if mutate == 'negative': bad[0] = -1
        if mutate == 'not_null': bad[0] += 1
        if mutate == 'short': bad.pop()
        if mutate == 'float': bad[0] = 1.0
        if mutate == 'bool': bad[0] = True
        try:
            validate_null_test(C,rhs,bad,2)
        except ValueError:
            counts['negative_controls'] += 1
        else:
            raise AssertionError('forged test accepted')
    root = Path(__file__).resolve().parents[1]
    source = root/'research/publication_packets/finite_allocation_minkowski/solution.lean'
    result = {'status':'PASS','scope':'Exact finite regression only; not Lean verification.',
              **counts,'solution_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
              'regression_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (root/'research/FINITE_ALLOCATION_REGRESSION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
