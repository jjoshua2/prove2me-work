#!/usr/bin/env python3
"""Deterministic exact-rational controls for target-anchored batch deletion.
These finite tests supplement, and do not replace, the Lean kernel proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import combinations
import json
from typing import Sequence

Vector = tuple[F, ...]
Rows = tuple[tuple[Vector, F], ...]

def dot(a: Vector, x: Vector) -> F:
    return sum((p*q for p,q in zip(a,x)), F(0))

def rank(rows: Sequence[Vector], d: int) -> int:
    a = [list(r) for r in rows]
    k = 0
    for j in range(d):
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        pivot = a[k][j]
        a[k] = [x/pivot for x in a[k]]
        for i in range(len(a)):
            if i != k:
                q = a[i][j]
                a[i] = [x-q*y for x,y in zip(a[i],a[k])]
        k += 1
    return k

def solve(rows: Rows, d: int) -> Vector | None:
    if d == 0:
        return ()
    a = [list(r)+[b] for r,b in rows]
    for j in range(d):
        p = next((i for i in range(j,d) if a[i][j]), None)
        if p is None:
            return None
        a[j], a[p] = a[p], a[j]
        pivot = a[j][j]
        a[j] = [x/pivot for x in a[j]]
        for i in range(d):
            if i != j:
                q = a[i][j]
                a[i] = [x-q*y for x,y in zip(a[i],a[j])]
    return tuple(a[j][-1] for j in range(d))

def vertices(rows: Rows, d: int) -> set[Vector]:
    out: set[Vector] = set()
    for indices in combinations(range(len(rows)), d):
        x = solve(tuple(rows[i] for i in indices), d)
        if x is not None and all(dot(a,x) <= b for a,b in rows):
            out.add(x)
    return out

def R(rows: list[tuple[Sequence[int | F], int | F]]) -> Rows:
    return tuple((tuple(map(F,a)),F(b)) for a,b in rows)

def subsets(indices: list[int]):
    for k in range(len(indices)+1):
        yield from combinations(indices,k)

def progress(v: Vector, x: Vector, M: F) -> set[int]:
    return {i for i in range(len(v)) if (x[i] == 0 if v[i] == 0 else x[i] <= M*v[i])}

def main() -> None:
    square = R([((-1,0),0),((1,0),1),((0,-1),0),((0,1),1)])
    huge = 10**40 + 7
    fixtures: list[tuple[str,int,Rows]] = [
        ('square',2,square),
        ('triangle',2,R([((-1,0),0),((0,-1),0),((1,1),1)])),
        ('redundant_zero_duplicate',2,square+R([((0,0),0),((0,0),2),((2,0),2),((1,1),3)])),
        ('lower_dimensional_segment',2,R([((-1,0),0),((1,0),1),((0,1),0),((0,-1),0)])),
        ('unbounded_half_strip',2,R([((-1,0),0),((0,-1),0),((0,1),1)])),
        ('unbounded_wedge',2,R([((-1,0),0),((0,-1),0),((-1,-1),-1)])),
        ('sheared_cube',3,R([((1,1,0),2),((-1,-1,0),0),((0,1,1),3),((0,-1,-1),-1),((0,0,1),2),((0,0,-1),0)])),
        ('large_coefficients',2,R([((-huge,0),0),((huge,0),huge),((0,-huge),0),((0,huge),huge)])),
        ('dimension_zero',0,R([((),0),((),1)])),
    ]
    reports = []
    total_targets = total_batches = 0
    for name,d,rows in fixtures:
        vs = vertices(rows,d)
        assert vs, name
        checks = 0
        for v in sorted(vs):
            tight = [i for i,(a,b) in enumerate(rows) if dot(a,v) == b]
            slack = [i for i,(a,b) in enumerate(rows) if dot(a,v) < b]
            assert rank([rows[i][0] for i in tight],d) == d
            for J in subsets(slack):
                kept = tuple(row for i,row in enumerate(rows) if i not in J)
                assert len(kept)+len(J) == len(rows)
                assert rank([a for a,_ in kept],d) == d
                assert v in vertices(kept,d), (name,v,J)
                # Restoring the removed rows is exactly the original row system.
                assert set(kept).union(rows[i] for i in J) == set(rows)
                checks += 1
            tangent_rows = tuple(rows[i] for i in tight)
            assert vertices(tangent_rows,d) == {v}, (name,v)
        total_targets += len(vs)
        total_batches += checks
        reports.append({'fixture':name,'dimension':d,'targets':len(vs),'batch_deletions':checks})
    # Nonvertex same-phase step: all four slacks are exact fractions.
    x,y,v = (F(1,4),F(1,2)),(F(1),F(1,2)),(F(0),F(0))
    slack = lambda z: tuple(b-dot(a,z) for a,b in square)
    assert progress(slack(v),slack(x),F(2)) == progress(slack(v),slack(y),F(2))
    assert x not in vertices(square,2) and y not in vertices(square,2)
    blocker = 1  # x <= 1; tight at y, strictly slack at target v.
    deleted = tuple(row for i,row in enumerate(square) if i != blocker)
    assert v in vertices(deleted,2) and rank([a for a,_ in deleted],2) == 2
    # Negative control: the quadrant's one-nonneutral-row step changes phase.
    quadrant = R([((-1,0),0),((0,-1),0)])
    qs = lambda z: tuple(b-dot(a,z) for a,b in quadrant)
    assert progress(qs(v),qs((F(1),F(1))),F(2)) != progress(qs(v),qs((F(0),F(1))),F(2))
    # Zero outer vertex diameter must not be confused with the parent's diameter.
    tight_at_origin = tuple(row for row in square if row[1] == 0)
    assert vertices(tight_at_origin,2) == {v}
    assert (F(1),F(1)) in vertices(square,2) and (F(1),F(1)) not in vertices(tight_at_origin,2)
    print(json.dumps({'fixtures':reports,'total_targets':total_targets,'total_batch_deletions':total_batches,
        'same_phase_nonvertex_target_preserved':True,'exception_changes_phase_control':True,
        'other_parent_vertices_need_not_survive_control':True,
        'status':'EXACT_FINITE_REGRESSION_PASS'},sort_keys=True,indent=2))

if __name__ == '__main__':
    main()
