#!/usr/bin/env python3
"""Exact finite regression for target-cone capping and batch reinsertion.

Uses Fraction arithmetic only; no floating-point polyhedral decisions.
These examples are regressions, not replacements for the Lean theorem.
"""
from __future__ import annotations

from collections import deque
from fractions import Fraction as F
from itertools import combinations, product
import hashlib
import json

Point = tuple[F, ...]
Row = tuple[Point, F]


def dot(a: Point, x: Point) -> F:
    assert len(a) == len(x)
    return sum((p * q for p, q in zip(a, x)), F(0))


def rref(matrix: list[list[F]], ncols: int) -> tuple[list[list[F]], list[int]]:
    a = [list(map(F, row)) for row in matrix]
    pivots: list[int] = []
    for col in range(ncols):
        pivot = next((i for i in range(len(pivots), len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        k = len(pivots)
        a[k], a[pivot] = a[pivot], a[k]
        c = a[k][col]
        a[k] = [x / c for x in a[k]]
        for i in range(len(a)):
            if i != k:
                c = a[i][col]
                a[i] = [x - c * y for x, y in zip(a[i], a[k])]
        pivots.append(col)
    return a, pivots


def rank(rows: list[Point], d: int) -> int:
    return len(rref([list(a) for a in rows], d)[1])


def solve(rows: list[Row], d: int) -> Point | None:
    mat, pivots = rref([list(a) + [b] for a, b in rows], d)
    if len(pivots) != d:
        return None
    if any(all(x == 0 for x in row[:d]) and row[d] != 0 for row in mat):
        return None
    return tuple(mat[i][d] for i in range(d))


def vertices(rows: list[Row], d: int) -> list[Point]:
    out = set()
    for ids in combinations(range(len(rows)), d):
        x = solve([rows[i] for i in ids], d)
        if x is not None and all(dot(a, x) <= b for a, b in rows):
            out.add(x)
    return sorted(out)


def graph(rows: list[Row], vs: list[Point], d: int) -> list[set[int]]:
    adj = [set() for _ in vs]
    for i, j in combinations(range(len(vs)), 2):
        common = [a for a, b in rows if dot(a, vs[i]) == b == dot(a, vs[j])]
        if rank(common, d) == d - 1:
            adj[i].add(j)
            adj[j].add(i)
    return adj


def distances(adj: list[set[int]], start: int, allowed: set[int] | None = None) -> dict[int, int]:
    allowed = set(range(len(adj))) if allowed is None else allowed
    ds = {start: 0}
    queue = deque([start])
    while queue:
        i = queue.popleft()
        for j in sorted(adj[i] & allowed):
            if j not in ds:
                ds[j] = ds[i] + 1
                queue.append(j)
    assert set(ds) == allowed, 'unexpected disconnected bounded face/graph'
    return ds


def rows(data: list[tuple[tuple[int, ...], int | F]]) -> list[Row]:
    return [(tuple(map(F, a)), F(b)) for a, b in data]


def fixtures() -> list[tuple[str, int, list[Row]]]:
    square = rows([((-1, 0), 0), ((0, -1), 0), ((1, 0), 1), ((0, 1), 1)])
    cube = rows([(tuple(s if i == j else 0 for i in range(3)), int(s == 1))
                 for j in range(3) for s in (-1, 1)])
    base = [
        ('square', 2, square),
        ('clipped-square', 2, square + rows([((1, 1), F(3, 2))])),
        ('hexagon', 2, rows([((1, 0), 2), ((-1, 0), 2), ((0, 1), 2),
                            ((0, -1), 2), ((1, 1), 3), ((-1, -1), 3)])),
        ('cube', 3, cube),
        ('simplex', 3, rows([((-1, 0, 0), 0), ((0, -1, 0), 0),
                             ((0, 0, -1), 0), ((1, 1, 1), 1)])),
        ('square-pyramid', 3, rows([((1, 0, 1), 1), ((-1, 0, 1), 1),
                                    ((0, 1, 1), 1), ((0, -1, 1), 1), ((0, 0, -1), 0)])),
        ('octahedron', 3, rows([(s, 1) for s in product((-1, 1), repeat=3)])),
        ('planar-square', 3, cube + rows([((0, 0, 1), 0)])),
        ('segment-in-plane', 2, square + rows([((0, 1), 0)])),
        ('singleton', 2, rows([((1, 0), 0), ((-1, 0), 0), ((0, 1), 0), ((0, -1), 0)])),
        ('dimension-zero', 0, rows([((), 0), ((), 1)])),
        ('redundant-and-zero-rows', 2, square + rows([((2, 0), 2), ((0, 0), 0),
                                                       ((0, 0), 7), ((1, 1), 5)])),
    ]
    # An invertible affine transformation plus wildly different positive row
    # scales checks invariance and avoids a unit/axis-only test population.
    for name, d, rs in list(base):
        if d == 0:
            continue
        shift = tuple(F(i + 2, i + 3) for i in range(d))
        transformed = []
        for k, (a, b) in enumerate(rs):
            scale = F(10**20 + k + 1, k + 1)
            aa = tuple(a[i] * (i + 1) * scale for i in range(d))
            transformed.append((aa, b * scale + dot(aa, shift)))
        base.append((name + '-scaled-translated', d, transformed))
    return base


def main() -> None:
    records = []
    totals = {'fixtures': 0, 'targets': 0, 'cap_cases': 0, 'cap_vertices': 0,
              'apex_edges': 0, 'lost_original_vertices': 0, 'final_face_budgets': 0}
    for name, d, rs in fixtures():
        vs = vertices(rs, d)
        assert vs, name
        adj = graph(rs, vs, d)
        ds = [distances(adj, k) for k in range(len(vs))]
        diameter = max(max(v.values()) for v in ds)
        totals['fixtures'] += 1
        for vi, v in enumerate(vs):
            tight = [i for i, (a, b) in enumerate(rs) if dot(a, v) == b]
            omitted = [i for i in range(len(rs)) if i not in tight]
            selected = [rs[i] for i in tight]
            assert rank([a for a, _ in selected], d) == d
            assert vertices(selected, d) == [v]
            totals['targets'] += 1
            totals['lost_original_vertices'] += len(vs) - 1
            c = tuple(-sum((a[j] for a, _ in selected), F(0)) for j in range(d))
            budgets = []
            for i in omitted:
                face = {k for k, x in enumerate(vs) if dot(rs[i][0], x) == rs[i][1]}
                ambient = max((ds[p][q] for p in face for q in face), default=0)
                intrinsic = max((max(distances(adj, p, face).values()) for p in face), default=0)
                assert ambient <= intrinsic
                budgets.append((i, ambient, intrinsic))
                totals['final_face_budgets'] += 1
            total_budget = sum(b for _, b, _ in budgets)
            assert max(ds[vi].values()) <= 1 + total_budget
            assert diameter <= 2 + total_budget
            for margin in (F(1, 3), F(1), F(19)):
                level = max(dot(c, x) for x in vs) + margin
                caprow = (c, level)
                capped_rows = selected + [caprow]
                cvs = vertices(capped_rows, d)
                cadj = graph(capped_rows, cvs, d)
                assert v in cvs
                root = cvs.index(v)
                assert cadj[root] == set(range(len(cvs))) - {root}
                assert max(max(distances(cadj, k).values()) for k in range(len(cvs))) <= 2
                assert all(dot(c, x) < level for x in vs)
                recovered = vertices(capped_rows + [rs[i] for i in omitted], d)
                assert recovered == vs
                totals['cap_cases'] += 1
                totals['cap_vertices'] += len(cvs)
                totals['apex_edges'] += len(cvs) - 1
                records.append({'fixture': name, 'target': list(map(str, v)),
                                'level': str(level), 'capped_vertices': len(cvs),
                                'root_distance': max(ds[vi].values()),
                                'parent_diameter': diameter, 'face_budget_sum': total_budget})
    # Reject dropping the "cap contains the whole parent" condition.
    square = fixtures()[0][2]
    assert vertices(square + rows([((1, 1), F(1, 2))]), 2) != vertices(square, 2)
    # Retaining slack rows does not in general give a target-centred star.
    partial = square[:3] + rows([((0, 1), 3)])
    pv = vertices(partial, 2)
    pa = graph(partial, pv, 2)
    assert len(pa[pv.index((F(0), F(0)))]) != len(pv) - 1
    encoded = json.dumps(records, sort_keys=True, separators=(',', ':')).encode()
    print(json.dumps({'totals': totals, 'negative_controls': 2,
                      'report_sha256': hashlib.sha256(encoded).hexdigest(),
                      'status': 'all exact checks passed'}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
