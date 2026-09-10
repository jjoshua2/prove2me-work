#!/usr/bin/env python3
"""Exact pointed H-polyhedron utility from the preceding continuation.

Exhaustive rational bases; an empty ray enumeration certifies boundedness only
after checked full column rank excludes lineality. No floating point is used.
"""
from __future__ import annotations
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations
from math import gcd, lcm
from test_face_preserving_checkpoints import Poly, Point, Row, point, dot, sub, rank, solve, cube_rows


def one_dimensional_kernel(rows: list[Point], d: int) -> Point | None:
    a = [list(r) for r in rows]
    pivots, r = [], 0
    for c in range(d):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        v = a[r][c]
        a[r] = [x / v for x in a[r]]
        for i in range(len(a)):
            if i != r:
                v = a[i][c]
                a[i] = [x - v * y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    if len(pivots) != d - 1:
        return None
    free = next(c for c in range(d) if c not in pivots)
    x = [Q(0)] * d
    x[free] = Q(1)
    for i, c in enumerate(pivots):
        x[c] = -a[i][free]
    assert all(dot(row, tuple(x)) == 0 for row in rows)
    return tuple(x)


def primitive(v: Point) -> Point:
    den = reduce(lcm, (x.denominator for x in v), 1)
    ints = [int(x * den) for x in v]
    div = reduce(gcd, (abs(x) for x in ints), 0)
    assert div
    return tuple(Q(x // div) for x in ints)


def recession_rays(rows: list[Row], d: int) -> list[Point]:
    assert rank([a for a, _ in rows]) == d, 'lineality is outside this checker'
    rays = set()
    for ids in combinations(range(len(rows)), d - 1):
        r = one_dimensional_kernel([rows[i][0] for i in ids], d)
        if r is None:
            continue
        for sign in (1, -1):
            v = primitive(tuple(sign * x for x in r))
            if all(dot(a, v) <= 0 for a, _ in rows):
                rays.add(v)
    return sorted(rays)


class PointedPolyhedron(Poly):
    """Unbounded H-polyhedron with finite edges and rooted ray faces."""
    def __init__(self, rows: list[Row]):
        self.rows = [(point(a), Q(b)) for a, b in rows]
        if not self.rows:
            raise ValueError('at least one row is required')
        self.d = len(self.rows[0][0])
        assert all(len(a) == self.d for a, _ in self.rows)
        assert rank([a for a, _ in self.rows]) == self.d
        vs = set()
        for ids in combinations(range(len(rows)), self.d):
            x = solve([self.rows[i] for i in ids])
            if x is not None and self.feasible(x):
                vs.add(x)
        self.v = sorted(vs)
        assert self.v, 'nonempty pointed instances must have a vertex'
        self.rays = recession_rays(self.rows, self.d)
        assert self.rays, 'this suite specifically exercises unbounded parents'
        assert rank([sub(v, self.v[0]) for v in self.v] + self.rays) == self.d
        self.tight = [self.active(v) for v in self.v]
        self.graph = [set() for _ in self.v]
        for i, j in combinations(range(len(self.v)), 2):
            common = self.tight[i] & self.tight[j]
            if rank([self.rows[k][0] for k in common]) == self.d - 1:
                self.graph[i].add(j)
                self.graph[j].add(i)
        assert len(self.distances(0)) == len(self.v)
        self.ray_edges = []
        for i, active in enumerate(self.tight):
            for j, r in enumerate(self.rays):
                zero = frozenset(k for k in active if dot(self.rows[k][0], r) == 0)
                if rank([self.rows[k][0] for k in zero]) == self.d - 1:
                    self.ray_edges.append((i, j, zero))
        assert self.ray_edges
        assert all(any(j == e[1] for e in self.ray_edges) for j in range(len(self.rays)))


def orthant_rows(d: int) -> list[Row]:
    return [(a, b) for k, (a, b) in enumerate(cube_rows(d)) if k % 2 == 0]
