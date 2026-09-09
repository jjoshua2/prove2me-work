#!/usr/bin/env python3
"""Exact finite certificates for pointed unbounded simultaneous clipping.

No floating-point geometry or LP. All candidate finite vertices and recession
extreme rays are enumerated by exact rational rank tests. All final vertex
pairs are tested. Cap shortcuts are explicitly distinguished from graph edges.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
import json
import random
import sys
from test_face_preserving_checkpoints import (
    Poly, Point, Row, point, dot, sub, lerp, rank, solve, cube_rows, dantzig_polars)


def kernel_one(rows: list[Point], d: int) -> Point | None:
    a = [list(r) for r in rows]
    pivots, r = [], 0
    for c in range(d):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        z = a[r][c]
        a[r] = [x / z for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][c]
                a[i] = [x - z * y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    if r != d - 1:
        return None
    free = next(c for c in range(d) if c not in pivots)
    v = [Q(0)] * d
    v[free] = Q(1)
    for i, c in enumerate(pivots):
        v[c] = -a[i][free]
    return tuple(v)


def recession_rays(rows: list[Row]) -> list[Point]:
    d = len(rows[0][0])
    normals = [a for a, _ in rows]
    assert rank(normals) == d, 'lineality is outside this certificate class'
    rays = set()
    for ids in combinations(range(len(rows)), d - 1):
        v = kernel_one([normals[i] for i in ids], d)
        if v is None:
            continue
        for sign in (1, -1):
            w = tuple(sign * x for x in v)
            if all(dot(a, w) <= 0 for a in normals):
                norm = sum(map(abs, w), Q(0))
                assert norm > 0
                rays.add(tuple(x / norm for x in w))
    return sorted(rays)


class PointedPoly(Poly):
    """Unbounded finite-vertex graph; vertices need not affinely span ambient space."""
    def __init__(self, rows: list[Row]):
        self.rows = [(point(a), Q(b)) for a, b in rows]
        self.d = len(self.rows[0][0])
        assert rank([a for a, _ in self.rows]) == self.d
        vs = set()
        for ids in combinations(range(len(rows)), self.d):
            x = solve([self.rows[i] for i in ids])
            if x is not None and self.feasible(x):
                vs.add(x)
        self.v = sorted(vs)
        assert self.v
        self.tight = [self.active(v) for v in self.v]
        self.graph = [set() for _ in self.v]
        for i, j in combinations(range(len(self.v)), 2):
            common = self.tight[i] & self.tight[j]
            if rank([self.rows[k][0] for k in common]) == self.d - 1:
                self.graph[i].add(j)
                self.graph[j].add(i)
        assert len(self.distances(0)) == len(self.v)
        self.rays = recession_rays(self.rows)
        assert self.rays, 'this test class is specifically unbounded'


class CapCertificate:
    def __init__(self, rows: list[Row], cuts: list[Row]):
        self.original = PointedPoly(rows)
        self.cuts = [(point(a), Q(b)) for a, b in cuts]
        raw_final = Poly(self.original.rows + self.cuts)
        assert recession_rays(raw_final.rows) == [], 'final parent must be bounded'
        self.ell = tuple(-sum((a[j] for a, _ in self.original.rows), Q(0))
                         for j in range(self.original.d))
        assert all(dot(self.ell, r) > 0 for r in self.original.rays)
        self.level = max(dot(self.ell, x) for x in self.original.v + raw_final.v) + 1
        self.outer = Poly(self.original.rows + [(self.ell, self.level)])
        assert recession_rays(self.outer.rows) == []
        self.inner = Poly(self.outer.rows + self.cuts)
        assert self.inner.v == raw_final.v and self.inner.graph == raw_final.graph
        assert all(dot(self.ell, x) < self.level for x in self.inner.v)
        self.old = frozenset(self.outer.v.index(x) for x in self.original.v)
        self.cap = frozenset(range(len(self.outer.v))) - self.old
        assert self.cap and self.cap == self.outer.face([len(self.original.rows)])
        self.base = {}
        for c in sorted(self.cap):
            bases = self.outer.graph[c] & self.old
            assert bases, 'new cap vertex must be adjacent to an original finite vertex'
            self.base[c] = min(bases)
        for a, edges in enumerate(self.original.graph):
            oa = self.outer.v.index(self.original.v[a])
            assert all(self.outer.v.index(self.original.v[b]) in self.outer.graph[oa] for b in edges)
        self.D = self.original.diameter()
        self.centre = tuple(sum((x[j] for x in self.inner.v), Q(0)) / len(self.inner.v)
                            for j in range(self.inner.d))
        self.slack = [b - dot(a, self.centre) for a, b in self.cuts]
        assert all(s > 0 for s in self.slack), 'full-dimensional strict-centre test suite'
        self.face_cache, self.cost_cache = {}, {}
        self.segment_cache, self.radial_cache, self.round_cache = {}, {}, {}
        self.B = [self.cost(frozenset([len(self.outer.rows) + i])) for i in range(len(cuts))]
        self.bound = self.D + 1 + sum(self.B)
        self.lifts = [self.lift(u) for u in self.inner.v]
        self.counts = {k: 0 for k in ('pairs', 'new_endpoint_pairs', 'cells', 'cap_cells',
            'cap_chords', 'cap_chords_not_edges', 'ray_connector_uses',
            'nonvertex_checkpoints', 'VV_pairs', 'VC_pairs', 'CC_pairs')}
        self.maxroute = self.maxsupports = 0
        self.augmented_route_bound = max(len(self.outer_skeleton(a, b)) - 1
            for a, b in combinations_with_replacement(range(len(self.outer.v)), 2))
        assert self.augmented_route_bound <= self.D + 1

    def face(self, rows: frozenset[int]) -> frozenset[int]:
        if rows not in self.face_cache:
            self.face_cache[rows] = self.inner.face(rows)
        return self.face_cache[rows]

    def cost(self, rows: frozenset[int]) -> int:
        if rows not in self.cost_cache:
            self.cost_cache[rows] = self.inner.diameter(self.face(rows))
        return self.cost_cache[rows]

    def lift(self, u: Point) -> tuple[int, int | None]:
        if u in self.outer.v:
            return self.outer.v.index(u), None
        active = [i for i, (a, b) in enumerate(self.cuts) if dot(a, u) == b]
        assert active
        i = active[0]
        a, b = self.cuts[i]
        k = max(range(len(self.outer.v)), key=lambda k: (dot(a, self.outer.v[k]), k in self.old))
        assert dot(a, self.outer.v[k]) >= b
        return k, i

    def outer_skeleton(self, a: int, b: int) -> list[int]:
        if a == b:
            return [a]
        if a in self.cap and b in self.cap:
            return [a, b]  # a cap chord, deliberately NOT claimed to be an edge
        aa = self.base[a] if a in self.cap else a
        bb = self.base[b] if b in self.cap else b
        start = self.original.v.index(self.outer.v[aa])
        end = self.original.v.index(self.outer.v[bb])
        walk = [self.outer.v.index(self.original.v[i]) for i in self.original.path(start, end)]
        if a in self.cap:
            walk.insert(0, a)
        if b in self.cap:
            walk.append(b)
        assert len(walk) - 1 <= self.D + 1
        assert all(y in self.outer.graph[x] for x, y in zip(walk, walk[1:]))
        return walk

    def radial(self, x: Point) -> Point:
        if x in self.radial_cache:
            return self.radial_cache[x]
        mu = max([Q(1)] + [dot(a, sub(x, self.centre)) / s
                          for (a, _), s in zip(self.cuts, self.slack)])
        y = tuple(o + (z - o) / mu for o, z in zip(self.centre, x))
        assert self.inner.feasible(y)
        self.radial_cache[x] = y
        return y

    def pair(self, ui: int, vi: int) -> None:
        u, v = self.inner.v[ui], self.inner.v[vi]
        a, ai = self.lifts[ui]
        b, bi = self.lifts[vi]
        mode = 'CC' if a in self.cap and b in self.cap else 'VV' if a in self.old and b in self.old else 'VC'
        self.counts['pairs'] += 1
        self.counts[mode + '_pairs'] += 1
        self.counts['new_endpoint_pairs'] += int(u not in self.original.v or v not in self.original.v)
        records = []
        if ai is not None:
            records.append((u, self.outer.v[a], 'spoke', ai, None))
        walk = self.outer_skeleton(a, b)
        paid = 0
        for x, y in zip(walk, walk[1:]):
            if x in self.cap and y in self.cap:
                kind, key = 'cap', None
                self.counts['cap_chords'] += 1
                self.counts['cap_chords_not_edges'] += int(y not in self.outer.graph[x])
            else:
                assert y in self.outer.graph[x]
                kind, key = 'edge', ('edge', min(x, y), max(x, y))
                paid += 1
                self.counts['ray_connector_uses'] += int((x in self.cap) != (y in self.cap))
            records.append((self.outer.v[x], self.outer.v[y], kind, None, key))
        if bi is not None:
            records.append((self.outer.v[b], v, 'spoke', bi, None))
        assert paid <= self.D + 1
        if mode == 'CC':
            assert paid == 0
        if mode == 'VV':
            assert paid <= self.D
        if not records:
            assert u == v
            return
        labels, checkpoints, supports = [], [u], {}
        for x, y, kind, active, key in records:
            assert self.outer.feasible(x) and self.outer.feasible(y)
            assert self.radial(x) == checkpoints[-1]
            if kind == 'spoke':
                normal, rhs = self.cuts[active]
                assert dot(normal, x) >= rhs and dot(normal, y) >= rhs
            if kind == 'cap':
                assert dot(self.ell, x) == dot(self.ell, y) == self.level
            record_key = (x, y, kind, active, key)
            if record_key not in self.segment_cache:
                local_points, local_labels = [self.radial(x)], []
                functions = [(Q(1), Q(0))] + [
                    (dot(normal, sub(x, self.centre)) / slack, dot(normal, sub(y, x)) / slack)
                    for (normal, _), slack in zip(self.cuts, self.slack)]
                times = {Q(0), Q(1)}
                for (a0, a1), (b0, b1) in combinations(functions, 2):
                    if a1 != b1:
                        t = (b0 - a0) / (a1 - b1)
                        if 0 < t < 1:
                            times.add(t)
                times = sorted(times)
                for left, right in zip(times, times[1:]):
                    mid = (left + right) / 2
                    vals = [c + mid * m for c, m in functions]
                    winners = [i for i, z in enumerate(vals) if z == max(vals)]
                    if kind != 'edge':
                        winners = [i for i in winners if i > 0]
                    assert winners
                    winner = winners[0]
                    for t in (left, right):
                        vals = [c + t * m for c, m in functions]
                        assert vals[winner] == max(vals)  # affine dominance on WHOLE cell
                        if kind == 'cap':
                            assert vals[winner] > 1
                    p, q = self.radial(lerp(x, y, left)), self.radial(lerp(x, y, right))
                    assert p == local_points[-1]
                    if winner == 0:
                        assert kind == 'edge'
                        rows = self.outer.tight[key[1]] & self.outer.tight[key[2]]
                        label = key
                        assert self.inner.face_dim(self.face(rows)) <= 1 and self.cost(rows) <= 1
                    else:
                        label = ('cut', winner - 1)
                        rows = frozenset([len(self.outer.rows) + winner - 1])
                    assert rows <= self.inner.active(p) and rows <= self.inner.active(q)
                    assert self.face(rows)
                    local_labels.append((label, rows))
                    local_points.append(q)
                self.segment_cache[record_key] = (local_labels, local_points)
            local_labels, local_points = self.segment_cache[record_key]
            assert checkpoints[-1] == local_points[0]
            for label, rows in local_labels:
                supports[label] = rows
                labels.append(label)
            checkpoints.extend(local_points[1:])
            self.counts['cells'] += len(local_labels)
            self.counts['cap_cells'] += len(local_labels) * int(kind == 'cap')
        assert checkpoints[-1] == v
        for x in checkpoints:
            if x not in self.round_cache:
                self.round_cache[x] = self.inner.select(x)
        rounded = [self.round_cache[x] for x in checkpoints]
        assert rounded[0] == ui and rounded[-1] == vi
        for i, label in enumerate(labels):
            face = self.face(supports[label])
            assert rounded[i] in face and rounded[i + 1] in face
        all_labels = sorted(supports)
        faces = {label: self.face(supports[label]) for label in all_labels}
        graph = {label: {other for other in all_labels if other != label and faces[label] & faces[other]}
                 for label in all_labels}
        start, end = labels[0], labels[-1]
        queue, prev = deque([start]), {start: None}
        while queue and end not in prev:
            x = queue.popleft()
            for y in sorted(graph[x]):
                if y not in prev:
                    prev[y] = x
                    queue.append(y)
        assert end in prev
        chain = [end]
        while chain[-1] != start:
            chain.append(prev[chain[-1]])
        chain.reverse()
        assert len(chain) == len(set(chain))
        route = [ui]
        for k, label in enumerate(chain):
            target = min(faces[label] & faces[chain[k + 1]]) if k + 1 < len(chain) else vi
            route.extend(self.inner.path(route[-1], target, faces[label])[1:])
        assert route[-1] == vi
        assert all(y in self.inner.graph[x] for x, y in zip(route, route[1:]))
        cost = sum(self.cost(supports[label]) for label in chain)
        assert len(route) - 1 <= cost <= paid + sum(self.B) <= self.bound
        if mode == 'CC':
            assert len(route) - 1 <= sum(self.B)
        assert len(supports) <= len(self.cuts) + paid
        self.maxroute = max(self.maxroute, len(route) - 1)
        self.maxsupports = max(self.maxsupports, len(supports))
        self.counts['nonvertex_checkpoints'] += sum(x not in self.inner.v for x in checkpoints)

    def run(self, name: str) -> dict:
        for a, b in combinations_with_replacement(range(len(self.inner.v)), 2):
            self.pair(a, b)
        return dict(name=name, dimension=self.inner.d, original_vertices=len(self.original.v),
            recession_extreme_rays=len(self.original.rays), cap_vertices=len(self.cap),
            final_vertices=len(self.inner.v), surviving_original_vertices=sum(x in self.inner.v for x in self.original.v),
            original_finite_graph_diameter=self.D, capped_ordinary_graph_diameter=self.outer.diameter(),
            augmented_route_bound=self.augmented_route_bound, final_diameter=self.inner.diameter(),
            final_face_cost_sum=sum(self.B), bound=self.bound, longest_constructed_route=self.maxroute,
            max_distinct_supports=self.maxsupports,
            extra_one_necessary=self.inner.diameter() > self.D + sum(self.B),
            distinct_segment_certificates=len(self.segment_cache),
            distinct_affine_cells=sum(len(labels) for labels, _ in self.segment_cache.values()),
            **self.counts)


def orthant_rows(d: int) -> list[Row]:
    return [row for k, row in enumerate(cube_rows(d)) if k % 2 == 0]


def upper_box(d: int) -> list[Row]:
    return [row for k, row in enumerate(cube_rows(d)) if k % 2 == 1]


def cases():
    for d in range(1, 5):
        yield f'orthant_box_{d}', orthant_rows(d), upper_box(d)
        if d <= 3:
            lower = [(a, Q(-1, 4)) for a, _ in orthant_rows(d)]
            yield f'orthant_inset_{d}', orthant_rows(d), lower + upper_box(d)
    for d in range(2, 5):
        rows = cube_rows(d)[:-1]
        top = upper_box(d)[-1]
        yield f'pointed_strip_{d}', rows, [top]
        if d <= 3:
            yield f'pointed_strip_inset_{d}', rows, [(orthant_rows(d)[-1][0], Q(-1, 4)), top]
    epigraph = [(point([1, -1]), Q(0)), (point([-1, -1]), Q(0)), (point([0, -1]), Q(-1))]
    yield 'two_vertex_epigraph', epigraph, [(point([0, 1]), Q(3))]
    yield 'two_vertex_epigraph_inset', epigraph, [(point([0, -1]), Q(-2)), (point([0, 1]), Q(3))]
    square_cone = [(point(v), Q(0)) for v in [(1, 0, -1), (-1, 0, -1), (0, 1, -1), (0, -1, -1)]]
    yield 'nonsimple_square_cone', square_cone, [(point([0, 0, 1]), Q(2))]
    yield 'nonsimple_square_frustum', square_cone, [(point([0, 0, -1]), Q(-1)), (point([0, 0, 1]), Q(2))]
    yield 'nonsimple_square_mixed', square_cone, [(point([0, 0, 1]), Q(2)), (point([1, 0, 0]), Q(1, 2)), (point([0, 1, 0]), Q(3, 4))]
    rng = random.Random(2026090917)
    for d in (2, 3):
        centre = point([Q(1, 2)] * d)
        for trial in range(6):
            cuts = upper_box(d)
            for _ in range(1 + trial % 3):
                a = point([rng.randrange(-3, 4) for _ in range(d)])
                if not any(a):
                    a = point([1] + [0] * (d - 1))
                cuts.append((a, dot(a, centre) + sum(map(abs, a), Q(0)) / 5))
            if trial == 5:
                cuts += [cuts[0], (point([1] * d), Q(100))]
            yield f'seeded_orthant_{d}_{trial}', orthant_rows(d), cuts
    for d, p in zip((4, 5), dantzig_polars()):
        active = p.tight[0]
        rows = [row for i, row in enumerate(p.rows) if i in active]
        cuts = [row for i, row in enumerate(p.rows) if i not in active]
        assert len(rows) == d
        yield f'Dantzig_tangent_cone_{d}', rows, cuts


def main():
    reports = []
    for name, rows, cuts in cases():
        print('Checking ' + name, file=sys.stderr, flush=True)
        reports.append(CapCertificate(rows, cuts).run(name))
    keys = ('pairs', 'new_endpoint_pairs', 'cells', 'cap_cells', 'cap_chords',
            'cap_chords_not_edges', 'ray_connector_uses', 'nonvertex_checkpoints',
            'VV_pairs', 'VC_pairs', 'CC_pairs', 'distinct_segment_certificates', 'distinct_affine_cells')
    total = {key: sum(r[key] for r in reports) for key in keys}
    total.update(cases=len(reports), cases_without_surviving_original_vertices=sum(r['surviving_original_vertices'] == 0 for r in reports),
        extra_one_necessary_instances=sum(r['extra_one_necessary'] for r in reports),
        all_constructed_routes_within_bound=True, all_far_cap_classifications_verified=True)
    assert total['extra_one_necessary_instances'] > 0
    assert total['cap_chords_not_edges'] > 0
    assert all(total[k] > 0 for k in ('VV_pairs', 'VC_pairs', 'CC_pairs'))
    print(json.dumps({'totals': total, 'cases': reports}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
