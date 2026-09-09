#!/usr/bin/env python3
"""Exact rational tests for fixed-parent checkpoint rounding and radial repair.

Standard library only. The finite hull/graph calculations are certificates,
not Lean formalizations. The general radial argument is in the research note.
No floating-point LP, sampled hull, or assumed diameter bound is used.
"""
from __future__ import annotations

from collections import deque
from fractions import Fraction as Q
from itertools import combinations, product
import json
import random

Point = tuple[Q, ...]
Row = tuple[Point, Q]


def point(xs) -> Point:
    return tuple(map(Q, xs))


def dot(a: Point, b: Point) -> Q:
    return sum((x * y for x, y in zip(a, b)), Q(0))


def sub(a: Point, b: Point) -> Point:
    return tuple(x - y for x, y in zip(a, b))


def lerp(a: Point, b: Point, t: Q) -> Point:
    return tuple((1 - t) * x + t * y for x, y in zip(a, b))


def rank(rows) -> int:
    if not rows:
        return 0
    a = [list(map(Q, r)) for r in rows]
    r = 0
    for c in range(len(a[0])):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        v = a[r][c]
        a[r] = [x / v for x in a[r]]
        for i in range(r + 1, len(a)):
            v = a[i][c]
            a[i] = [x - v * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def solve(rows: list[Row]) -> Point | None:
    d = len(rows)
    a = [list(v) + [b] for v, b in rows]
    for c in range(d):
        p = next((i for i in range(c, d) if a[i][c]), None)
        if p is None:
            return None
        a[c], a[p] = a[p], a[c]
        q = a[c][c]
        a[c] = [x / q for x in a[c]]
        for i in range(d):
            if i != c:
                q = a[i][c]
                a[i] = [x - q * y for x, y in zip(a[i], a[c])]
    return tuple(a[i][-1] for i in range(d))


class Poly:
    """Finite exact enumeration; callers supply bounded full-dimensional cases."""
    def __init__(self, rows: list[Row]):
        self.rows = [(point(a), Q(b)) for a, b in rows]
        self.d = len(self.rows[0][0])
        assert all(len(a) == self.d for a, _ in self.rows)
        vs = set()
        for ids in combinations(range(len(rows)), self.d):
            x = solve([self.rows[i] for i in ids])
            if x is not None and self.feasible(x):
                vs.add(x)
        self.v = sorted(vs)
        assert self.v, 'empty vertex set'
        assert rank([sub(v, self.v[0]) for v in self.v]) == self.d
        self.tight = [self.active(v) for v in self.v]
        self.graph = [set() for _ in self.v]
        for i, j in combinations(range(len(self.v)), 2):
            common = self.tight[i] & self.tight[j]
            if rank([self.rows[k][0] for k in common]) == self.d - 1:
                self.graph[i].add(j)
                self.graph[j].add(i)
        assert len(self.distances(0)) == len(self.v)

    def feasible(self, x: Point) -> bool:
        return all(dot(a, x) <= b for a, b in self.rows)

    def active(self, x: Point) -> frozenset[int]:
        return frozenset(i for i, (a, b) in enumerate(self.rows) if dot(a, x) == b)

    def face(self, ids) -> frozenset[int]:
        ids = set(ids)
        return frozenset(i for i, active in enumerate(self.tight) if ids <= active)

    def face_dim(self, face) -> int:
        if not face:
            return -1
        first = self.v[min(face)]
        return rank([sub(self.v[i], first) for i in face])

    def distances(self, u: int, allowed=None) -> dict[int, int]:
        allowed = set(range(len(self.v))) if allowed is None else set(allowed)
        assert u in allowed
        ds = {u: 0}
        queue = deque([u])
        while queue:
            a = queue.popleft()
            for b in self.graph[a] & allowed:
                if b not in ds:
                    ds[b] = ds[a] + 1
                    queue.append(b)
        return ds

    def path(self, u: int, v: int, allowed=None) -> list[int]:
        allowed = set(range(len(self.v))) if allowed is None else set(allowed)
        prev = {u: None}
        queue = deque([u])
        while queue and v not in prev:
            a = queue.popleft()
            for b in sorted(self.graph[a] & allowed):
                if b not in prev:
                    prev[b] = a
                    queue.append(b)
        assert v in prev, 'disconnected induced face'
        out = [v]
        while out[-1] != u:
            out.append(prev[out[-1]])
        return out[::-1]

    def diameter(self, face=None) -> int:
        face = frozenset(range(len(self.v))) if face is None else face
        if not face:
            return 0
        ds = [self.distances(i, face) for i in face]
        assert all(len(d) == len(face) for d in ds)
        return max(max(d.values()) for d in ds)

    def irredundant(self) -> bool:
        return all(self.face_dim(self.face([i])) == self.d - 1 for i in range(len(self.rows)))

    def simple(self) -> bool:
        return all(len(a) == self.d for a in self.tight)

    def select(self, x: Point) -> int:
        assert self.feasible(x)
        if x in self.v:
            return self.v.index(x)
        candidates = self.face(self.active(x))
        assert candidates, 'face-preserving selection failed'
        return min(candidates)

    def faces(self):
        # Every nonempty polytope face is determined by a subset of its rows.
        out = {}
        for bits in product((False, True), repeat=len(self.rows)):
            ids = frozenset(i for i, b in enumerate(bits) if b)
            face = self.face(ids)
            if face:
                out.setdefault(face, ids)
        return out


def cube_rows(d: int) -> list[Row]:
    out = []
    for i in range(d):
        a = [0] * d
        a[i] = -1
        out.append((point(a), Q(0)))
        a[i] = 1
        out.append((point(a), Q(1)))
    return out


def verify_rounding(poly: Poly) -> int:
    faces = poly.faces()
    points = set(poly.v)
    for face in faces:
        points.add(tuple(sum((poly.v[i][j] for i in face), Q(0)) / len(face)
                         for j in range(poly.d)))
    for a, b in combinations(poly.v, 2):
        points.add(lerp(a, b, Q(2, 5)))
    for x in points:
        chosen = poly.select(x)
        active = poly.active(x)
        assert active <= poly.tight[chosen]
        # Membership in any face containing x follows from its defining rows.
        for face, ids in faces.items():
            if ids <= active:
                assert chosen in face
    return len(points)


def radial_certificate(outer: Poly, cuts: list[Row], centre: Point,
                       walk: list[int]) -> dict[str, int]:
    """Construct and check the complete piecewise-rational certificate.

    Pairwise affine crossings partition each old edge exactly. Dominance is
    verified at both ends of each cell, hence throughout it by affine linearity.
    No claim about the entire interval is inferred from a sampled midpoint.
    """
    assert outer.feasible(centre)
    cuts = [(point(a), Q(b)) for a, b in cuts]
    slack = [b - dot(a, centre) for a, b in cuts]
    assert all(s > 0 for s in slack)
    inner = Poly(outer.rows + cuts)
    assert all(b in outer.graph[a] for a, b in zip(walk, walk[1:]))
    u, v = outer.v[walk[0]], outer.v[walk[-1]]
    assert u in inner.v and v in inner.v

    def shadow(x: Point) -> Point:
        mu = max([Q(1)] + [dot(a, sub(x, centre)) / s
                          for (a, _), s in zip(cuts, slack)])
        y = tuple(o + (xx - o) / mu for o, xx in zip(centre, x))
        assert inner.feasible(y)
        return y

    supports = {}  # label -> defining rows in the final polytope
    transitions = []
    checkpoints = [u]
    for edge_index, (ia, ib) in enumerate(zip(walk, walk[1:])):
        a, b = outer.v[ia], outer.v[ib]
        functions = [(Q(1), Q(0))] + [
            (dot(c, sub(a, centre)) / s, dot(c, sub(b, a)) / s)
            for (c, _), s in zip(cuts, slack)]
        times = {Q(0), Q(1)}
        for (a0, a1), (b0, b1) in combinations(functions, 2):
            if a1 != b1:
                t = (b0 - a0) / (a1 - b1)
                if 0 < t < 1:
                    times.add(t)
        times = sorted(times)
        assert checkpoints[-1] == shadow(a)
        for left, right in zip(times, times[1:]):
            midpoint = (left + right) / 2
            best = max(range(len(functions)),
                       key=lambda i: functions[i][0] + midpoint * functions[i][1])
            for t in (left, right):
                values = [c + t * m for c, m in functions]
                assert values[best] == max(values)
            p, q = shadow(lerp(a, b, left)), shadow(lerp(a, b, right))
            assert checkpoints[-1] == p
            if best == 0:
                label = ('edge', min(ia, ib), max(ia, ib))
                ids = outer.tight[ia] & outer.tight[ib]
                assert p == lerp(a, b, left) and q == lerp(a, b, right)
            else:
                label = ('cut', best - 1)
                ids = frozenset([len(outer.rows) + best - 1])
            supports[label] = ids
            assert ids <= inner.active(p) and ids <= inner.active(q)
            assert inner.face(ids)
            transitions.append(label)
            checkpoints.append(q)
    assert checkpoints[-1] == v
    if not transitions:
        assert u == v
        return {'cells': 0, 'supports': 0, 'route': 0, 'budget': 0, 'nonvertices': 0}

    rounded = [inner.select(x) for x in checkpoints]
    assert inner.v[rounded[0]] == u and inner.v[rounded[-1]] == v
    for k, label in enumerate(transitions):
        face = inner.face(supports[label])
        assert rounded[k] in face and rounded[k + 1] in face
    labels = sorted(supports)
    faces = {a: inner.face(supports[a]) for a in labels}
    for a in labels:
        if a[0] == 'edge':
            assert inner.face_dim(faces[a]) <= 1
            assert inner.diameter(faces[a]) <= 1
    graph = {a: {b for b in labels if a != b and faces[a] & faces[b]} for a in labels}
    start, end = transitions[0], transitions[-1]
    prev, queue = {start: None}, deque([start])
    while queue and end not in prev:
        a = queue.popleft()
        for b in sorted(graph[a]):
            if b not in prev:
                prev[b] = a
                queue.append(b)
    assert end in prev
    chain = [end]
    while chain[-1] != start:
        chain.append(prev[chain[-1]])
    chain.reverse()
    assert len(chain) == len(set(chain))
    route = [rounded[0]]
    for j, label in enumerate(chain):
        target = (min(faces[label] & faces[chain[j + 1]])
                  if j + 1 < len(chain) else rounded[-1])
        route.extend(inner.path(route[-1], target, faces[label])[1:])
    assert all(b in inner.graph[a] for a, b in zip(route, route[1:]))
    budget = len(walk) - 1 + sum(inner.diameter(inner.face([len(outer.rows) + i]))
                               for i in range(len(cuts)))
    assert len(route) - 1 <= budget
    assert len(supports) <= len(cuts) + len(walk) - 1
    return {'cells': len(transitions), 'supports': len(supports),
            'route': len(route) - 1, 'budget': budget,
            'nonvertices': sum(x not in inner.v for x in checkpoints)}


def sweep_obstruction():
    rows = cube_rows(3)
    a = point([3, 2, 1])
    before = Poly(rows + [(a, Q(11, 2))])
    after = Poly(rows + [(a, Q(9, 2))])
    assert before.irredundant() and after.irredundant()
    assert before.simple() and after.simple()
    assert len(before.v) == len(after.v) == 10
    u, z, v = map(point, [(1, 0, 0), (1, 1, 0), (0, 1, 0)])
    old = [before.v.index(x) for x in (u, z, v)]
    assert all(b in before.graph[a] for a, b in zip(old, old[1:]))
    assert before.distances(old[0])[old[-1]] == 2  # genuinely shortest old path
    assert u in after.v and v in after.v and not after.feasible(z)
    fx, fy, cut = 1, 3, 6
    assert before.face([fx, fy]) and not after.face([fx, fy])
    assert after.face([fx]) and after.face([fy])
    assert after.face([fx, cut]) and after.face([fy, cut])
    p, q = point([1, Q(1, 2), Q(1, 2)]), point([Q(2, 3), 1, Q(1, 2)])
    assert p not in after.v and q not in after.v
    rounded = [after.select(x) for x in (u, p, q, v)]
    for j, row in enumerate((fx, cut, fy)):
        assert rounded[j] in after.face([row]) and rounded[j + 1] in after.face([row])
    certificate = radial_certificate(before, [(a, Q(9, 2))], point([Q(1, 4)] * 3), old)
    # Smaller 5-facet example: persistent faces lose their intersection.
    tetra = [(point([-1, 0, 0]), Q(0)), (point([0, -1, 0]), Q(0)),
             (point([0, 0, -1]), Q(0)), (point([1, 1, 1]), Q(1))]
    t0 = Poly(tetra + [(a, Q(5, 2))])
    t1 = Poly(tetra + [(a, Q(3, 2))])
    assert t0.irredundant() and t1.irredundant() and t0.simple() and t1.simple()
    assert t0.face([2, 3]) and not t1.face([2, 3])
    return {'cube_old_distance': 2, 'cube_final_distance': after.distances(after.v.index(u))[after.v.index(v)],
            'cube_vertices_each': 10, 'all_seven_facets_persist': True,
            'five_facet_intersection_failure': True, 'radial_repair': certificate}


def circuit_carrier_obstruction():
    rows = [(point(a), Q(b)) for a, b in
            [((1, 1), 2), ((1, -1), 2), ((-1, 1), 2), ((-1, -1), 2),
             ((0, 1), 1), ((0, -1), 1)]]
    p = Poly(rows)
    assert p.irredundant() and p.simple() and len(p.v) == 6
    u, v, g = point([-2, 0]), point([2, 0]), point([1, 0])
    assert u in p.v and v in p.v
    zero = [i for i, (a, _) in enumerate(rows) if dot(a, g) == 0]
    assert rank([rows[i][0] for i in zero]) == p.d - 1
    # Every nonzero vector with no larger row support is parallel to g;
    # rank d-1 of zero rows proves support-minimality for full-column-rank A.
    bounds = [(b - dot(a, u)) / dot(a, g) for a, b in rows if dot(a, g) > 0]
    assert min(bounds) == 4
    assert not (p.active(u) & p.active(v))
    assert all(dot(a, point([0, 0])) < b for a, b in rows)
    assert p.distances(p.v.index(u))[p.v.index(v)] == 3
    return {'rows': 6, 'dimension': 2, 'maximal_circuit_length': 1,
            'edge_distance': 3, 'proper_segment_carrier_exists': False}


def dantzig_polars():
    d4 = [point(v) for v in [(0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0),
          (0, 0, 1, 0), (0, 0, 0, 1), (Q(1, 4), Q(-1, 5), Q(1, 4), Q(1, 4)),
          (Q(1, 20), Q(-21, 320), Q(5, 16), Q(5, 16)),
          (Q(1, 4), Q(1, 4), Q(1, 4), Q(-1, 16))]]
    d5 = [point(v) for v in [(-7906, -3779, 3765, 2536, -1617),
          (-2479, -1913, 3968, 8624, 277), (-8136, 213, 4395, 1773, -3361),
          (1815, -3255, 7206, 5567, 1784), (2471, -9137, -2139, -1790, 1623),
          (-183, -2801, 99, 9569, 738), (-1635, 4562, -7049, 2145, -4714),
          (-6786, 4628, -3912, 3784, -1704), (1614, 2189, -3607, -8899, -636),
          (-4161, -60, 1196, -7692, 4700)]]
    for vertices in (d4, d5):
        c = tuple(sum((v[i] for v in vertices), Q(0)) / len(vertices)
                  for i in range(len(vertices[0])))
        yield Poly([(sub(v, c), Q(1)) for v in vertices])


def main():
    report = {'sweep_obstruction': sweep_obstruction(),
              'circuit_carrier_obstruction': circuit_carrier_obstruction()}
    rounding = []
    for name, p in [('cube2', Poly(cube_rows(2))), ('cube3', Poly(cube_rows(3))),
                    ('cube4', Poly(cube_rows(4)))]:
        rounding.append({'name': name, 'vertices': len(p.v), 'checkpoints': verify_rounding(p)})
    for d, p, expected in zip((4, 5), dantzig_polars(), (14, 40)):
        assert len(p.v) == expected and p.irredundant() and p.simple()
        rounding.append({'name': f'Dantzig{d}', 'vertices': len(p.v),
                         'checkpoints': verify_rounding(p)})
    report['rounding'] = rounding
    rng = random.Random(20260909)
    cases = []
    for d in (2, 3, 4):
        outer, centre = Poly(cube_rows(d)), point([Q(1, 2)] * d)
        for trial in range(16):
            start, end = rng.sample(range(len(outer.v)), 2)
            cuts = []
            for _ in range(trial % 4):
                a = point([rng.randrange(-3, 4) for _ in range(d)])
                if not any(a):
                    a = point([1] + [0] * (d - 1))
                bound = max(dot(a, outer.v[start]), dot(a, outer.v[end]),
                            dot(a, centre) + sum(map(abs, a), Q(0)) / 3)
                cuts.append((a, bound))
            survivors = [i for i, v in enumerate(outer.v) if all(dot(a, v) <= b for a, b in cuts)]
            assert len(survivors) >= 2
            assert start in survivors and end in survivors
            walk = [start]
            # Repeated edges and removed vertices deliberately allowed.
            for _ in range(8):
                walk.append(rng.choice(sorted(outer.graph[walk[-1]])))
            walk.extend(outer.path(walk[-1], end)[1:])
            cases.append(radial_certificate(outer, cuts, centre, walk))
    report['radial_multi_cut'] = {'cases': len(cases),
        'cells': sum(x['cells'] for x in cases),
        'nonvertex_checkpoint_occurrences': sum(x['nonvertices'] for x in cases),
        'max_distinct_supports': max(x['supports'] for x in cases),
        'all_constructed_routes_within_final_face_budget': True}
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
