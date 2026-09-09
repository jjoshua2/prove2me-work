#!/usr/bin/env python3
"""Exact constructive regressions for simultaneous clipping with NEW endpoints.

Uses rational arithmetic and exhaustive vertex-base enumeration from PR #50.
Finite computations are not Lean hull formalizations. No polynomial diameter
hypothesis is inferred from these examples. Run with Python's standard library.
"""
from __future__ import annotations

from collections import deque
from fractions import Fraction as Q
from itertools import combinations
import json
import random

from test_face_preserving_checkpoints import Poly, Point, Row, cube_rows, dot, lerp, point, sub


class FullClip:
    def __init__(self, dimension: int, cuts: list[Row]):
        self.outer = Poly(cube_rows(dimension))
        self.cuts = [(point(a), Q(b)) for a, b in cuts]
        self.centre = point([Q(1, 2)] * dimension)
        self.slack = [b - dot(a, self.centre) for a, b in self.cuts]
        assert all(s > 0 for s in self.slack), 'centre must be strictly feasible'
        self.inner = Poly(self.outer.rows + self.cuts)
        self.offset = len(self.outer.rows)
        self.cut_faces = [self.inner.face([self.offset + i]) for i in range(len(cuts))]
        self.cut_cost = [self.inner.diameter(face) for face in self.cut_faces]
        self.outer_diameter = self.outer.diameter()
        self.inner_diameter = self.inner.diameter()
        assert self.inner_diameter <= self.outer_diameter + sum(self.cut_cost)
        self.survivors = len(set(self.outer.v) & set(self.inner.v))

    def shadow(self, x: Point) -> Point:
        mu = max([Q(1)] + [dot(a, sub(x, self.centre)) / s
                          for (a, _), s in zip(self.cuts, self.slack)])
        y = tuple(o + (xx - o) / mu for o, xx in zip(self.centre, x))
        assert self.inner.feasible(y)
        return y

    def attach(self, u: Point) -> tuple[int, int | None]:
        if u in self.outer.v:
            return self.outer.v.index(u), None
        active = [i for i, (a, b) in enumerate(self.cuts) if dot(a, u) == b]
        assert active, 'a new vertex must lie on an added cut'
        i = min(active)
        a, b = self.cuts[i]
        j = max(range(len(self.outer.v)), key=lambda j: dot(a, self.outer.v[j]))
        assert dot(a, self.outer.v[j]) >= b
        return j, i

    def certify_pair(self, ui: int, vi: int) -> dict[str, int]:
        p, q = self.inner.v[ui], self.inner.v[vi]
        a, ai = self.attach(p)
        c, ci = self.attach(q)
        walk = self.outer.path(a, c)
        length = len(walk) - 1
        segments = []
        if p != self.outer.v[a]:
            segments.append((p, self.outer.v[a], None, ai))
        for x, y in zip(walk, walk[1:]):
            label = ('edge', min(x, y), max(x, y))
            segments.append((self.outer.v[x], self.outer.v[y], label, None))
        if self.outer.v[c] != q:
            segments.append((self.outer.v[c], q, None, ci))
        checkpoints = [p]
        labels = []
        supports = {}
        cells = 0
        for x, y, edge_label, cut_attachment in segments:
            assert x != y
            functions = [(Q(1), Q(0))] + [
                (dot(a, sub(x, self.centre)) / s, dot(a, sub(y, x)) / s)
                for (a, _), s in zip(self.cuts, self.slack)]
            times = {Q(0), Q(1)}
            for (a0, a1), (b0, b1) in combinations(functions, 2):
                if a1 != b1:
                    t = (b0 - a0) / (a1 - b1)
                    if 0 < t < 1:
                        times.add(t)
            times = sorted(times)
            assert checkpoints[-1] == self.shadow(x)
            for left, right in zip(times, times[1:]):
                middle = (left + right) / 2
                best = max(range(len(functions)),
                           key=lambda i: functions[i][0] + middle * functions[i][1])
                # Whole-cell certification: all differences are affine and the
                # chosen function dominates at BOTH endpoints, not just a sample.
                for t in (left, right):
                    values = [a + b * t for a, b in functions]
                    assert values[best] == max(values)
                r, s = self.shadow(lerp(x, y, left)), self.shadow(lerp(x, y, right))
                assert checkpoints[-1] == r
                if best:
                    label = ('cut', best - 1)
                    ids = frozenset([self.offset + best - 1])
                elif edge_label is not None:
                    label = edge_label
                    ids = self.outer.tight[label[1]] & self.outer.tight[label[2]]
                    assert r == lerp(x, y, left) and s == lerp(x, y, right)
                else:
                    # The outward attachment stays outside/on its source cut.
                    # At unit scale it is on that very cut, never a new edge charge.
                    assert cut_attachment is not None
                    normal, bound = self.cuts[cut_attachment]
                    assert dot(normal, x) >= bound and dot(normal, y) >= bound
                    assert dot(normal, r) == bound and dot(normal, s) == bound
                    label = ('cut', cut_attachment)
                    ids = frozenset([self.offset + cut_attachment])
                assert ids <= self.inner.active(r) and ids <= self.inner.active(s)
                supports[label] = ids
                labels.append(label)
                checkpoints.append(s)
                cells += 1
        assert checkpoints[-1] == q
        budget = length + sum(self.cut_cost)
        assert length <= self.outer_diameter
        if not labels:
            assert p == q
            return {'cells': 0, 'new_endpoints': int(ai is not None) + int(ci is not None),
                    'zero_outer_walk': int(length == 0), 'nonvertices': 0,
                    'route': 0, 'budget': budget, 'supports': 0}
        rounded = [self.inner.select(x) for x in checkpoints]
        assert rounded[0] == ui and rounded[-1] == vi
        faces = {label: self.inner.face(ids) for label, ids in supports.items()}
        for j, label in enumerate(labels):
            assert rounded[j] in faces[label] and rounded[j + 1] in faces[label]
        for label, face in faces.items():
            if label[0] == 'edge':
                assert self.inner.face_dim(face) <= 1 and self.inner.diameter(face) <= 1
        assert sum(k[0] == 'edge' for k in faces) <= length
        graph = {a: {b for b in faces if a != b and faces[a] & faces[b]} for a in faces}
        start, end = labels[0], labels[-1]
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
        route = [ui]
        for j, label in enumerate(chain):
            target = min(faces[label] & faces[chain[j + 1]]) if j + 1 < len(chain) else vi
            route.extend(self.inner.path(route[-1], target, faces[label])[1:])
        assert route[-1] == vi
        assert all(b in self.inner.graph[a] for a, b in zip(route, route[1:]))
        assert len(route) - 1 <= budget
        return {'cells': cells, 'new_endpoints': int(ai is not None) + int(ci is not None),
                'zero_outer_walk': int(length == 0),
                'nonvertices': sum(x not in self.inner.v for x in checkpoints),
                'route': len(route) - 1, 'budget': budget, 'supports': len(faces)}


def summary(records: list[dict[str, int]]) -> dict[str, int | bool]:
    return {'pairs': len(records), 'cells': sum(r['cells'] for r in records),
            'new_endpoint_occurrences': sum(r['new_endpoints'] for r in records),
            'zero_length_outer_walks': sum(r['zero_outer_walk'] for r in records),
            'nonvertex_checkpoint_occurrences': sum(r['nonvertices'] for r in records),
            'max_supports': max((r['supports'] for r in records), default=0),
            'all_routes_constructed_within_budget': True}


def main() -> None:
    nested = []
    nested_records = []
    for d in (2, 3, 4):
        cuts = [(a, Q(-1, 4) if b == 0 else Q(3, 4)) for a, b in cube_rows(d)]
        case = FullClip(d, cuts)
        assert case.survivors == 0
        pairs = list(combinations(range(len(case.inner.v)), 2))
        records = [case.certify_pair(*pair) for pair in pairs]
        assert all(r['new_endpoints'] == 2 for r in records)
        nested_records.extend(records)
        nested.append({'dimension': d, 'outer_vertices': len(case.outer.v),
                       'inner_vertices': len(case.inner.v), 'surviving_outer_vertices': 0,
                       'inner_diameter': case.inner_diameter, **summary(records)})
    rng = random.Random(20260909)
    random_records = []
    instances = 0
    for d in (2, 3, 4):
        centre = point([Q(1, 2)] * d)
        for trial in range(10):
            cuts = []
            for _ in range(trial % 4):
                a = point([rng.randrange(-3, 4) for _ in range(d)])
                if not any(a):
                    a = point([1] + [0] * (d - 1))
                b = dot(a, centre) + sum(map(abs, a), Q(0)) * Q(rng.randrange(1, 4), 8)
                cuts.append((a, b))
            if trial % 3 == 1 and cuts:
                cuts.append(cuts[0])
            if trial % 3 == 2:
                cuts.append((point([0] * d), Q(1)))
            case = FullClip(d, cuts)
            pairs = list(combinations(range(len(case.inner.v)), 2))
            rng.shuffle(pairs)
            random_records.extend(case.certify_pair(*pair) for pair in pairs[:12])
            random_records.append(case.certify_pair(0, 0))
            instances += 1
    print(json.dumps({'no_surviving_vertices': nested,
                      'no_surviving_vertices_total': summary(nested_records),
                      'seeded_general_clips': {'instances': instances, **summary(random_records)}},
                     indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
