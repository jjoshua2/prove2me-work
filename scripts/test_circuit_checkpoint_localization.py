#!/usr/bin/env python3
"""Exact rational regressions; not a Lean proof or a novelty claim.

Run from any directory. Only the Python standard library is required.
Every assertion uses Fraction arithmetic. The JSON summary is deterministic.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from collections import deque
from dataclasses import dataclass, field
from fractions import Fraction as Q
from pathlib import Path

Vector = tuple[Q, ...]

def dot(a: Vector, b: Vector) -> Q:
    return sum((x * y for x, y in zip(a, b, strict=True)), Q(0))

def matrix_rank(rows: list[Vector], d: int) -> int:
    matrix = [list(row) for row in rows]
    r = 0
    for c in range(d):
        pivot = next((k for k in range(r, len(matrix)) if matrix[k][c]), None)
        if pivot is None:
            continue
        matrix[r], matrix[pivot] = matrix[pivot], matrix[r]
        scale = matrix[r][c]
        matrix[r] = [v / scale for v in matrix[r]]
        for k in range(r + 1, len(matrix)):
            f = matrix[k][c]
            if f:
                matrix[k] = [v - f * w for v, w in zip(matrix[k], matrix[r], strict=True)]
        r += 1
        if r == len(matrix):
            break
    return r

def solve_square(rows: list[Vector], rhs: list[Q]) -> Vector | None:
    d = len(rows)
    m = [list(row) + [b] for row, b in zip(rows, rhs, strict=True)]
    for c in range(d):
        pivot = next((k for k in range(c, d) if m[k][c]), None)
        if pivot is None:
            return None
        m[c], m[pivot] = m[pivot], m[c]
        f = m[c][c]
        m[c] = [v / f for v in m[c]]
        for k in range(d):
            if k != c and m[k][c]:
                f = m[k][c]
                m[k] = [v - f * w for v, w in zip(m[k], m[c], strict=True)]
    return tuple(m[k][-1] for k in range(d))

@dataclass
class Poly:
    name: str
    d: int
    a: list[Vector]
    b: list[Q]
    cache: dict[tuple[int, ...], int] = field(default_factory=dict)

    def __post_init__(self) -> None:
        assert len(self.a) == len(self.b)
        assert all(len(row) == self.d for row in self.a)
        assert matrix_rank(self.a, self.d) == self.d

    @property
    def n(self) -> int:
        return len(self.a)

    def rank(self, indices: set[int]) -> int:
        key = tuple(sorted(indices))
        if key not in self.cache:
            self.cache[key] = matrix_rank([self.a[i] for i in key], self.d)
        return self.cache[key]

    def feasible(self, x: Vector) -> bool:
        return all(dot(row, x) <= b for row, b in zip(self.a, self.b, strict=True))

    def active(self, x: Vector) -> set[int]:
        return {i for i, row in enumerate(self.a) if any(row) and dot(row, x) == self.b[i]}

    def face_dim(self, x: Vector) -> int:
        return self.d - self.rank(self.active(x))

    def vertices(self) -> list[Vector]:
        found: set[Vector] = set()
        for indices in itertools.combinations(range(self.n), self.d):
            x = solve_square([self.a[i] for i in indices], [self.b[i] for i in indices])
            if x is not None and self.feasible(x):
                found.add(x)
        return sorted(found)

    def pair(self, x: Vector, y: Vector) -> dict[str, int | bool]:
        assert x != y and self.feasible(x) and self.feasible(y)
        g = tuple(v - u for u, v in zip(x, y, strict=True))
        X, Y = self.active(x), self.active(y)
        C, S, T = X & Y, X - Y, Y - X
        Z = {i for i, row in enumerate(self.a) if any(row) and dot(row, g) == 0}
        assert not (S & T or S & Z or T & Z)
        assert C <= Z
        h = self.d - self.rank(C)
        p, q = self.d - self.rank(X), self.d - self.rank(Y)
        r = self.rank(Z)
        assert r <= self.d - 1
        delta = self.d - 1 - r
        active_delta = self.d - 1 - self.rank(C)
        assert active_delta == h - 1
        assert p <= h and q <= h
        assert h <= len(S) + p and h <= len(T) + q
        lhs = 2 * h + self.d
        rhs = self.n + p + q + delta + 1
        assert lhs <= rhs
        # All surplus has an exact nonnegative decomposition.
        slack_parts = [len(S) - h + p, len(T) - h + q,
                       len(Z) - r, self.n - len(S | T | Z)]
        assert min(slack_parts) >= 0
        assert rhs - lhs == sum(slack_parts)
        circuit = r == self.d - 1
        if circuit:
            assert 2 * h + self.d <= self.n + p + q + 1
        if circuit and p == q == 0:
            assert 2 * h + self.d <= self.n + 1
        maximal = any(dot(self.a[i], g) > 0 for i in Y)
        return dict(h=h, p=p, q=q, neutral_rank=r, direction_defect=delta,
                    active_defect=active_delta, circuit=circuit, maximal=maximal,
                    lhs=lhs, rhs=rhs, slack=rhs - lhs)

def unit(d: int, i: int, scale: int = 1) -> Vector:
    return tuple(Q(scale if j == i else 0) for j in range(d))

def cube(d: int) -> tuple[Poly, list[Vector]]:
    a = [unit(d, i, s) for i in range(d) for s in (-1, 1)]
    b = [Q(0), Q(1)] * d
    v = [tuple(map(Q, bits)) for bits in itertools.product((0, 1), repeat=d)]
    return Poly(f"cube_{d}", d, a, b), v

def simplex(d: int) -> tuple[Poly, list[Vector]]:
    a = [unit(d, i, -1) for i in range(d)] + [tuple([Q(1)] * d)]
    b = [Q(0)] * d + [Q(1)]
    return Poly(f"simplex_{d}", d, a, b), [tuple([Q(0)] * d)] + [unit(d, i) for i in range(d)]

def sheared_cube(d: int) -> tuple[Poly, list[Vector], list[tuple[int, ...]]]:
    a: list[Vector] = []
    b: list[Q] = []
    for i in range(d - 1):
        a.append(unit(d, i, -1)); b.append(Q(0))
        a.append(tuple(v - w for v, w in zip(unit(d, i), unit(d, d - 1), strict=True)))
        b.append(Q(1))
    a.extend([unit(d, d - 1, -1), unit(d, d - 1)])
    b.extend([Q(0), Q(1)])
    labels = list(itertools.product((0, 1), repeat=d))
    vertices = [tuple(Q(bit * (1 + bits[-1])) for bit in bits[:-1]) + (Q(bits[-1]),)
                for bits in labels]
    return Poly(f"sheared_cube_{d}", d, a, b), vertices, labels

def generated_points(vertices: list[Vector], seed: int) -> list[Vector]:
    rng = random.Random(seed)
    vs = vertices if len(vertices) <= 24 else rng.sample(vertices, 24)
    points = set(vs)
    for _ in range(30):
        x, y = rng.choice(vs), rng.choice(vs)
        t = rng.choice([Q(1, 2), Q(1, 3), Q(2, 3)])
        points.add(tuple((1 - t) * u + t * v for u, v in zip(x, y, strict=True)))
    points.add(tuple(sum((x[j] for x in vertices), Q(0)) / len(vertices)
                     for j in range(len(vertices[0]))))
    return sorted(points)

def main() -> dict:
    digest = hashlib.sha256()
    counts = dict(pairs=0, circuits=0, vertex_circuit_pairs=0,
                  nonvertex_pairs=0, positive_direction_defect_pairs=0,
                  tight_general_bound_pairs=0)
    models: list[tuple[Poly, list[Vector]]] = []
    sharp = []
    for d in range(1, 9):
        P, vertices, labels = sheared_cube(d)
        assert all(P.feasible(v) and P.face_dim(v) == 0 for v in vertices)
        # Exact strict feasibility and row-by-row irredundancy witnesses.
        center = tuple([Q(1, 2)] * d)
        assert all(dot(a, center) < b for a, b in zip(P.a, P.b, strict=True))
        for i in range(P.n):
            w = [Q(0)] * d
            if i < 2 * (d - 1):
                w[i // 2] = Q(-1) if i % 2 == 0 else Q(2)
            elif i == 2 * (d - 1):
                w[-1] = Q(-1, 2)
            else:
                w[-1] = Q(2)
            w = tuple(w)
            assert dot(P.a[i], w) > P.b[i]
            assert all(dot(P.a[j], w) <= P.b[j] for j in range(P.n) if j != i)
        if d <= 4:
            assert P.vertices() == sorted(vertices)
        route = [tuple([Q(0)] * d), tuple([Q(1)] * d)]
        for j in range(d - 1):
            w = list(route[-1]); w[j] = Q(2); route.append(tuple(w))
        step_data = [P.pair(x, y) for x, y in zip(route, route[1:])]
        assert all(r["circuit"] and r["maximal"] for r in step_data)
        assert P.face_dim(route[0]) == P.face_dim(route[-1]) == 0
        assert [r["h"] for r in step_data] == list(range(d, 0, -1))
        first = step_data[0]
        assert first["h"] == d and first["p"] == 0 and first["q"] == d - 1
        assert first["slack"] == 0 and first["active_defect"] == d - 1
        # A face-preserving selector yields an explicit short edge walk here:
        # keep active upper coordinates and put every remaining coordinate at zero.
        rounded = [route[0]]
        for k in range(1, d + 1):
            rounded.append(tuple(Q(2 if j < k - 1 else 0) for j in range(d - 1)) + (Q(1),))
        assert rounded[0] == route[0] and rounded[-1] == route[-1]
        for x, v in zip(route, rounded, strict=True):
            assert P.feasible(v) and P.face_dim(v) == 0
            assert P.active(x) <= P.active(v)
        for x, y in zip(rounded, rounded[1:]):
            assert x != y and P.rank(P.active(x) & P.active(y)) == d - 1
        # Independent cube-label neighbor construction, with geometric edge checks.
        index = {bits: i for i, bits in enumerate(labels)}
        graph = [[] for _ in labels]
        checked_edges = 0
        for i, bits in enumerate(labels):
            for j in range(d):
                neighbor = list(bits); neighbor[j] = 1 - neighbor[j]
                k = index[tuple(neighbor)]
                graph[i].append(k)
                if i < k:
                    assert P.rank(P.active(vertices[i]) & P.active(vertices[k])) == d - 1
                    checked_edges += 1
        start = index[tuple([0] * d)]; goal = index[tuple([1] * d)]
        dist = {start: 0}; queue = deque([start])
        while queue:
            i = queue.popleft()
            for j in graph[i]:
                if j not in dist:
                    dist[j] = dist[i] + 1; queue.append(j)
        assert len(dist) == 2 ** d and dist[goal] == d
        sharp.append(dict(d=d, n=P.n, vertices=len(vertices), checked_edges=checked_edges,
                          circuit_route_length=d, graph_distance=dist[goal],
                          face_preserving_rounding_length=len(rounded)-1,
                          first_step=first, carrier_dimensions=[r["h"] for r in step_data]))
        if d <= 6:
            models.extend([(P, vertices), cube(d), simplex(d)])
    # A maximal vertex-to-vertex circuit that is not an edge.
    a = [(-1, 0), (0, -1), (1, 0), (0, 1), (1, -1), (-1, 1)]
    H = Poly("hexagon", 2, [tuple(map(Q, row)) for row in a], list(map(Q, [0, 0, 3, 3, 2, 2])))
    hv = H.vertices()
    assert len(hv) == 6
    hex_result = H.pair((Q(0), Q(0)), (Q(3), Q(3)))
    assert hex_result["circuit"] and hex_result["maximal"] and hex_result["h"] == 2
    models.append((H, hv))
    # Small exact vertex enumeration for bounded boxes with additional cuts.
    rng = random.Random(960910)
    for d in (2, 3, 4):
        for trial in range(2):
            P, _ = cube(d)
            P.name = f"cut_box_{d}_{trial}"
            center = tuple([Q(1, 2)] * d)
            for _ in range(3):
                row = tuple(Q(rng.randint(-3, 3)) for _ in range(d))
                if not any(row):
                    row = unit(d, 0)
                P.a.append(row); P.b.append(dot(row, center) + Q(rng.randint(1, 4), 3))
            P.cache.clear()
            vs = P.vertices()
            assert vs
            models.append((P, vs))
    model_summary = []
    for model_no, (P, vertices) in enumerate(models):
        points = generated_points(vertices, model_no)
        pairs = list(itertools.combinations(range(len(points)), 2))
        rng = random.Random(71 + model_no)
        if len(pairs) > 350:
            pairs = sorted(rng.sample(pairs, 350))
        for i, j in pairs:
            r = P.pair(points[i], points[j])
            counts["pairs"] += 1
            counts["circuits"] += int(r["circuit"])
            counts["vertex_circuit_pairs"] += int(r["circuit"] and r["p"] == r["q"] == 0)
            counts["nonvertex_pairs"] += int(r["p"] > 0 or r["q"] > 0)
            counts["positive_direction_defect_pairs"] += int(r["direction_defect"] > 0)
            counts["tight_general_bound_pairs"] += int(r["slack"] == 0)
            record = [P.name, [str(t) for t in points[i]], [str(t) for t in points[j]], r]
            digest.update((json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n").encode())
        model_summary.append(dict(name=P.name, d=P.d, n=P.n, vertices=len(vertices),
                                  sampled_points=len(points), pairs=len(pairs)))
    return dict(status="all_exact_assertions_passed", arithmetic="fractions.Fraction",
                proof_status="computational_regressions_not_Lean_verification",
                counts=counts, cases_sha256=digest.hexdigest(), models=model_summary,
                balanced_sharp_family=sharp, hexagon=hex_result)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = main()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    else:
        print(text, end="")
