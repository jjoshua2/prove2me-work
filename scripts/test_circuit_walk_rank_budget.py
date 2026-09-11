#!/usr/bin/env python3
"""Deterministic exact-rational tests for circuit-walk rank accounting.

These are finite regression certificates, NOT a Lean or Prove2Me verdict.
The module is standalone and requires only the Python standard library.
All checks are explicit (they still execute under python -O).
"""
from __future__ import annotations

import argparse
from collections import deque
from dataclasses import dataclass, field
from fractions import Fraction as Q
from functools import reduce
from itertools import combinations, product
import hashlib
import json
from math import gcd, lcm
from pathlib import Path
import random
from typing import Sequence

Vector = tuple[Q, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def dot(a: Sequence[Q], b: Sequence[Q]) -> Q:
    return sum((u * v for u, v in zip(a, b, strict=True)), Q(0))


def sub(y: Vector, x: Vector) -> Vector:
    return tuple(v - u for u, v in zip(x, y, strict=True))


def rref(rows: Sequence[Sequence[Q]], d: int) -> tuple[list[list[Q]], list[int]]:
    m = [list(map(Q, row)) for row in rows]
    pivots: list[int] = []
    for c in range(d):
        k = next((i for i in range(len(pivots), len(m)) if m[i][c]), None)
        if k is None:
            continue
        r = len(pivots)
        m[r], m[k] = m[k], m[r]
        factor = m[r][c]
        m[r] = [v / factor for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                factor = m[i][c]
                m[i] = [a - factor * b for a, b in zip(m[i], m[r], strict=True)]
        pivots.append(c)
        if len(pivots) == len(m):
            break
    return m, pivots


def rank(rows: Sequence[Sequence[Q]], d: int) -> int:
    return len(rref(rows, d)[1])


def normalize(g: Sequence[Q]) -> Vector:
    den = lcm(*(v.denominator for v in g))
    ints = [int(v * den) for v in g]
    factor = reduce(gcd, map(abs, ints), 0)
    require(factor > 0, 'zero circuit direction')
    return tuple(Q(v // factor) for v in ints)


def unit(d: int, i: int, sign: int = 1) -> Vector:
    return tuple(Q(sign if j == i else 0) for j in range(d))


@dataclass
class Poly:
    name: str
    d: int
    a: list[Vector]
    b: list[Q]
    _rank_cache: dict[tuple[int, ...], int] = field(default_factory=dict)
    _directions: list[Vector] | None = None

    def __post_init__(self) -> None:
        self.a = [tuple(map(Q, row)) for row in self.a]
        self.b = list(map(Q, self.b))
        require(self.d >= 1 and len(self.a) == len(self.b), 'malformed model')
        require(all(len(row) == self.d for row in self.a), 'row dimension mismatch')
        require(rank(self.a, self.d) == self.d, 'total row map must be injective')

    @property
    def n(self) -> int:
        return len(self.a)

    def row_rank(self, indices: set[int]) -> int:
        key = tuple(sorted(indices))
        if key not in self._rank_cache:
            self._rank_cache[key] = rank([self.a[i] for i in key], self.d)
        return self._rank_cache[key]

    def feasible(self, x: Vector) -> bool:
        return all(dot(a, x) <= b for a, b in zip(self.a, self.b, strict=True))

    def active(self, x: Vector) -> set[int]:
        return {i for i, a in enumerate(self.a) if any(a) and dot(a, x) == self.b[i]}

    def nullity(self, x: Vector) -> int:
        return self.d - self.row_rank(self.active(x))

    def circuit_directions(self) -> list[Vector]:
        if self._directions is not None:
            return self._directions
        out: set[Vector] = set()
        for selected in combinations(range(self.n), self.d - 1):
            matrix, pivots = rref([self.a[i] for i in selected], self.d)
            if len(pivots) != self.d - 1:
                continue
            free = next(j for j in range(self.d) if j not in pivots)
            g = [Q(0)] * self.d
            g[free] = Q(1)
            for i, c in enumerate(pivots):
                g[c] = -matrix[i][free]
            v = normalize(g)
            out.add(v)
            out.add(tuple(-t for t in v))
        self._directions = sorted(out)
        require(bool(out), 'circuit enumeration found no direction')
        return self._directions

    def maximal_step(self, x: Vector, g: Vector) -> Vector | None:
        slopes = [dot(row, g) for row in self.a]
        slack = [b - dot(row, x) for row, b in zip(self.a, self.b, strict=True)]
        require(min(slack) >= 0, 'infeasible starting point')
        if any(s == 0 and c > 0 for s, c in zip(slack, slopes, strict=True)):
            return None
        caps = [s / c for s, c in zip(slack, slopes, strict=True) if c > 0]
        if not caps:  # An unbounded direction has no maximal finite step.
            return None
        t = min(caps)
        require(t > 0, 'nonpositive step after feasibility check')
        return tuple(u + t * v for u, v in zip(x, g, strict=True))

    def transitions(self, x: Vector, preserve_active: bool = False) -> list[Vector]:
        out: set[Vector] = set()
        X = self.active(x)
        for g in self.circuit_directions():
            if preserve_active and any(dot(self.a[i], g) != 0 for i in X):
                continue
            y = self.maximal_step(x, g)
            if y is not None:
                out.add(y)
        return sorted(out)

    def vertices(self) -> list[Vector]:
        result: set[Vector] = set()
        for selected in combinations(range(self.n), self.d):
            rows = [self.a[i] + (self.b[i],) for i in selected]
            matrix, pivots = rref(rows, self.d)
            if len(pivots) != self.d:
                continue
            x = tuple(matrix[i][-1] for i in range(self.d))
            if self.feasible(x):
                result.add(x)
        return sorted(result)

    def step_record(self, x: Vector, y: Vector) -> dict:
        require(self.feasible(x) and self.feasible(y), 'infeasible endpoint')
        X, Y = self.active(x), self.active(y)
        p, q = self.d - self.row_rank(X), self.d - self.row_rank(Y)
        h = self.d - self.row_rank(X & Y)
        require(h >= max(p, q), 'negative rank loss/gain')
        lost, gained = h - p, h - q
        require(lost + p == gained + q, 'local conservation failed')
        if x == y:
            require(lost == gained == 0, 'padding must have zero charge')
            return dict(p=p, q=q, h=h, lost=0, gained=0, genuine=0, slack=0,
                        parts=[0, 0, 0, 0])
        g = sub(y, x)
        Z = {i for i, a in enumerate(self.a) if any(a) and dot(a, g) == 0}
        S, T = X - Y, Y - X
        zr = self.row_rank(Z)
        require(zr == self.d - 1, 'displacement is not a row circuit')
        require(any(dot(self.a[i], g) > 0 for i in Y), 'step not maximal')
        require(gained >= 1, 'maximality failed to gain rank')
        require(not (S & T or S & Z or T & Z), 'row partition overlap')
        parts = [len(S) - lost, len(T) - gained, len(Z) - zr,
                 self.n - len(S | T | Z)]
        require(min(parts) >= 0, 'negative localization slack component')
        sigma = sum(parts)
        e = self.n - self.d
        require(lost + gained + sigma == e + 1, 'exact local budget failed')
        require(q + 1 <= h and h <= e + p, 'maximal-step progress failed')
        return dict(p=p, q=q, h=h, lost=lost, gained=gained, genuine=1,
                    slack=sigma, parts=parts)

    def walk_record(self, w: list[Vector]) -> dict:
        require(bool(w) and all(self.feasible(x) for x in w), 'invalid walk')
        records = [self.step_record(x, y) for x, y in zip(w, w[1:])]
        N = sum(r['genuine'] for r in records)
        lost = sum(r['lost'] for r in records)
        gained = sum(r['gained'] for r in records)
        sigma = sum(r['slack'] for r in records)
        p0, pL, e = self.nullity(w[0]), self.nullity(w[-1]), self.n - self.d
        require(lost + p0 == gained + pL, 'whole-walk conservation failed')
        require(lost + gained + sigma == N * (e + 1), 'whole-walk slack budget failed')
        require(2 * gained + pL + sigma == N * (e + 1) + p0,
                'endpoint-corrected exact identity failed')
        require(gained >= N, 'missing mandatory maximal-step gains')
        if p0 == pL == 0:
            require(lost == gained and N <= lost <= N * (e + 1) // 2,
                    'vertex-to-vertex half-budget failed')
        if p0 == 0:
            genuine_prefix = 0
            for r in records:
                genuine_prefix += r['genuine']
                require(r['q'] <= genuine_prefix * max(e - 1, 0), 'prefix bound failed')
            if all(r['lost'] <= 1 for r in records):
                require(all(r['p'] == r['q'] == 0 and
                            (not r['genuine'] or r['h'] == 1) for r in records),
                        'rank-one edge certificate failed')
            if e <= 1:
                require(all(not r['genuine'] or r['h'] == 1 for r in records),
                        'small-excess zero-overhead refinement failed')
        return dict(steps=len(w)-1, genuine=N, source_nullity=p0, target_nullity=pL,
                    lost=lost, gained=gained, slack=sigma,
                    max_checkpoint_nullity=max((self.nullity(x) for x in w), default=0),
                    max_carrier_dimension=max((r['h'] for r in records), default=0),
                    rank_one_certificate=all(r['lost'] <= 1 for r in records),
                    nonedge_steps=sum(r['genuine'] and
                        (r['p'] != 0 or r['q'] != 0 or r['h'] != 1) for r in records))


def cube(d: int) -> Poly:
    return Poly(f'cube_{d}', d, [unit(d, i, s) for i in range(d) for s in (-1, 1)],
                [Q(0), Q(1)] * d)


def simplex(d: int) -> Poly:
    return Poly(f'simplex_{d}', d, [unit(d, i, -1) for i in range(d)] + [(Q(1),)*d],
                [Q(0)]*d + [Q(1)])


def sheared_cube(d: int) -> Poly:
    a, b = [], []
    for i in range(d-1):
        a.extend([unit(d, i, -1), sub(unit(d, i), unit(d, d-1))])
        b.extend([Q(0), Q(1)])
    a.extend([unit(d, d-1, -1), unit(d, d-1)])
    b.extend([Q(0), Q(1)])
    return Poly(f'sheared_cube_{d}', d, a, b)


def thin_diagonal_box(d: int) -> Poly:
    # n=3d-1 and the diagonal is one maximal vertex-to-vertex circuit.
    a = [unit(d, i, s) for i in range(d) for s in (-1, 1)]
    b = [Q(0), Q(3)] * d
    for i in range(d-1):
        a.append(sub(unit(d, i), unit(d, i+1)))
        b.append(Q(1))
    return Poly(f'sharp_diagonal_box_{d}', d, a, b)


def polygon_from_ccw(name: str, vertices: list[Vector]) -> Poly:
    a, b = [], []
    for x, y in zip(vertices, vertices[1:] + vertices[:1], strict=True):
        dx, dy = sub(y, x)
        normal = (dy, -dx)
        a.append(normal)
        b.append(dot(normal, x))
    P = Poly(name, 2, a, b)
    require(all(P.feasible(x) and P.nullity(x) == 0 for x in vertices),
            'invalid strictly convex polygon')
    # Every edge has exactly its two listed vertices on its supporting line.
    for row, rhs in zip(P.a, P.b, strict=True):
        require(sum(dot(row, v) == rhs for v in vertices) == 2,
                'polygon has a collinear or redundant edge')
    return P


def polygon_rank_barrier(m: int) -> tuple[Poly, list[Vector]]:
    require(m >= 1, 'm must be positive')
    xs = [Q(2*k+1, 2) for k in range(-m, m)]
    bottom = [(x, -(Q(m*m)-x*x)) for x in xs]
    top = [(x, Q(m*m)-x*x) for x in reversed(xs)]
    vs = [(Q(-m), Q(0))] + bottom + [(Q(m), Q(0))] + top
    return polygon_from_ccw(f'polygon_barrier_{m}', vs), vs


def graph_distance(P: Poly, vertices: list[Vector], u: Vector, v: Vector) -> int:
    index = {x: i for i, x in enumerate(vertices)}
    active = [P.active(x) for x in vertices]
    graph: list[list[int]] = [[] for _ in vertices]
    for i, j in combinations(range(len(vertices)), 2):
        if P.row_rank(active[i] & active[j]) == P.d - 1:
            graph[i].append(j)
            graph[j].append(i)
    seen = {index[u]: 0}
    queue = deque([index[u]])
    while queue:
        i = queue.popleft()
        if i == index[v]:
            return seen[i]
        for j in graph[i]:
            if j not in seen:
                seen[j] = seen[i] + 1
                queue.append(j)
    raise ValueError('graph disconnected')


def main() -> dict:
    rng = random.Random(2026091103)
    digest = hashlib.sha256()
    counts = dict(walks=0, genuine_steps=0, padding_steps=0,
                  vertex_to_vertex_walks=0, nonvertex_start_walks=0,
                  walks_with_nonvertex_checkpoints=0, rank_one_certificates=0)
    models: list[Poly] = []
    for d in range(1, 5):
        models.extend([simplex(d), cube(d), sheared_cube(d)])
    for d in (2, 3, 4):
        for trial in range(2):
            P = cube(d)
            P.name = f'cut_cube_{d}_{trial}'
            center = (Q(1, 2),) * d
            for _ in range(2):
                row = tuple(Q(rng.randint(-2, 2)) for _ in range(d))
                if not any(row):
                    row = unit(d, 0)
                P.a.append(row)
                P.b.append(dot(row, center) + Q(rng.randint(1, 3), 3))
            models.append(P)
    redundant = cube(2)
    redundant.name = 'cube_2_duplicate_and_zero_rows'
    redundant.a.extend([redundant.a[0], (Q(0), Q(0))])
    redundant.b.extend([Q(0), Q(0)])
    models.append(redundant)
    model_summary = []
    for P in models:
        vertices = P.vertices()
        require(bool(vertices), 'bounded model has no enumerated vertices')
        for trial in range(12):
            start = rng.choice(vertices)
            if trial % 3 == 0:
                other = rng.choice(vertices)
                start = tuple((x+y)/2 for x, y in zip(start, other, strict=True))
            w = [start]
            for k in range(6):
                choices = P.transitions(w[-1])
                require(bool(choices), 'bounded test model has no finite step')
                w.append(rng.choice(choices))
                if (trial+k) % 5 == 0:
                    w.append(w[-1])
            # Finish by preserving every active row, dropping nullity strictly.
            while P.nullity(w[-1]) > 0:
                choices = P.transitions(w[-1], preserve_active=True)
                require(bool(choices), 'no face-preserving completion direction')
                previous = P.nullity(w[-1])
                w.append(choices[0])
                require(P.nullity(w[-1]) < previous, 'completion failed to descend')
            record = P.walk_record(w)
            counts['walks'] += 1
            counts['genuine_steps'] += record['genuine']
            counts['padding_steps'] += record['steps'] - record['genuine']
            counts['vertex_to_vertex_walks'] += int(record['source_nullity'] == 0)
            counts['nonvertex_start_walks'] += int(record['source_nullity'] > 0)
            counts['walks_with_nonvertex_checkpoints'] += int(record['max_checkpoint_nullity'] > 0)
            counts['rank_one_certificates'] += int(record['source_nullity'] == 0 and record['rank_one_certificate'])
            raw = [P.name, [[str(t) for t in x] for x in w], record]
            digest.update((json.dumps(raw, sort_keys=True, separators=(',', ':'))+'\n').encode())
        # Empty and all-padding walks must not consume genuine-step budget.
        center = tuple(sum((x[j] for x in vertices), Q(0))/len(vertices) for j in range(P.d))
        for w in ([vertices[0]], [vertices[0]]*4, [center]*3):
            record = P.walk_record(w)
            require(record['genuine'] == record['lost'] == record['gained'] == record['slack'] == 0,
                    'zero-length/padding regression failed')
        model_summary.append(dict(name=P.name, d=P.d, n=P.n,
                                  vertices=len(vertices), directed_circuits=len(P.circuit_directions())))
    sharp = []
    for d in range(1, 9):
        P = thin_diagonal_box(d)
        u, v = (Q(0),)*d, (Q(3),)*d
        center = (Q(3, 2),)*d
        require(all(dot(a, center) < b for a,b in zip(P.a, P.b, strict=True)),
                'sharp family is not strictly feasible')
        for i in range(P.n):
            if i < 2*d:
                coordinate, side = divmod(i, 2)
                witness = [Q(0) if side == 0 else Q(3)]*d
                witness[coordinate] += Q(-1, 2) if side == 0 else Q(1, 2)
            else:
                cut = i - 2*d
                witness = [Q(2) if j <= cut else Q(0) for j in range(d)]
            witness = tuple(witness)
            require(dot(P.a[i], witness) > P.b[i] and
                    all(dot(P.a[j], witness) <= P.b[j] for j in range(P.n) if j != i),
                    'sharp family row irredundancy witness failed')
        record = P.walk_record([u, v])
        require(P.n == 3*d-1 and record['lost'] == record['gained'] == d and record['slack'] == 0,
                'sharp half-budget family failed')
        sharp.append(dict(d=d, n=P.n, **record))
    # Average charge one does not imply the original walk is an edge walk.
    P = sheared_cube(2)
    w = [(Q(0), Q(0)), (Q(1), Q(1)), (Q(2), Q(1))]
    rec = P.walk_record(w)
    require(rec['lost'] == rec['gained'] == rec['genuine'] == 2 and rec['nonedge_steps'] == 2,
            'average-rank counterexample failed')
    average_counterexample = dict(model=P.name, checkpoints=[[str(t) for t in x] for x in w],
                                  local=[P.step_record(x, y) for x, y in zip(w, w[1:])], **rec)
    barriers = []
    for m in (1, 2, 3, 5, 8):
        P, vs = polygon_rank_barrier(m)
        u, v = (Q(-m), Q(0)), (Q(m), Q(0))
        rec = P.walk_record([u, v])
        distance = graph_distance(P, vs, u, v)
        require(P.n == 4*m+2 and distance == 2*m+1 and rec['lost'] == rec['gained'] == 2,
                'polygon rank-only cost barrier failed')
        barriers.append(dict(m=m, n=P.n, graph_distance=distance, lost=2, gained=2,
                             circuit_walk_length=1))
    cone = Poly('unbounded_orthant_2', 2, [unit(2, 0, -1), unit(2, 1, -1)], [Q(0), Q(0)])
    cone_record = cone.walk_record([(Q(1), Q(1)), (Q(0), Q(1)), (Q(0), Q(0))])
    wedge = Poly('unbounded_three_row_wedge', 2,
                 [unit(2, 0, -1), unit(2, 1, -1), (Q(1), Q(-1))], [Q(0), Q(0), Q(1)])
    wedge_record = wedge.walk_record([(Q(0), Q(0)), (Q(1), Q(0)), (Q(0), Q(0))])
    negative_checks = []
    square = cube(2)
    bad_walks = [
        ('nonmaximal', [(Q(0),Q(0)), (Q(1,2),Q(0))]),
        ('noncircuit', [(Q(0),Q(0)), (Q(1),Q(1))]),
        ('infeasible', [(Q(0),Q(0)), (Q(2),Q(0))]),
    ]
    for label, walk in bad_walks:
        try:
            square.walk_record(walk)
        except ValueError as exc:
            negative_checks.append(dict(case=label, rejected=True, reason=str(exc)))
        else:
            raise ValueError('invalid witness was accepted: '+label)
    return dict(evidence='EXACT_RATIONAL_REGRESSIONS_ONLY', seed=2026091103,
                Lean_compiled=False, Prove2Me_actions=0, counts=counts,
                trace_sha256=digest.hexdigest(), models=model_summary,
                sharp_half_budget=sharp, average_rank_counterexample=average_counterexample,
                polygon_rank_only_barriers=barriers, negative_checks=negative_checks,
                unbounded_examples=[dict(name=cone.name, **cone_record), dict(name=wedge.name, **wedge_record)])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = main()
    text = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text)
