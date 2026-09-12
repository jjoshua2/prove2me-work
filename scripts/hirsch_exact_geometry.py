"""Small exact rational geometry helpers. No float acceptance or network use.
Enumeration is a capped diagnostic/low-dimensional routing method, not a
polynomial-time algorithm or a substitute for the universal proof.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from typing import Any, Sequence

Vector = list[Q]
Matrix = list[Vector]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rational(value: Any) -> Q:
    require(type(value) in (int, str, Q), 'Use integers or rational strings; no floats/bools')
    return Q(value)


def vector(value: Any) -> Vector:
    require(isinstance(value, list), 'Expected a vector array')
    return [rational(x) for x in value]


def matrix(value: Any) -> Matrix:
    require(isinstance(value, list), 'Expected a matrix array')
    rows = [vector(row) for row in value]
    require(not rows or all(len(row) == len(rows[0]) for row in rows), 'Ragged matrix')
    return rows


def dot(x: Sequence[Q], y: Sequence[Q]) -> Q:
    require(len(x) == len(y), 'Dot product dimension mismatch')
    return sum((a*b for a, b in zip(x, y)), Q(0))


def eye(d: int) -> Matrix:
    return [[Q(i == j) for j in range(d)] for i in range(d)]


def transpose(a: Matrix, width: int | None = None) -> Matrix:
    return [list(row) for row in zip(*a)] if a else [[] for _ in range(width or 0)]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    require(bool(b), 'Use an explicit empty-matrix branch')
    require(all(len(row) == len(b[0]) for row in b), 'Ragged matrix')
    return [[dot(row, col) for col in zip(*b)] for row in a]


def rref(rows: Matrix) -> tuple[Matrix, list[int]]:
    a = [row[:] for row in rows]
    width = len(a[0]) if a else 0
    pivots: list[int] = []
    for j in range(width):
        k = len(pivots)
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        scale = a[k][j]
        a[k] = [x/scale for x in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                scale = a[i][j]
                a[i] = [x-scale*y for x, y in zip(a[i], a[k])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return a[:len(pivots)], pivots


def rank(a: Matrix) -> int:
    return len(rref(a)[1])


def inverse(a: Matrix) -> Matrix:
    d = len(a)
    require(d > 0 and all(len(row) == d for row in a), 'Positive square inverse required')
    rr, piv = rref([row+e for row, e in zip(a, eye(d))])
    require(piv == list(range(d)) and [row[:d] for row in rr] == eye(d), 'Singular matrix')
    return [row[d:] for row in rr]


def solve(a: Matrix, b: Vector) -> Vector:
    require(len(a) == len(b), 'Solve dimension mismatch')
    return [dot(row, b) for row in inverse(a)]


def active_set(a: Matrix, b: Vector, x: Vector) -> set[int]:
    require(len(a) == len(b) and all(len(row) == len(x) for row in a), 'A/b/x shape mismatch')
    slack = [rhs-dot(row, x) for row, rhs in zip(a, b)]
    require(all(s >= 0 for s in slack), 'Infeasible point')
    return {i for i, s in enumerate(slack) if not s}


def verify_vertex(a: Matrix, b: Vector, x: Vector) -> set[int]:
    active = active_set(a, b, x)
    require(rank([a[i] for i in sorted(active)]) == len(x), 'Point lacks full active rank')
    return active


def verify_edge(a: Matrix, b: Vector, x: Vector, y: Vector) -> None:
    require(x != y, 'Stationary move is not a claimed edge')
    common = verify_vertex(a, b, x) & verify_vertex(a, b, y)
    require(rank([a[i] for i in sorted(common)]) == len(x)-1,
            'Shared active rows do not define a one-dimensional face')


def vertices(a: Matrix, b: Vector, *, max_bases: int = 200000) -> dict[tuple[Q, ...], set[int]]:
    require(bool(a) and len(a) == len(b), 'Nonempty A/b required')
    d = len(a[0])
    count = comb(len(a), d)
    require(count <= max_bases, f'Enumeration cap: {count} bases exceeds {max_bases}')
    found: dict[tuple[Q, ...], set[int]] = {}
    if d == 0:
        require(all(rhs >= 0 for rhs in b), 'Infeasible zero-dimensional model')
        return {(): {i for i, rhs in enumerate(b) if not rhs}}
    for ids in combinations(range(len(a)), d):
        basis = [a[i] for i in ids]
        if rank(basis) != d:
            continue
        x = solve(basis, [b[i] for i in ids])
        if all(dot(row, x) <= rhs for row, rhs in zip(a, b)):
            found[tuple(x)] = active_set(a, b, x)
    return found


def graph(a: Matrix, vv: dict[tuple[Q, ...], set[int]]) -> dict[tuple[Q, ...], list[tuple[Q, ...]]]:
    points = list(vv)
    require(bool(points), 'No vertices')
    d = len(points[0]); out = {p: [] for p in points}
    for i, p in enumerate(points):
        for q in points[:i]:
            common = vv[p] & vv[q]
            if rank([a[j] for j in sorted(common)]) == d-1:
                out[p].append(q); out[q].append(p)
    return out


def shortest_path(adj: dict, start: tuple, target: tuple) -> list[tuple]:
    require(start in adj and target in adj, 'Missing route endpoint')
    parent = {start: None}; todo = deque([start])
    while todo and target not in parent:
        p = todo.popleft()
        for q in adj[p]:
            if q not in parent:
                parent[q] = p; todo.append(q)
    require(target in parent, 'Disconnected enumerated local graph')
    route = [target]
    while route[-1] != start:
        route.append(parent[route[-1]])
    return list(reversed(route))


def graph_stats(adj: dict) -> dict[str, int]:
    maximum = 0
    for start in adj:
        dist = {start: 0}; todo = deque([start])
        while todo:
            p = todo.popleft()
            for q in adj[p]:
                if q not in dist:
                    dist[q] = dist[p]+1; todo.append(q)
        require(len(dist) == len(adj), 'Disconnected diagnostic graph')
        maximum = max(maximum, max(dist.values()))
    return {'vertices': len(adj), 'edges': sum(map(len, adj.values()))//2,
            'ordered_distances': len(adj)**2, 'diameter': maximum}


def jsonable(value: Any) -> Any:
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {str(k): jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [jsonable(v) for v in value]
    if isinstance(value, set):
        return sorted(value)
    return value
