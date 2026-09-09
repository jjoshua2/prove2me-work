#!/usr/bin/env python3
"""Exact regression certificates; no floats, external packages, or network.

The polygon certificates are computational, not Lean hull formalizations.
The generic repair/routing implications are verified separately by Lean.
"""
from __future__ import annotations

from collections import deque
from itertools import combinations, combinations_with_replacement, product
import json


def path(adj: list[set[int]], start: int, end: int,
         allowed: set[int] | None = None) -> list[int] | None:
    if allowed is None:
        allowed = set(range(len(adj)))
    if start not in allowed or end not in allowed:
        return None
    prev: dict[int, int | None] = {start: None}
    queue = deque([start])
    while queue:
        u = queue.popleft()
        if u == end:
            result = [u]
            while prev[u] is not None:
                u = prev[u]
                result.append(u)
            return result[::-1]
        for v in sorted(adj[u] & allowed):
            if v not in prev:
                prev[v] = u
                queue.append(v)
    return None


def parabola_polygon(n: int) -> list[set[int]]:
    """Enumerate all supporting edges of conv{(i,i^2): 0<=i<n}."""
    if n < 3:
        raise ValueError("At least three vertices are required")
    points = [(i, i*i) for i in range(n)]
    edges = set()
    for i, j in combinations(range(n), 2):
        x, y = points[i]
        dx, dy = points[j][0]-x, points[j][1]-y
        signs = [dx*(points[k][1]-y)-dy*(points[k][0]-x)
                 for k in range(n) if k not in (i, j)]
        assert all(s != 0 for s in signs)
        if all(s > 0 for s in signs) or all(s < 0 for s in signs):
            edges.add((i, j))
    expected = {(i, i+1) for i in range(n-1)} | {(0, n-1)}
    assert edges == expected
    for i in range(n):
        assert all(j*j-2*i*j > -i*i for j in range(n) if i != j)
    adj = [set() for _ in points]
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    return adj


def crossing_counterexamples() -> dict:
    cases = []
    for m in range(4, 33):
        adj = parabola_polygon(2*m)
        for positive_faces in (False, True):
            if positive_faces and m < 7:
                continue
            w = [0, m, 1, m+1] if positive_faces else [0, m, 0, m]
            faces = [{0, 1}, {m, m+1}] if positive_faces else [{0}, {m}]
            costs = [1, 1] if positive_faces else [0, 0]
            blocks = [(0, 2), (1, 3)]
            assert not (blocks[0][1] <= blocks[1][0])
            assert faces[0].isdisjoint(faces[1])
            for (s, t), face, cost in zip(blocks, faces, costs):
                assert w[s] in face and w[t] in face
                for u, v in combinations_with_replacement(sorted(face), 2):
                    p = path(adj, u, v, face)
                    assert p is not None and len(p)-1 <= cost
            outside = [k for k in range(3)
                       if all(k < s or t <= k for s, t in blocks)]
            assert outside == []
            p = path(adj, w[0], w[-1])
            assert p is not None
            distance = len(p)-1
            false_budget = 3 + sum(costs)
            assert distance == (m-1 if positive_faces else m)
            assert distance > false_budget
            if positive_faces:
                assert len(set(w)) == 4
            cases.append((m, positive_faces, distance, false_budget))
    return {"cases": len(cases), "singleton_example": [8, 4, 3],
            "distinct_vertex_edge_example": [14, 6, 5],
            "columns": ["polygon_vertices", "actual_distance", "false_budget"]}


def region_route(adj: list[set[int]], regions: tuple[set[int], ...],
                 costs: tuple[int, ...], u: int, v: int) -> list[int] | None:
    labels = [set() for _ in regions]
    for i, j in combinations(range(len(regions)), 2):
        if regions[i] & regions[j]:
            labels[i].add(j)
            labels[j].add(i)
    first = next(i for i, s in enumerate(regions) if u in s)
    last = next(i for i, s in enumerate(regions) if v in s)
    route = path(labels, first, last)
    if route is None:
        return None
    assert len(route) == len(set(route))
    points = [u] + [min(regions[i] & regions[j])
                    for i, j in zip(route, route[1:])] + [v]
    answer = [u]
    for i, a, b in zip(route, points, points[1:]):
        piece = path(adj, a, b, regions[i])
        assert piece is not None and len(piece)-1 <= costs[i]
        answer.extend(piece[1:])
    assert len(answer)-1 <= sum(costs[i] for i in route) <= sum(costs)
    assert answer[0] == u and answer[-1] == v
    assert all(b in adj[a] for a, b in zip(answer, answer[1:]))
    return answer


def exhaustive_small_graphs() -> dict:
    n = 4
    pairs = list(combinations(range(n), 2))
    families = connected_pairs = 0
    for bits in range(1 << len(pairs)):
        adj = [set() for _ in range(n)]
        for k, (a, b) in enumerate(pairs):
            if bits >> k & 1:
                adj[a].add(b)
                adj[b].add(a)
        local = []
        for mask in range(1, 1 << n):
            s = {i for i in range(n) if mask >> i & 1}
            paths = [path(adj, u, v, s)
                     for u, v in combinations_with_replacement(sorted(s), 2)]
            if all(p is not None for p in paths):
                local.append((s, max(len(p)-1 for p in paths if p is not None)))
        for size in range(1, 4):
            for family in combinations(local, size):
                regions = tuple(s for s, _ in family)
                costs = tuple(c for _, c in family)
                vertices = sorted(set().union(*regions))
                families += 1
                for u, v in combinations_with_replacement(vertices, 2):
                    if region_route(adj, regions, costs, u, v) is not None:
                        connected_pairs += 1
    return {"graphs": 1 << len(pairs), "families": families,
            "certified_endpoint_pairs": connected_pairs,
            "max_regions": 3, "vertices": n}


def exact_length_accounting() -> dict:
    checks = 0
    def visit(L: int, pos: int, blocks: tuple[tuple[int, int], ...], left: int):
        nonlocal checks
        for costs in product(range(3), repeat=len(blocks)):
            current = 0
            exact = 0
            for (s, t), B in zip(blocks, costs):
                exact += s-current+B
                current = t
            exact += L-current
            removed = sum(t-s for s, t in blocks)
            assert removed <= L
            assert exact == L-removed+sum(costs)
            assert exact <= L+sum(costs)
            if sum(costs) <= removed:
                assert exact <= L
            checks += 1
        if left:
            for s in range(pos, L+1):
                for t in range(s, L+1):
                    visit(L, t, blocks+((s, t),), left-1)
    for L in range(7):
        visit(L, 0, (), 3)
    return {"checked_budgets": checks, "max_length": 6,
            "max_blocks": 3, "costs": [0, 1, 2]}


def main() -> None:
    result = {"crossing": crossing_counterexamples(),
              "regions": exhaustive_small_graphs(),
              "ordered_accounting": exact_length_accounting()}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
