#!/usr/bin/env python3
"""Finite repair-network certificates, using exact integer costs.

A positive result is conditional on the caller's local region-diameter proofs.
A cut only obstructs the supplied network, not unlisted ambient edges.
No third-party packages, network requests, or Prove2Me writes are used.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from heapq import heappop, heappush
from itertools import combinations
from pathlib import Path
from typing import Any
import argparse
import json


@dataclass(frozen=True)
class Region:
    vertices: frozenset[int]
    cost: int


def network(n: int, regions: list[Region], bridges: list[tuple[int, int]],
            source: int, target: int) -> list[Region]:
    if not isinstance(n, int) or n < 1 or not (0 <= source < n and 0 <= target < n):
        raise ValueError('Invalid vertex universe or terminals')
    nodes = list(regions) + [Region(frozenset(e), 1) for e in bridges]
    nodes += [Region(frozenset([source]), 0), Region(frozenset([target]), 0)]
    for r in nodes:
        if not isinstance(r.cost, int) or r.cost < 0:
            raise ValueError('Costs must be nonnegative integers')
        if any(not isinstance(x, int) or not 0 <= x < n for x in r.vertices):
            raise ValueError('Region vertex outside the supplied universe')
    if any(len(e) != 2 for e in bridges):
        raise ValueError('A bridge needs exactly two endpoints')
    return nodes


def certificate(n: int, regions: list[Region], bridges: list[tuple[int, int]],
                source: int, target: int) -> dict[str, Any]:
    """Minimum uniform-region-charge path, or a separating vertex cut.

    Minimum refers to this finite weighted region-intersection network, not
    to the shortest ambient walk or the best possible choice of local routes.
    """
    nodes = network(n, regions, bridges, source, target)
    s, t = len(nodes) - 2, len(nodes) - 1
    dist: dict[int, int] = {s: 0}
    parent: dict[int, tuple[int, int]] = {}
    queue = [(0, s)]
    done: set[int] = set()
    while queue:
        value, i = heappop(queue)
        if i in done or value != dist[i]:
            continue
        done.add(i)
        for j, node in enumerate(nodes):
            shared = nodes[i].vertices & node.vertices
            if j == i or not shared:
                continue
            candidate = value + node.cost
            if j not in dist or candidate < dist[j]:
                dist[j] = candidate
                parent[j] = (i, min(shared))
                heappush(queue, (candidate, j))
    if t not in dist:
        side = set().union(*(nodes[i].vertices for i in dist))
        result = {'kind': 'cut', 'side': sorted(side)}
    else:
        chain, portals = [t], []
        i = t
        while i != s:
            i, portal = parent[i]
            chain.append(i)
            portals.append(portal)
        result = {'kind': 'route', 'cost': dist[t],
                  'nodes': chain[::-1], 'portals': portals[::-1]}
    verify_certificate(n, regions, bridges, source, target, result)
    return result


def verify_certificate(n: int, regions: list[Region], bridges: list[tuple[int, int]],
                       source: int, target: int, result: dict[str, Any]) -> None:
    """Independent certificate checks; no Dijkstra/shortest-path calls."""
    nodes = network(n, regions, bridges, source, target)
    if result.get('kind') == 'cut':
        side = set(result['side'])
        if any(not isinstance(x, int) or not 0 <= x < n for x in side):
            raise ValueError('Malformed cut')
        if source not in side or target in side:
            raise ValueError('Cut fails to separate terminals')
        if any(r.vertices & side and not r.vertices <= side for r in regions):
            raise ValueError('A supplied region crosses the cut')
        if any((a in side) != (b in side) for a, b in bridges):
            raise ValueError('A supplied bridge crosses the cut')
        return
    if result.get('kind') != 'route':
        raise ValueError('Unknown certificate kind')
    chain, portals = result['nodes'], result['portals']
    if not chain or chain[0] != len(nodes) - 2 or chain[-1] != len(nodes) - 1:
        raise ValueError('Route has incorrect terminals')
    if len(set(chain)) != len(chain) or any(not 0 <= i < len(nodes) for i in chain):
        raise ValueError('Route must use distinct valid node labels')
    if len(portals) != len(chain) - 1:
        raise ValueError('Incorrect portal count')
    for i, j, x in zip(chain, chain[1:], portals):
        if x not in nodes[i].vertices or x not in nodes[j].vertices:
            raise ValueError('Portal not shared by consecutive regions')
    total = sum(nodes[i].cost for i in chain)
    if result['cost'] != total or total > sum(r.cost for r in regions) + len(bridges):
        raise ValueError('Incorrect one-charge-per-region budget')


def reference_reachable(n: int, regions: list[Region], bridges: list[tuple[int, int]],
                        source: int) -> set[int]:
    """Independent transitive closure on vertices, not region labels."""
    seen = {source}
    changed = True
    while changed:
        old = set(seen)
        for r in regions:
            if r.vertices & seen:
                seen.update(r.vertices)
        for a, b in bridges:
            if a in seen or b in seen:
                seen.update((a, b))
        changed = seen != old
    return seen


def regression_family(n: int, regions: list[Region], bridges: list[tuple[int, int]]) -> int:
    for u in range(n):
        reachable = reference_reachable(n, regions, bridges, u)
        for v in range(n):
            result = certificate(n, regions, bridges, u, v)
            if (result['kind'] == 'route') != (v in reachable):
                raise AssertionError('Certificate disagrees with independent vertex closure')
    return n * n


def exact_polygon(m: int) -> dict[str, Any]:
    """Exact H-polygon witness on the integer parabola, with 2m vertices.

    This rational hull certificate is independent of the Lean finite-cycle
    proof; the general H-polytope/graph identification is not Lean-formalized.
    """
    if m < 3:
        raise ValueError('Need m >= 3 for disjoint endpoint edges')
    n = 2 * m
    vertices = [(Fraction(i), Fraction(i * i)) for i in range(n)]
    rows = [(2*k + 1, -1, k*(k + 1)) for k in range(n - 1)] + [(-(n - 1), 1, 0)]
    feasible = set()
    for (a, b, c), (d, e, f) in combinations(rows, 2):
        det = a*e - b*d
        if not det:
            continue
        point = (Fraction(c*e - b*f, det), Fraction(a*f - c*d, det))
        if all(A*point[0] + B*point[1] <= C for A, B, C in rows):
            feasible.add(point)
    assert feasible == set(vertices)
    assert tuple(rows[0][i] + rows[-1][i] for i in range(3)) == (-(n-2), 0, 0)
    assert tuple(rows[-2][i] + rows[-1][i] for i in range(3)) == (n-2, 0, (n-2)*(n-1))
    assert (vertices[1][0]-vertices[0][0])*(vertices[2][1]-vertices[0][1]) - \
           (vertices[2][0]-vertices[0][0])*(vertices[1][1]-vertices[0][1]) == 2
    edges = []
    for A, B, C in rows:
        tight = [i for i, (x, y) in enumerate(vertices) if A*x+B*y == C]
        assert len(tight) == 2
        edges.append(tuple(tight))
    assert {frozenset(e) for e in edges} == {frozenset((i, (i+1)%n)) for i in range(n)}
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    distances = {0: 0}; pending = [0]
    for u in pending:
        for v in sorted(adj[u]):
            if v not in distances:
                distances[v] = distances[u]+1; pending.append(v)
    assert distances[m] == m
    regions = [Region(frozenset((0, 1)), 1), Region(frozenset((m-1, m)), 1)]
    seq = (0, m-1, 1, m)
    assert {seq[0], seq[2]} <= regions[0].vertices
    assert {seq[1], seq[3]} <= regions[1].vertices
    assert set(range(0, 2)) | set(range(1, 3)) == set(range(3))
    blocked = certificate(n, regions, [], 0, m)
    assert blocked == {'kind': 'cut', 'side': [0, 1]}
    bridges = [(i, i+1) for i in range(1, m-1)]
    repaired = certificate(n, regions, bridges, 0, m)
    assert repaired['kind'] == 'route' and repaired['cost'] == m
    return {'m': m, 'vertices': n, 'facets': n, 'dimension': 2,
            'old_sequence': list(seq), 'intervals': [[0, 2], [1, 3]],
            'face_budget_sum': 2, 'loose_proposed_budget': 5,
            'true_endpoint_distance': m, 'network_cut': blocked,
            'repaired_with_bridges': repaired}


def run_tests() -> dict[str, Any]:
    counts = {'region_family_endpoint_cases': 0, 'bridge_graph_endpoint_cases': 0,
              'mixed_endpoint_cases': 0}
    subsets = [frozenset(c) for k in range(2, 5) for c in combinations(range(4), k)]
    for mask in range(1 << len(subsets)):
        regions = [Region(s, len(s)-1) for i, s in enumerate(subsets) if mask >> i & 1]
        counts['region_family_endpoint_cases'] += regression_family(4, regions, [])
    pairs = list(combinations(range(5), 2))
    for mask in range(1 << len(pairs)):
        bridges = [e for i, e in enumerate(pairs) if mask >> i & 1]
        counts['bridge_graph_endpoint_cases'] += regression_family(5, [], bridges)
    small = [frozenset(c) for k in range(2, 4) for c in combinations(range(3), k)]
    pairs3 = list(combinations(range(3), 2))
    for mask in range(1 << len(small)):
        regions = [Region(s, 1 + i) for i, s in enumerate(small) if mask >> i & 1]
        for emask in range(1 << len(pairs3)):
            bridges = [e for i, e in enumerate(pairs3) if emask >> i & 1]
            counts['mixed_endpoint_cases'] += regression_family(3, regions, bridges)
    sample = [Region(frozenset((0, 1)), 1), Region(frozenset((0, 1)), 4),
              Region(frozenset((2, 3)), 1), Region(frozenset((4, 5)), 90),
              Region(frozenset((1,)), 0), Region(frozenset(), 0)]
    result = certificate(6, sample, [(1, 2)], 0, 3)
    assert result['cost'] == 3
    bad = dict(result, cost=2)
    try:
        verify_certificate(6, sample, [(1, 2)], 0, 3, bad)
    except ValueError:
        pass
    else:
        raise AssertionError('Tampered cost certificate accepted')
    try:
        verify_certificate(6, sample, [(1, 2)], 0, 3, {'kind': 'cut', 'side': [0, 1]})
    except ValueError:
        pass
    else:
        raise AssertionError('Crossed cut certificate accepted')
    witnesses = [exact_polygon(m) for m in (3, 6, 10, 25)]
    return {'status': 'PASS', 'exhaustive_cases': counts,
            'total_endpoint_cases': sum(counts.values()),
            'exact_polygon_witnesses': witnesses,
            'scope': 'Finite certificates; local geometric diameter proofs remain caller obligations.'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional JSON regression receipt')
    args = parser.parse_args()
    results = run_tests()
    text = json.dumps(results, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
