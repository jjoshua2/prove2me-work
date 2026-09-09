#!/usr/bin/env python3
"""Exact polygon certificates for the crossing-interval repair obstruction.

Only integer arithmetic and exhaustive finite graph search are used. This is
an independent computational certificate, not a Lean hull formalization.
"""
from __future__ import annotations

from collections import deque
from itertools import combinations
import json
from pathlib import Path


def orient(a: tuple[int, int], b: tuple[int, int], c: tuple[int, int]) -> int:
    return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])


def check_polygon(m: int) -> dict[str, object]:
    if m < 4:
        raise ValueError("m must be at least 4")
    n = 4 * m
    points = [(i, i * i) for i in range(n)]
    edges: set[tuple[int, int]] = set()
    determinant_checks = 0
    for i, j in combinations(range(n), 2):
        signs = [orient(points[i], points[j], points[k]) for k in range(n) if k not in (i, j)]
        determinant_checks += len(signs)
        assert all(value != 0 for value in signs), "Unexpected collinearity"
        if all(value > 0 for value in signs) or all(value < 0 for value in signs):
            edges.add((i, j))
    expected = {(i, i + 1) for i in range(n - 1)} | {(0, n - 1)}
    assert edges == expected, "Hull does not realize the claimed cycle"
    adj: dict[int, set[int]] = {i: set() for i in range(n)}
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    assert all(len(neighbors) == 2 for neighbors in adj.values())
    distance = {0: 0}
    queue = deque([0])
    while queue:
        i = queue.popleft()
        for j in adj[i]:
            if j not in distance:
                distance[j] = distance[i] + 1
                queue.append(j)
    assert len(distance) == n
    w = [0, 2 * m, 1, 2 * m + 1]
    regions = [{0, 1}, {2 * m, 2 * m + 1}]
    intervals = [(0, 2), (1, 3)]
    assert intervals[0][0] < intervals[1][0] < intervals[0][1] < intervals[1][1]
    for region, (s, t) in zip(regions, intervals):
        assert w[s] in region and w[t] in region
        assert tuple(sorted(region)) in edges
    assert regions[0].isdisjoint(regions[1])
    assert all(any(s <= k < t for s, t in intervals) for k in range(3))
    assert all(w[k + 1] not in adj[w[k]] and w[k] != w[k + 1] for k in range(3))
    actual = distance[w[-1]]
    assert actual == 2 * m - 1 and actual > 3 + 1 + 1
    # This potential is independently checked on every oriented graph edge.
    potential = {i: min(i, n - i) for i in range(n)}
    assert all(abs(potential[i] - potential[j]) <= 1 for i, j in edges)
    assert potential[w[-1]] == actual
    return {
        "m": m,
        "vertices": n,
        "dimension": 2,
        "hull_edges": sorted(edges),
        "points": points,
        "old_sequence_indices": w,
        "damage_intervals": intervals,
        "repair_regions": [sorted(region) for region in regions],
        "local_costs": [1, 1],
        "claimed_loose_budget": 5,
        "actual_shortest_distance": actual,
        "determinant_checks": determinant_checks,
    }


def main() -> None:
    results = [check_polygon(m) for m in range(4, 21)]
    out = Path("interval_repair_evidence")
    out.mkdir(exist_ok=True)
    report = {
        "scope": "Exact integer polygon/graph certificates; not Lean hull proofs",
        "instances": results,
        "instance_count": len(results),
        "determinant_checks": sum(int(r["determinant_checks"]) for r in results),
    }
    (out / "crossing_polygon_certificates.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "instances": len(results),
        "determinant_checks": report["determinant_checks"],
        "first_instance_distance": results[0]["actual_shortest_distance"],
        "last_instance_distance": results[-1]["actual_shortest_distance"],
        "status": "PASS",
    }, indent=2))


if __name__ == "__main__":
    main()
