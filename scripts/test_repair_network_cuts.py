#!/usr/bin/env python3
"""Exact finite regressions for repair-network cuts; no floating point or API calls."""
from __future__ import annotations
import argparse
import itertools
import json
from collections import deque
from pathlib import Path

Graph = list[set[int]]


def distances(g: Graph, source: int, allowed: set[int] | None = None) -> dict[int, int]:
    allowed = set(range(len(g))) if allowed is None else allowed
    if source not in allowed:
        return {}
    result = {source: 0}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in sorted(g[u] & allowed):
            if v not in result:
                result[v] = result[u] + 1
                queue.append(v)
    return result


def region_graph(regions: list[set[int]]) -> Graph:
    return [{j for j, other in enumerate(regions) if j != i and bool(region & other)}
            for i, region in enumerate(regions)]


def intrinsic_cost(g: Graph, s: set[int]) -> int | None:
    costs = [distances(g, u, s) for u in s]
    if not s or any(len(row) != len(s) for row in costs):
        return None
    return max(max(row.values()) for row in costs)


def check_finite_networks() -> dict[str, int]:
    pairs = list(itertools.combinations(range(4), 2))
    families = label_pairs = cuts = route_bounds = 0
    for mask in range(1 << len(pairs)):
        g: Graph = [set() for _ in range(4)]
        for bit, (u, v) in enumerate(pairs):
            if (mask >> bit) & 1:
                g[u].add(v)
                g[v].add(u)
        parent_dist = [distances(g, u) for u in range(4)]
        valid = []
        for smask in range(1, 16):
            s = {i for i in range(4) if (smask >> i) & 1}
            cost = intrinsic_cost(g, s)
            if cost is not None:
                valid.append((s, cost))
        for n in range(1, min(3, len(valid)) + 1):
            for family in itertools.combinations(valid, n):
                families += 1
                regions = [s for s, _ in family]
                costs = [c for _, c in family]
                rg = region_graph(regions)
                budget = sum(costs)
                for i in range(n):
                    reached = distances(rg, i)
                    for j in range(n):
                        label_pairs += 1
                        cut_condition = True
                        for cmask in range(1 << n):
                            if not ((cmask >> i) & 1) or ((cmask >> j) & 1):
                                continue
                            cuts += 1
                            a = {k for k in range(n) if (cmask >> k) & 1}
                            crossed = any(rg[k] - a for k in a)
                            cut_condition = cut_condition and crossed
                        assert cut_condition == (j in reached)
                        if j in reached:
                            for u in regions[i]:
                                for v in regions[j]:
                                    assert v in parent_dist[u]
                                    assert parent_dist[u][v] <= budget
                                    route_bounds += 1
    return dict(graphs=64, region_families=families, endpoint_label_pairs=label_pairs,
                separating_cuts=cuts, certified_parent_route_bounds=route_bounds)


def check_cube(d: int) -> dict[str, object]:
    if d < 6:
        raise ValueError('The loose-budget obstruction requires dimension at least six.')
    size = 1 << d
    full = size - 1
    g: Graph = [{x ^ (1 << k) for k in range(d)} for x in range(size)]
    # Active inequalities of 0 <= x_k <= 1. Each active normal is +/- e_k.
    tight = [{2 * k + ((x >> k) & 1) for k in range(d)} for x in range(size)]
    assert all(len(rows) == d and {r // 2 for r in rows} == set(range(d)) for rows in tight)
    assert not (tight[0] & tight[full])
    pair_checks = 0
    for x in range(size):
        for y in range(x + 1, size):
            differences = (x ^ y).bit_count()
            # Common face has exactly these differences as its free coordinates.
            assert len(tight[x] & tight[y]) == d - differences
            assert (y in g[x]) == (differences == 1)
            pair_checks += 1
        for y in g[x]:
            assert abs(y.bit_count() - x.bit_count()) == 1
    w = [0, full ^ 1, 1, full]
    regions = [{0, 1}, {full ^ 1, full}]
    intervals = [(0, 2), (1, 3)]
    for region, (s, t) in zip(regions, intervals):
        assert w[s] in region and w[t] in region
        assert intrinsic_cost(g, region) == 1
    assert all(any(s <= j < t for s, t in intervals) for j in range(3))
    assert not (regions[0] & regions[1])
    assert region_graph(regions) == [set(), set()]
    dist = distances(g, 0)[full]
    assert dist == d and dist > 3 + 2 * 1
    return dict(dimension=d, h_rows=2*d, vertices=size,
                edges=sum(map(len, g))//2, exact_vertex_pair_checks=pair_checks,
                sequence_masks=w, intervals=intervals, individual_repair_costs=[1, 1],
                surviving_old_steps=0, false_loose_bound=5, actual_endpoint_distance=dist,
                source_target_share_a_facet=False, region_cut={'left':[0], 'right':[1]})


def check_repeated_region_sequence() -> dict[str, int]:
    g: Graph = [set() for _ in range(6)]
    for k in range(5):
        g[k].add(k+1)
        g[k+1].add(k)
    regions = [{0, 1, 2}, {4, 5}, {2, 3}, {3, 4}]
    costs = [2, 1, 1, 1]
    w = [0, 2, 3, 4, 5, 4, 3, 2, 0, 2, 3, 4, 5]
    assert all(intrinsic_cost(g, s) == c for s, c in zip(regions, costs))
    assert all(any(u in s and v in s for s in regions) for u, v in zip(w, w[1:]))
    actual = distances(g, w[0])[w[-1]]
    assert actual == sum(costs) == 5
    return dict(old_transitions=len(w)-1, distinct_general_regions=2,
                distinct_surviving_edge_regions=2, total_once_only_cost=5,
                actual_endpoint_distance=actual)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-dimension', type=int, default=9)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not 6 <= args.max_dimension <= 12:
        parser.error('--max-dimension must be between 6 and 12')
    result = {'scope': 'Exact finite Python regression, separate from Lean kernel certificates.',
              'finite_networks': check_finite_networks(),
              'cubes': [check_cube(d) for d in range(6, args.max_dimension + 1)],
              'repeated_mixed_regions': check_repeated_region_sequence()}
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
