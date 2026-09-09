#!/usr/bin/env python3
"""Independent Floyd-Warshall cost oracle for every 4-vertex region family."""
from itertools import combinations
from pathlib import Path
import json
from portal_cut_certificate import Region, certificate


def main():
    n = 4
    supports = [frozenset(c) for k in range(2, 5) for c in combinations(range(n), k)]
    checked = 0
    for mask in range(1 << len(supports)):
        regions = [Region(s, i % 4 + 1) for i, s in enumerate(supports) if mask >> i & 1]
        infinity = sum(r.cost for r in regions) + 1
        distances = [[0 if u == v else infinity for v in range(n)] for u in range(n)]
        for r in regions:
            for u in r.vertices:
                for v in r.vertices:
                    distances[u][v] = min(distances[u][v], r.cost)
        for k in range(n):
            for u in range(n):
                for v in range(n):
                    distances[u][v] = min(distances[u][v], distances[u][k] + distances[k][v])
        for u in range(n):
            for v in range(n):
                result = certificate(n, regions, [], u, v)
                if distances[u][v] < infinity:
                    assert result['kind'] == 'route' and result['cost'] == distances[u][v]
                else:
                    assert result['kind'] == 'cut'
                checked += 1
    result = {'status': 'PASS', 'independent_floyd_warshall_endpoint_cases': checked,
              'scope': 'Minimum supplied uniform-region-charge cost, not ambient graph distance.'}
    path = Path(__file__).resolve().parents[1] / 'research' / 'portal_cost_optimality.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
