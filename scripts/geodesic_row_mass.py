#!/usr/bin/env python3
"""Exact finite incidence audit for the all-available-cut carrier mass theorem.

The graph is validated and shortestness is recomputed. This CLI checks the
FINITE GRAPH and INTEGER BUDGET only; it does not establish that a supplied
graph is a polytope face graph or that alleged excesses are geometrically valid.
The companion regression builds exact polytopes and computes those quantities.
No third-party packages or network access are used.
"""
from __future__ import annotations
import argparse
from collections import deque
import json
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def nat(x: Any, name: str) -> int:
    require(type(x) is int and x >= 0, f'{name} must be a nonnegative integer')
    return x


def graph_from_edges(n: int, edges: list[list[int]]) -> list[set[int]]:
    nat(n, 'vertex_count')
    require(n > 0, 'graph must be nonempty')
    g = [set() for _ in range(n)]
    for edge in edges:
        require(isinstance(edge, list) and len(edge) == 2, 'edge must have two endpoints')
        u, v = edge
        nat(u, 'endpoint'); nat(v, 'endpoint')
        require(u < n and v < n and u != v, 'loop or invalid endpoint')
        require(v not in g[u], 'duplicate undirected edge')
        g[u].add(v); g[v].add(u)
    return g


def shortest_path(g: list[set[int]], start: int, end: int) -> list[int]:
    parent = {start: None}; todo = deque([start])
    while todo and end not in parent:
        x = todo.popleft()
        for y in sorted(g[x]):
            if y not in parent:
                parent[y] = x; todo.append(y)
    require(end in parent, 'endpoints are disconnected')
    out = []; x = end
    while x is not None:
        out.append(x); x = parent[x]
    return out[::-1]


def audit(data: dict[str, Any]) -> dict[str, Any]:
    require(isinstance(data, dict), 'input must be an object')
    g = graph_from_edges(data['vertex_count'], data['edges'])
    path = data['path']; available = data['available']; selected = data['selected']
    for name, values in [('path', path), ('available', available), ('selected', selected)]:
        require(isinstance(values, list), f'{name} must be an array')
        require(all(type(v) is int and 0 <= v < len(g) for v in values), f'invalid {name}')
        require(len(values) == len(set(values)), f'duplicate {name} label')
    require(bool(path), 'empty vertex sequence')
    require(all(y in g[x] for x, y in zip(path, path[1:])), 'sequence is not a walk')
    require(len(path) == len(shortest_path(g, path[0], path[-1])),
            'path is not metric-shortest; chordlessness alone is insufficient')
    require(set(selected) <= set(available) & set(path), 'selected labels must be available and on path')
    e = nat(data['excess'], 'excess'); s = len(available); r = len(selected)
    delta = data['carrier_excesses']
    require(isinstance(delta, list) and len(delta) == r, 'one excess per selected label required')
    for d in delta: nat(d, 'carrier excess')
    contacts = {j: [i for i, v in enumerate(path) if v == j or v in g[j]] for j in available}
    for j, positions in contacts.items():
        require(len(positions) <= 3, f'contact count failed for {j}')
        require(not positions or max(positions)-min(positions) <= 2, f'window failed for {j}')
    loads = [sum(i == j or i in g[j] for j in available) for i in selected]
    require(all(d+s <= e+t for d, t in zip(delta, loads)), 'pointwise resource budget fails')
    pos = {v: i for i, v in enumerate(path)}
    selected_positions = {pos[v] for v in selected}
    runs = sum(k-1 not in selected_positions for k in selected_positions)
    actual = sum(delta); total_load = sum(loads)
    require(total_load + 2*runs <= 3*s, 'run-refined load bound fails')
    require(actual + r*s + 2*runs <= r*e + 3*s, 'run-refined aggregate fails')
    result = {
        'status': 'PASS', 'available': s, 'selected': r, 'path_edges': len(path)-1,
        'selected_runs': runs, 'contact_loads': loads, 'total_contact_load': total_load,
        'carrier_mass': actual, 'subtraction_free_lhs': actual+r*s,
        'subtraction_free_rhs': r*e+3*s,
        'contact_positions': {str(k): v for k, v in contacts.items()},
        'scope': 'Exact graph/integer audit only; geometric excesses and Lean acceptance are not certified here.'
    }
    if s <= e:
        result['availability_defect'] = e-s
        result['new_mass_bound'] = r*(e-s)+3*s-2*runs
        if r <= e:
            result['old_selected_only_bound'] = r*(e-r+3)-2*runs
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        out = json.dumps(audit(json.loads(args.input.read_text())), indent=2, sort_keys=True)+'\n'
        if args.output: args.output.write_text(out)
        else: print(out, end='')
    except (ValueError, KeyError, TypeError, OSError) as exc:
        parser.exit(2, f'Certificate rejected: {exc}\n')

if __name__ == '__main__':
    main()
