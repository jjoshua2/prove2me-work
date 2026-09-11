#!/usr/bin/env python3
"""Exact, dependency-free tests of compact single-cut vertex classification.

All vertices are enumerated from every ambient full-rank row basis. For each
new cap vertex, an actual adjacent old vertex is constructed by moving along
the old active-row kernel until the first old constraint blocks it. No BFS,
floating-point LP, sampling of vertices, or assumed adjacency is used.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations
import json
import random
from pathlib import Path


def dot(a, x):
    return sum((u*v for u, v in zip(a, x)), F(0))


def rref(rows, width):
    mat = [list(map(F, row)) for row in rows]
    pivots = []
    k = 0
    for j in range(width):
        p = next((p for p in range(k, len(mat)) if mat[p][j]), None)
        if p is None:
            continue
        mat[k], mat[p] = mat[p], mat[k]
        q = mat[k][j]
        mat[k] = [x/q for x in mat[k]]
        for p in range(len(mat)):
            if p != k and mat[p][j]:
                q = mat[p][j]
                mat[p] = [x-q*y for x, y in zip(mat[p], mat[k])]
        pivots.append(j)
        k += 1
    return mat, pivots


def rank(rows, d):
    return len(rref(rows, d)[1])


def vertices(rows, d):
    result = set()
    for basis in combinations(rows, d):
        mat, piv = rref([list(a)+[b] for a, b in basis], d)
        if len(piv) != d:
            continue
        x = tuple(row[-1] for row in mat)
        if all(dot(a, x) <= b for a, b in rows):
            result.add(x)
    return sorted(result)


def is_edge(rows, x, y, d):
    return x != y and rank([a for a, b in rows
        if dot(a, x) == b == dot(a, y)], d) == d-1


def check_case(name, rows, d, level):
    rows = [(tuple(map(F, a)), F(b)) for a, b in rows]
    c = tuple(-sum((a[k] for a, _ in rows), F(0)) for k in range(d))
    # Injectivity makes this particular negative-row-sum cap bounded.
    assert rank([a for a, _ in rows], d) == d
    old = vertices(rows, d)
    capped = rows + [(c, F(level))]
    new = vertices(capped, d)
    certificates = []
    for z in new:
        if z in old:
            continue
        assert dot(c, z) == level
        active = [i for i, (a, b) in enumerate(rows) if dot(a, z) == b]
        mat, pivots = rref([rows[i][0] for i in active], d)
        assert len(pivots) == d-1
        free = next(j for j in range(d) if j not in pivots)
        g = [F(0)] * d
        g[free] = F(1)
        for k, j in enumerate(pivots):
            g[j] = -mat[k][free]
        cap_g = dot(c, g)
        assert cap_g != 0
        if cap_g > 0:
            g = [-q for q in g]
        blockers = [(b-dot(a, z))/dot(a, g) for a, b in rows if dot(a, g) > 0]
        assert blockers, 'A compact cap cannot contain an unbounded inward ray'
        t = min(blockers)
        assert t > 0
        v = tuple(x+t*h for x, h in zip(z, g))
        assert v in old and v in new
        assert dot(c, v) < level
        assert is_edge(capped, v, z, d)
        # The full old active carrier, not merely its rank, is preserved.
        assert all(dot(rows[i][0], v) == rows[i][1] for i in active)
        certificates.append({'new': list(map(str, z)), 'old_neighbor': list(map(str, v)),
            'direction': list(map(str, g)), 'step': str(t), 'old_active_rows': active})
    far = all(dot(c, v) < level for v in old)
    preserved_edges = 0
    if far:
        assert all(v in new for v in old)
        for u, v in combinations(old, 2):
            if is_edge(rows, u, v, d):
                assert is_edge(capped, u, v, d)
                preserved_edges += 1
    return {'name': name, 'dimension': d,
        'rows': [{'a': list(map(str, a)), 'b': str(b)} for a, b in rows],
        'cap_normal': list(map(str, c)), 'cap_level': str(level),
        'old_vertices': len(old), 'capped_vertices': len(new),
        'strictly_beyond_all_old_vertices': far,
        'old_edges_preserved': preserved_edges,
        'excluded_old_vertices': sum(dot(c, v) > level for v in old),
        'old_vertices_on_cap': sum(dot(c, v) == level for v in old),
        'certificates': certificates}


def run():
    cases = []
    def add(name, rows, d, level=None):
        rr = [(tuple(map(F, a)), F(b)) for a, b in rows]
        c = tuple(-sum((a[k] for a, _ in rr), F(0)) for k in range(d))
        vv = vertices(rr, d)
        if level is None:
            level = max([dot(c, v) for v in vv] + [F(0)]) + 1
        cases.append(check_case(name, rr, d, F(level)))
    add('zero_dimension', [], 0, 1)
    add('half_line', [([-1], 0)], 1, 2)
    add('empty_cap', [([-1], 0)], 1, -1)
    add('embedded_ray', [([-1, 0], 0), ([0, 1], 0), ([0, -1], 0)], 2, 2)
    add('embedded_segment', [([-2, 0, 0], 0), ([1, 0, 0], 2),
        ([0, 1, 0], 0), ([0, -1, 0], 0), ([0, 0, 1], 0), ([0, 0, -1], 0)], 3, 1)
    add('degenerate_square_cone', [([1,0,-1],0), ([-1,0,-1],0),
        ([0,1,-1],0), ([0,-1,-1],0)], 3, 8)
    scaled_square = [([-2,0],0), ([0,-2],0), ([1,0],1), ([0,1],1)]
    add('parent_only_cap_not_far_enough', scaled_square, 2, F(7,4))
    add('cap_through_old_vertices', scaled_square, 2, 1)
    add('all_old_vertices_preserved', scaled_square, 2, 3)
    rng = random.Random(20260911)
    for d, count in [(2, 40), (3, 40), (4, 8)]:
        for k in range(count):
            rows = [(tuple(-int(i == j) for i in range(d)), 0) for j in range(d)]
            for _ in range(d + 2):
                a = tuple(rng.randint(-3, 3) for _ in range(d))
                rows.append((a, rng.randint(1, 5)))
            if k % 4 == 0:
                rows.extend([rows[0], ((0,)*d, 0), ((0,)*d, 7)])
            add(f'seeded_far_d{d}_{k}', rows, d)
            # Small cap deliberately allowed to exclude old vertices.
            if k % 3 == 0:
                add(f'seeded_near_d{d}_{k}', rows, d, F(1, 3))
    huge = 10**35 + 17
    add('large_coefficients', [([-huge,0],0), ([0,-1],0), ([1,-1],2)], 2)
    summary = {'instances': len(cases),
        'new_cap_vertex_certificates': sum(len(c['certificates']) for c in cases),
        'old_vertices_enumerated': sum(c['old_vertices'] for c in cases),
        'capped_vertices_enumerated': sum(c['capped_vertices'] for c in cases),
        'far_instances': sum(c['strictly_beyond_all_old_vertices'] for c in cases),
        'non_far_instances': sum(not c['strictly_beyond_all_old_vertices'] for c in cases),
        'instances_excluding_old_vertices': sum(c['excluded_old_vertices'] > 0 for c in cases),
        'old_edges_preserved_in_far_instances': sum(c['old_edges_preserved'] for c in cases)}
    # All five inequalities of the pentagon parent are genuine facets.
    parent_rows = [(tuple(map(F,a)),F(b)) for a,b in scaled_square] + [((F(1), F(1)), F(3,2))]
    pverts = vertices(parent_rows, 2)
    assert all(sum(dot(a,v) == b for v in pverts) >= 2 for a,b in parent_rows)
    assert max(sum(v) for v in pverts) == F(3,2) < F(7,4) < 2
    summary['parent_only_counterexample'] = {
        'parent': '0<=x,y<=1; x+y<=3/2; lower rows scaled by 2',
        'explicit_cap': 'x+y<=7/4', 'excluded_outer_vertex': ['1','1'],
        'all_five_parent_rows_genuine_facets': True,
        'parent_strictly_below_cap': True}
    return {'summary': summary, 'cases': cases}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = run()
    args.output.write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    print(json.dumps(report['summary'], sort_keys=True, indent=2))
