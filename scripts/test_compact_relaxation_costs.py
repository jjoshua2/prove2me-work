#!/usr/bin/env python3
"""Exact cost diagnostics on the existing 4D/5D Dantzig witnesses.

For every one-row deletion, certify compactness with strictly positive row
weights summing to zero and full row rank, or provide an explicit nonzero
recession direction. No floating-point boundedness or optimization is trusted.
These are rational certificates, not Lean hull formalizations.
"""
from __future__ import annotations

from fractions import Fraction as Q
from itertools import combinations
import json

from test_face_preserving_checkpoints import Poly, dantzig_polars, dot, rank, solve


def null_ray(rows, dimension):
    a = [list(r) for r in rows]
    pivots = []
    r = 0
    for c in range(dimension):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        scale = a[r][c]
        a[r] = [x / scale for x in a[r]]
        for i in range(len(a)):
            if i != r:
                scale = a[i][c]
                a[i] = [x - scale * y for x, y in zip(a[i], a[r])]
        pivots.append(c)
        r += 1
        if r == len(a):
            break
    if r != dimension - 1:
        return None
    free = next(c for c in range(dimension) if c not in pivots)
    v = [Q(0)] * dimension
    v[free] = Q(1)
    for i, c in enumerate(pivots):
        v[c] = -a[i][free]
    return tuple(v)


def certificate(normals, removed):
    d = len(normals[0])
    rest = [a for i, a in enumerate(normals) if i != removed]
    assert rank(rest) == d
    assert all(sum((a[c] for a in normals), Q(0)) == 0 for c in range(d))
    for ids in combinations(range(len(rest)), d):
        transposed = [(tuple(rest[j][c] for j in ids), normals[removed][c]) for c in range(d)]
        coefficients = solve(transposed)
        if coefficients is None or min(coefficients) < 0:
            continue
        weights = [Q(1)] * len(rest)
        for i, value in zip(ids, coefficients):
            weights[i] += value
        assert min(weights) > 0
        assert all(sum((w * a[c] for w, a in zip(weights, rest)), Q(0)) == 0 for c in range(d))
        return {'kind': 'positive_spanning_weights', 'weights': list(map(str, weights))}
    for ids in combinations(range(len(rest)), d - 1):
        v = null_ray([rest[i] for i in ids], d)
        if v is None:
            continue
        for sign in (1, -1):
            ray = tuple(sign * x for x in v)
            if all(dot(a, ray) <= 0 for a in rest):
                assert any(ray)
                return {'kind': 'nonzero_recession_ray', 'ray': list(map(str, ray))}
    raise AssertionError('Neither kind of exact certificate was found')


def main():
    output = []
    for d, parent in zip((4, 5), dantzig_polars()):
        diagnostics = []
        parent_diameter = parent.diameter()
        for i in range(len(parent.rows)):
            cert = certificate([a for a, _ in parent.rows], i)
            record = {'deleted_row': i, 'certificate': cert}
            if cert['kind'] == 'positive_spanning_weights':
                outer = Poly(parent.rows[:i] + parent.rows[i + 1:])
                diameter = outer.diameter()
                face_cost = parent.diameter(parent.face([i]))
                assert parent_diameter <= diameter + face_cost
                record.update({'outer_vertices': len(outer.v), 'outer_diameter': diameter,
                               'final_cut_face_cost': face_cost,
                               'clipping_bound': diameter + face_cost})
            diagnostics.append(record)
        output.append({'dimension': d, 'parent_vertices': len(parent.v),
                       'parent_diameter': parent_diameter, 'one_row_deletions': diagnostics})
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
