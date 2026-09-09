#!/usr/bin/env python3
"""Exact pyramid diagnostics: cap complexity is not a necessary routing cost.

These calculations are separate from the all-pairs exterior-cap construction.
They reconstruct the complete bounded graph and the intrinsic final-face graph.
"""
from __future__ import annotations
import json
from fractions import Fraction as Q
from test_face_preserving_checkpoints import Poly, point, dot
from test_recession_cap_clipping import PointedPoly, recession_rays


def case(m: int) -> dict:
    # Homogenized convex hull of (i,i^2), i=0,...,m-1 at height z=1.
    rows = [(point([2*i+1, -1, -i*(i+1)]), Q(0)) for i in range(m-1)]
    rows += [(point([-(m-1), 1, 0]), Q(0)), (point([0, 0, -1]), Q(0))]
    outer = PointedPoly(rows)
    apex = point([0, 0, 0])
    assert outer.v == [apex] and len(outer.rays) == m
    final = Poly(rows + [(point([0, 0, 1]), Q(1))])
    assert recession_rays(final.rows) == []
    expected = {apex} | {point([i, i*i, 1]) for i in range(m)}
    assert set(final.v) == expected
    base = final.face([len(rows)])
    assert len(base) == m
    ai = final.v.index(apex)
    assert final.graph[ai] == set(base)
    assert all(len(final.graph[i] & base) == 2 for i in base)
    assert final.diameter(base) == m // 2
    assert final.diameter() == 2
    # Every pair of base vertices has an explicit parent route via the apex.
    for u in base:
        for v in base:
            assert ai in final.graph[u] and v in final.graph[ai]
    ell = tuple(-sum((a[j] for a, _ in rows), Q(0)) for j in range(3))
    level = max(dot(ell, x) for x in final.v) + 1
    truncated = Poly(rows + [(ell, level)])
    cap = truncated.face([len(rows)])
    assert len(cap) == m and truncated.diameter(cap) == m // 2
    assert all(dot(ell, x) < level for x in final.v)
    return dict(polygon_vertices=m, original_finite_diameter=0,
        recession_rays=m, exterior_cap_diameter=truncated.diameter(cap),
        final_cut_face_intrinsic_diameter=final.diameter(base),
        cap_bound=1 + m//2, true_final_diameter=2,
        parent_bypass_for_every_cut_face_vertex_pair=2)


def main():
    cases = [case(m) for m in (4, 6, 8, 12, 16, 20)]
    print(json.dumps({'cases': cases,
        'lesson': 'The cap itself needs no paid diameter; even a paid final face can have an arbitrarily cheaper parent-graph bypass.',
        'formalization': 'Exact rational finite graphs plus the general pyramid argument, not Lean hull theorems.'}, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
