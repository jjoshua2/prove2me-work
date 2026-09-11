#!/usr/bin/env python3
"""Exact finite tests of a tight-row certificate for swapping circuit steps.

The certificate permits overlapping row supports. This is rational test
coverage, not a Lean verdict or a claim of polynomial edge refinement.
Uses the unchanged checkpoint regression's exact polyhedral primitives.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations
import hashlib
import json
from pathlib import Path

from test_circuit_checkpoint_localization import (
    Poly, Vector, cube, dot, matrix_rank, sheared_cube, simplex, unit,
)


def add(x: Vector, y: Vector) -> Vector:
    return tuple(a + b for a, b in zip(x, y, strict=True))


def sub(x: Vector, y: Vector) -> Vector:
    return tuple(a - b for a, b in zip(x, y, strict=True))


def one_dimensional_kernel(rows: list[Vector], d: int) -> Vector | None:
    """Rational elimination, returning a normalized vector only for nullity 1."""
    a = [list(row) for row in rows]
    pivots: list[int] = []
    for column in range(d):
        pivot = next((i for i in range(len(pivots), len(a)) if a[i][column]), None)
        if pivot is None:
            continue
        r = len(pivots)
        a[r], a[pivot] = a[pivot], a[r]
        scale = a[r][column]
        a[r] = [entry / scale for entry in a[r]]
        for i in range(len(a)):
            if i != r and a[i][column]:
                scale = a[i][column]
                a[i] = [v - scale * w for v, w in zip(a[i], a[r], strict=True)]
        pivots.append(column)
    if len(pivots) != d - 1:
        return None
    free = next(i for i in range(d) if i not in pivots)
    g = [Q(0)] * d
    g[free] = Q(1)
    for r, column in enumerate(pivots):
        g[column] = -a[r][free]
    first = next(v for v in g if v)
    return tuple(v / first for v in g)


def circuits(p: Poly) -> list[Vector]:
    directions: set[Vector] = set()
    for indices in combinations(range(p.n), p.d - 1):
        g = one_dimensional_kernel([p.a[i] for i in indices], p.d)
        if g is None:
            continue
        neutral = [row for row in p.a if dot(row, g) == 0]
        assert matrix_rank(neutral, p.d) == p.d - 1
        # Adding any supported row kills the one-dimensional neutral kernel.
        assert all(matrix_rank(neutral + [row], p.d) == p.d
                   for row in p.a if dot(row, g) != 0)
        directions.add(g)
        directions.add(tuple(-v for v in g))
    return sorted(directions)


def endpoint(p: Poly, x: Vector, g: Vector) -> Vector | None:
    """Independent maximum-ratio test, not the proposed tight-row test."""
    assert p.feasible(x) and any(g)
    bounds = [(rhs - dot(row, x)) / dot(row, g)
              for row, rhs in zip(p.a, p.b, strict=True) if dot(row, g) > 0]
    # All test models have explicit bounding boxes or are simplices.
    assert bounds
    t = min(bounds)
    if t <= 0:
        return None
    y = add(x, tuple(t * v for v in g))
    assert p.feasible(y)
    return y


def blockers(p: Poly, y: Vector, g: Vector) -> list[int]:
    return [i for i, row in enumerate(p.a)
            if dot(row, y) == p.b[i] and dot(row, g) > 0]


def encode(x: Vector) -> list[str]:
    return [str(v) for v in x]


def case(p: Poly, x: Vector, y: Vector, z: Vector) -> dict:
    g, h = sub(y, x), sub(z, y)
    w = add(x, h)
    feasible = p.feasible(w)
    first_rows = blockers(p, w, h)
    second_rows = blockers(p, z, g)
    certificate = feasible and bool(first_rows) and bool(second_rows)
    first_maximal = endpoint(p, x, h) == w
    second_maximal = feasible and endpoint(p, w, g) == z
    actual_swap = feasible and first_maximal and second_maximal
    assert certificate == actual_swap
    if feasible:
        assert bool(first_rows) == first_maximal
        assert bool(second_rows) == second_maximal
    disjoint = all(dot(row, g) == 0 or dot(row, h) == 0 for row in p.a)
    assert not disjoint or certificate
    return dict(x=encode(x), y=encode(y), z=encode(z), w=encode(w),
                swapped_feasible=feasible, first_maximal=first_maximal,
                second_maximal=second_maximal, first_blockers=first_rows,
                second_blockers=second_rows, certificate=certificate,
                row_disjoint=disjoint)


def run() -> dict:
    models: list[tuple[Poly, list[Vector]]] = []
    for d in (1, 2, 3):
        models.append(cube(d))
    for d in (2, 3):
        models.append(simplex(d))
        p, vs, _ = sheared_cube(d)
        models.append((p, vs))
    p, _ = cube(3)
    # Irredundant corner-truncated [0,2]^3. The slanted facet overlaps
    # both coordinate directions, without blocking this square-face swap.
    p = Poly('truncated_cube_3', 3, p.a + [tuple([Q(1)] * 3)],
             [Q(0), Q(2)] * 3 + [Q(5)])
    models.append((p, p.vertices()))
    p, _ = cube(2)
    p = Poly('truncated_square_2', 2, p.a + [(Q(1), Q(1))],
             [Q(0), Q(2)] * 2 + [Q(3)])
    models.append((p, p.vertices()))
    p, vs = cube(2)
    models.append((Poly('redundant_square_2', 2,
                        p.a + [(Q(1), Q(1)), (Q(0), Q(0)), p.a[0]],
                        p.b + [Q(3), Q(0), p.b[0]]), vs))
    total: Counter[str] = Counter()
    digest = hashlib.sha256()
    summaries = []
    representatives: dict[str, dict] = {}
    for p, vs in models:
        dirs = circuits(p)
        seeds = set(vs)
        # All pair midpoints, not just edge midpoints; many are nonvertices.
        seeds.update(tuple((u + v) / 2 for u, v in zip(x, y, strict=True))
                     for x, y in combinations(vs, 2))
        seeds.add(tuple(sum(v[j] for v in vs) / len(vs) for j in range(p.d)))
        count: Counter[str] = Counter()
        for x in sorted(seeds):
            for g in dirs:
                y = endpoint(p, x, g)
                if y is None:
                    continue
                for h in dirs:
                    z = endpoint(p, y, h)
                    if z is None:
                        continue
                    r = case(p, x, y, z)
                    count['two_step_walks'] += 1
                    count['nonvertex_start_walks'] += int(p.face_dim(x) > 0)
                    count['nonvertex_middle_walks'] += int(p.face_dim(y) > 0)
                    if r['certificate']:
                        kind = 'row_disjoint_swaps' if r['row_disjoint'] else 'overlapping_support_swaps'
                    elif not r['swapped_feasible']:
                        kind = 'infeasible_swapped_point'
                    elif not r['first_maximal'] and not r['second_maximal']:
                        kind = 'both_maximality_tests_fail'
                    elif not r['first_maximal']:
                        kind = 'first_maximality_only_fails'
                    else:
                        kind = 'second_maximality_only_fails'
                    count[kind] += 1
                    representatives.setdefault(kind, {'model': p.name, **r})
                    digest.update((json.dumps([p.name, r], sort_keys=True,
                                              separators=(',', ':')) + '\n').encode())
        total.update(count)
        summaries.append(dict(name=p.name, d=p.d, rows=p.n, vertices=len(vs),
                              seeds=len(seeds), oriented_circuits=len(dirs), counts=dict(count)))
    assert total['overlapping_support_swaps'] > 0
    assert total['first_maximality_only_fails'] > 0
    assert total['second_maximality_only_fails'] > 0
    assert total['infeasible_swapped_point'] > 0
    p, _ = next((p, vs) for p, vs in models if p.name == 'truncated_cube_3')
    x, y, z = tuple([Q(0)] * 3), (Q(2), Q(0), Q(0)), (Q(2), Q(2), Q(0))
    assert endpoint(p, x, unit(3, 0)) == y and endpoint(p, y, unit(3, 1)) == z
    explicit = case(p, x, y, z)
    assert explicit['certificate'] and not explicit['row_disjoint']
    # Each of the seven inequalities is genuinely needed.
    witnesses = [(-1, 0, 0), (Q(5, 2), 0, 0), (0, -1, 0),
                 (0, Q(5, 2), 0), (0, 0, -1), (0, 0, Q(5, 2)), (2, 2, 2)]
    for i, witness in enumerate(witnesses):
        w = tuple(map(Q, witness))
        assert {j for j, row in enumerate(p.a) if dot(row, w) > p.b[j]} == {i}
    return dict(evidence='exact finite rational tests; NOT Lean or Prove2Me verification',
                arithmetic='fractions.Fraction', models=summaries, totals=dict(total),
                cases_sha256=digest.hexdigest(), representatives=representatives,
                irredundant_overlapping_example={'model': p.name, **explicit},
                theorem_scope='Preserves the two given displacements and maximality. '
                              'Does not prove that reordering controls carrier cost.')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Refusing optimized Python: exact checks use assertions.')
    text = json.dumps(run(), sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
