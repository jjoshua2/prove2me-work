#!/usr/bin/env python3
"""Exact 2-D regression for nonvertex blocker deletion; not a substitute for Lean."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
import json

Point = tuple[F, F]
Row = tuple[F, F, F]


def value(row: Row, x: Point) -> F:
    return row[0] * x[0] + row[1] * x[1]


def rank2(rows: list[Row]) -> bool:
    return any(a[0] * b[1] != a[1] * b[0] for a, b in combinations(rows, 2))


def feasible(rows: list[Row], x: Point) -> bool:
    return all(value(a, x) <= a[2] for a in rows)


def vertices(rows: list[Row]) -> set[Point]:
    result: set[Point] = set()
    for a, b in combinations(rows, 2):
        det = a[0] * b[1] - a[1] * b[0]
        if det:
            x = ((a[2] * b[1] - a[1] * b[2]) / det,
                 (a[0] * b[2] - a[2] * b[0]) / det)
            if feasible(rows, x):
                result.add(x)
    return result


def phase(rows: list[Row], v: Point, x: Point, M: int) -> frozenset[int]:
    sv = [a[2] - value(a, v) for a in rows]
    sx = [a[2] - value(a, x) for a in rows]
    return frozenset(i for i in range(len(rows))
                     if (sx[i] == 0 if sv[i] == 0 else sx[i] <= M * sv[i]))


def main() -> None:
    bases = [
        [(-1, 0, 0), (0, -1, 0)],                       # quadrant: genuine exception
        [(-1, 0, 0), (0, -1, 0), (0, 1, 1)],          # pointed unbounded strip
        [(-1, 0, 0), (0, -1, 0), (1, 0, 1), (0, 1, 1)],
        [(-1, 0, 0), (0, -1, 0), (1, 1, 2)],
        [(-1, 0, 0), (0, -1, 0), (1, -1, 1)],
        [(-1, 0, 0), (0, -1, 0), (1, 0, 1), (0, 1, 1), (1, 1, F(3, 2))],
        [(1, 0, 0), (-1, 0, 0), (0, -1, 0)],          # lower-dimensional ray
        [(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0)],  # singleton
    ]
    counts: Counter[str] = Counter()
    details = []
    for bi, base in enumerate(bases):
        # Positive rescaling preserves geometry; zero and redundant rows test representation dependence.
        for scale in (1, 3, 10**36 + 1):
            rows = [tuple(F(scale * z) for z in a) for a in base]
            rows += [(F(0), F(0), F(0)), (F(0), F(0), F(1))]
            assert rank2(rows)
            verts = vertices(rows)
            assert verts
            sources = set(verts)
            sources |= {(F(i, 2), F(j, 2)) for i, j in product(range(-2, 7), repeat=2)
                        if feasible(rows, (F(i, 2), F(j, 2)))}
            for p, q in combinations(sorted(verts), 2):
                sources.add(((p[0] + q[0]) / 2, (p[1] + q[1]) / 2))
            # In rank two, a circuit direction has a rank-one neutral row set.
            directions = {(F(-a[1]), F(a[0])) for a in base if a[0] or a[1]}
            directions |= {(-g[0], -g[1]) for g in tuple(directions)}
            local: Counter[str] = Counter()
            deletion_verts = [vertices(rows[:j] + rows[j + 1:]) for j in range(len(rows))]
            for j, row in enumerate(rows):
                for v in sorted(verts):
                    if value(row, v) < row[2]:
                        assert rank2(rows[:j] + rows[j + 1:])
                        assert v in deletion_verts[j]
                        local['arbitrary_slack_row_vertex_checks'] += 1
            for x in sorted(sources):
                for g in sorted(directions):
                    pos = [(a[2] - value(a, x)) / value(a, g) for a in rows if value(a, g) > 0]
                    if not pos:
                        continue
                    step = min(pos)
                    if step <= 0:
                        continue
                    y = (x[0] + step * g[0], x[1] + step * g[1])
                    if not feasible(rows, y):
                        continue
                    local['maximal_circuit_steps'] += 1
                    local['nonvertex_source_steps'] += x not in verts
                    for j, row in enumerate(rows):
                        if value(row, g) <= 0 or value(row, y) != row[2]:
                            continue
                        retained = rows[:j] + rows[j + 1:]
                        other = any(i != j and value(a, g) != 0 for i, a in enumerate(rows))
                        pointed = rank2(retained)
                        assert pointed == other, (bi, scale, x, g, j)
                        local['blocker_deletion_checks'] += 1
                        if not pointed:
                            assert all(value(row, v) == row[2] for v in verts)
                            local['universal_vertex_face_exceptions'] += 1
                        for v in sorted(verts):
                            if value(row, v) < row[2]:
                                assert pointed and v in deletion_verts[j]
                                assert len(retained) - 2 < len(rows) - 2
                                local['slack_target_preservation_checks'] += 1
                            M = max(2, len(rows))
                            if phase(rows, v, x, M) == phase(rows, v, y, M):
                                assert value(row, v) < row[2]
                                assert pointed and v in deletion_verts[j]
                                assert row[2] - value(row, x) <= M * (row[2] - value(row, v))
                                local['same_phase_target_preservation_checks'] += 1
                                local['same_phase_nonvertex_source_checks'] += x not in verts
            counts.update(local)
            details.append({'base': bi, 'row_scale': str(scale), 'vertices': len(verts), **dict(sorted(local.items()))})
    for key in ('universal_vertex_face_exceptions', 'same_phase_nonvertex_source_checks',
                'slack_target_preservation_checks'):
        assert counts[key] > 0, key
    print(json.dumps({'status': 'PASS', 'systems': len(details), 'totals': dict(sorted(counts.items())),
                      'instances': details}, sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
