#!/usr/bin/env python3
"""Exact certificates for a family obstructing low-defect circuit reordering.

For k controls x_i and ordered-pair coordinates z_ij, impose
    |z_ij| <= x_i,  |z_ij| <= 1-x_j  (i != j).
The d=k^2 dimensional polytope has 4*k*(k-1) irredundant rows.
All control-only maximal circuit moves commute, but every order has maximum
carrier dimension floor((k+1)^2/4). A different explicit k-edge route exists.

This is finite exact rational verification, not a Lean proof or exhaustive
vertex enumeration in dimensions above four. The accompanying research note
proves the all-k statements by explicit rank and feasibility arguments.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import permutations
import json
from pathlib import Path
from typing import Sequence

Vector = tuple[Q, ...]


def rank(rows: Sequence[Sequence[int | Q]], dimension: int) -> int:
    """Exact Gaussian elimination; only update rows with nonzero pivots."""
    work = [list(map(Q, row)) for row in rows]
    assert all(len(row) == dimension for row in work)
    pivot_row = 0
    for col in range(dimension):
        pivot = next((r for r in range(pivot_row, len(work)) if work[r][col]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        pivot_vector = work[pivot_row]
        for r in range(pivot_row + 1, len(work)):
            if not work[r][col]:
                continue
            multiplier = work[r][col] / pivot_vector[col]
            work[r][col] = Q(0)
            for c in range(col + 1, dimension):
                if pivot_vector[c]:
                    work[r][c] -= multiplier * pivot_vector[c]
        pivot_row += 1
        if pivot_row == len(work):
            break
    return pivot_row


class CoupledFamily:
    def __init__(self, k: int):
        if k < 2:
            raise ValueError('k must be at least two')
        self.k = k
        self.arcs = tuple((i, j) for i in range(k) for j in range(k) if i != j)
        self.position = {arc: k + index for index, arc in enumerate(self.arcs)}
        self.d = k * k
        # Each row contains precisely one control and one ordered-pair coordinate.
        self.rows: list[tuple[int, ...]] = []
        self.rhs: list[Q] = []
        self.descriptions: list[tuple[str, int, int, int]] = []
        for i, j in self.arcs:
            for role in ('tail', 'head'):
                for sign in (-1, 1):
                    row = [0] * self.d
                    row[i if role == 'tail' else j] = -1 if role == 'tail' else 1
                    row[self.position[i, j]] = sign
                    self.rows.append(tuple(row))
                    self.rhs.append(Q(0 if role == 'tail' else 1))
                    self.descriptions.append((role, i, j, sign))
        self.sparse_rows = [tuple((i, v) for i, v in enumerate(row) if v) for row in self.rows]
        self.n = len(self.rows)
        assert self.n == 4 * k * (k - 1)

    def values(self, point: Vector) -> tuple[Q, ...]:
        assert len(point) == self.d
        return tuple(sum((coefficient * point[i] for i, coefficient in row), Q(0))
                     for row in self.sparse_rows)

    def feasible(self, point: Vector) -> bool:
        return all(value <= bound for value, bound in zip(self.values(point), self.rhs, strict=True))

    def tight(self, point: Vector) -> set[int]:
        return {i for i, (value, bound) in enumerate(zip(self.values(point), self.rhs, strict=True))
                if value == bound}

    def direction(self, coordinate: int) -> Vector:
        return tuple(Q(int(j == coordinate)) for j in range(self.d))

    def point(self, processed: set[int], lifted: bool) -> Vector:
        coordinates = [Q(int(i in processed)) for i in range(self.k)] + [Q(0)] * len(self.arcs)
        if lifted:
            for (i, j), index in self.position.items():
                coordinates[index] = Q(int(i in processed and j not in processed))
        return tuple(coordinates)

    def maximal_step(self, x: Vector, y: Vector) -> None:
        assert self.feasible(x) and self.feasible(y) and x != y
        change = tuple(b-a for a, b in zip(x, y, strict=True))
        changes = self.values(change)
        # A row already tight at y and increasing along the displacement
        # certifies infeasibility for EVERY normalized t>1, not one sample t.
        assert any(changes[i] > 0 for i in self.tight(y))

    def vertex(self, x: Vector) -> None:
        assert self.feasible(x)
        assert rank([self.rows[i] for i in self.tight(x)], self.d) == self.d

    def edge(self, x: Vector, y: Vector) -> int:
        self.vertex(x)
        self.vertex(y)
        common = self.tight(x) & self.tight(y)
        common_rank = rank([self.rows[i] for i in common], self.d)
        assert common_rank == self.d - 1
        self.maximal_step(x, y)
        return common_rank

    def irredundancy_witness(self, row_index: int) -> Vector:
        role, i, j, sign = self.descriptions[row_index]
        value = Q(1, 4) if role == 'tail' else Q(3, 4)
        coordinates = [value] * self.k + [Q(0)] * len(self.arcs)
        coordinates[self.position[i, j]] = sign * Q(1, 2)
        witness = tuple(coordinates)
        violated = {r for r, (v, b) in enumerate(zip(self.values(witness), self.rhs, strict=True)) if v > b}
        assert violated == {row_index}
        return witness


def check(k: int) -> dict:
    p = CoupledFamily(k)
    interior = tuple([Q(1, 2)] * k + [Q(0)] * len(p.arcs))
    assert all(v < b for v, b in zip(p.values(interior), p.rhs, strict=True))
    for i in range(p.n):
        p.irredundancy_witness(i)
    source, target = p.point(set(), False), p.point(set(range(k)), False)
    p.vertex(source)
    p.vertex(target)
    supports = []
    for i in range(k):
        values = p.values(p.direction(i))
        neutral = [row for row, value in zip(p.rows, values, strict=True) if value == 0]
        assert rank(neutral, p.d) == p.d-1
        supports.append({r for r, value in enumerate(values) if value != 0})
    assert all(supports[i].isdisjoint(supports[j]) for i in range(k) for j in range(i))
    stages = []
    for s in range(k):
        processed = set(range(s))
        x, y = p.point(processed, False), p.point(processed | {s}, False)
        p.maximal_step(x, y)
        common = p.tight(x) & p.tight(y)
        common_rank = rank([p.rows[i] for i in common], p.d)
        carrier_dimension = p.d - common_rank
        assert carrier_dimension == (s+1)*(k-s)
        # At fixed binary controls, each processed->unprocessed z-coordinate
        # varies independently, all other z-coordinates are forced to zero.
        free_arcs = [(i,j) for i,j in p.arcs if i in processed and j not in processed]
        active_rank = rank([p.rows[i] for i in p.tight(x)], p.d)
        assert p.d-active_rank == len(free_arcs) == s*(k-s)
        if free_arcs:
            displacement = p.direction(p.position[free_arcs[0]])
            for sign in (-1,1):
                perturbed = tuple(a + sign*Q(1,2)*b for a,b in zip(x,displacement,strict=True))
                assert p.feasible(perturbed)
        lifted_x = p.point(processed, True)
        lifted_y = p.point(processed | {s}, True)
        lifted_common_rank = p.edge(lifted_x, lifted_y)
        stages.append({'processed_controls': s, 'control_only_carrier_dimension': carrier_dimension,
                       'control_only_active_defect': carrier_dimension-1,
                       'control_only_source_face_dimension': s*(k-s),
                       'lifted_step_common_rank': lifted_common_rank})
    # Exhaustive order check for k<=6 of the explicit feasible/maximal steps
    # and their common-row sets. Rank is transported by an explicit coordinate
    # relabeling, not recomputed for every permutation.
    permutation_count = 0
    if k <= 6:
        for order in permutations(range(k)):
            processed = set()
            for s, moving in enumerate(order):
                x, y = p.point(processed, False), p.point(processed | {moving}, False)
                p.maximal_step(x, y)
                canonical_common = p.tight(p.point(set(range(s)), False)) & p.tight(p.point(set(range(s+1)), False))
                actual_common = p.tight(x) & p.tight(y)
                descriptions = {p.descriptions[i] for i in actual_common}
                relabeled = {(role,order[i],order[j],sign) for index in canonical_common
                             for role,i,j,sign in [p.descriptions[index]]}
                assert descriptions == relabeled
                processed.add(moving)
            permutation_count += 1
    max_h = max(stage['control_only_carrier_dimension'] for stage in stages)
    assert max_h == (k+1)**2//4
    return {'k': k, 'dimension': p.d, 'irredundant_rows': p.n,
            'prescribed_circuit_steps': k, 'pairwise_row_disjoint_directions': True,
            'maximum_carrier_dimension_in_every_order': max_h,
            'maximum_active_defect_in_every_order': max_h-1,
            'explicit_alternative_edge_route_length': k,
            'orders_checked_by_exact_relabeling': permutation_count, 'stages': stages}


def run() -> dict:
    instances = [check(k) for k in range(2,9)]
    # The four-dimensional first member is small enough for independent hull
    # enumeration and graph BFS using the other regression module.
    from test_circuit_carrier_defect import Polytope
    family = CoupledFamily(2)
    p = Polytope('coupled_commuting_nonvertex_obstruction', family.rows, family.rhs)
    x, y = family.point(set(),False), family.point({0,1},False)
    assert len(p.vertices) == 6 and p.distances[x][y] == 2
    intermediates = [family.point({i},False) for i in range(2)]
    assert all(q not in p.graph for q in intermediates)
    return {'evidence_level': 'exact rational finite certificates; all-k proof in research note',
            'boundedness_argument': '0<=x_i<=1 and |z_ij|<=1 follow directly from the paired inequalities',
            'full_hull_bfs_only_k2': {'dimension':4, 'vertices':6, 'endpoint_distance':2,
                                    'both_control_only_intermediates_are_nonvertices':True},
            'larger_instances': 'No full hull or BFS. Active-row and common-row ranks certify supplied vertices and edges.',
            'instances': instances,
            'totals': {'irredundancy_witnesses':sum(x['irredundant_rows'] for x in instances),
                       'canonical_circuit_steps':sum(x['prescribed_circuit_steps'] for x in instances),
                       'alternative_edge_steps':sum(x['explicit_alternative_edge_route_length'] for x in instances),
                       'orders_checked':sum(x['orders_checked_by_exact_relabeling'] for x in instances)}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    text = json.dumps(run(), sort_keys=True, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
