#!/usr/bin/env python3
"""Exact rational certificates for the irredundant-row-count proof.

No floating point, external packages, network, or proof service is used.
These checks are finite evidence, NOT Lean compilation or a Prove2Me verdict.
Run from the repository root:
  python3 scripts/check_irredundant_row_count.py --json
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import combinations, product
import json
import random
from typing import Iterable, Sequence

Vector = tuple[Q, ...]


def vector(xs: Iterable[int | Q]) -> Vector:
    return tuple(Q(x) for x in xs)


def dot(x: Vector, y: Vector) -> Q:
    if len(x) != len(y):
        raise ValueError("Dimension mismatch")
    return sum((a * b for a, b in zip(x, y)), Q(0))


def add(x: Vector, y: Vector) -> Vector:
    if len(x) != len(y):
        raise ValueError("Dimension mismatch")
    return tuple(a + b for a, b in zip(x, y))


def scale(t: Q, x: Vector) -> Vector:
    return tuple(t * a for a in x)


@dataclass(frozen=True)
class Row:
    normal: Vector
    bound: Q

    def slack(self, x: Vector) -> Q:
        return self.bound - dot(self.normal, x)


@dataclass(frozen=True)
class Model:
    name: str
    dimension: int
    rows: tuple[Row, ...]
    centre: Vector
    deletion_witnesses: tuple[Vector, ...]


@dataclass(frozen=True)
class CertifiedRow:
    row: Row
    weights: tuple[Q, ...]
    extra_slack: Q


def require(condition: bool, message: str) -> None:
    # Explicit checks remain enabled under python -O.
    if not condition:
        raise AssertionError(message)


def check_irredundancy(rows: Sequence[Row], witnesses: Sequence[Vector]) -> None:
    require(len(rows) == len(witnesses), "Wrong witness count")
    for i, w in enumerate(witnesses):
        require(rows[i].slack(w) < 0, f"Row {i} is not violated")
        require(all(r.slack(w) >= 0 for j, r in enumerate(rows) if j != i),
                f"Deletion witness {i} violates another row")


def singleton_tight_points(model: Model) -> tuple[Vector, ...]:
    require(len(model.centre) == model.dimension, "Bad centre dimension")
    require(all(len(r.normal) == model.dimension for r in model.rows), "Bad row dimension")
    require(all(r.slack(model.centre) > 0 for r in model.rows), "Centre is not strict")
    check_irredundancy(model.rows, model.deletion_witnesses)
    points = []
    for i, (r, w) in enumerate(zip(model.rows, model.deletion_witnesses)):
        denominator = dot(r.normal, w) - dot(r.normal, model.centre)
        t = r.slack(model.centre) / denominator
        require(0 < t < 1, "Bad interpolation coefficient")
        x = add(scale(1 - t, model.centre), scale(t, w))
        require(r.slack(x) == 0, "Distinguished row is not tight")
        require(all(other.slack(x) > 0 for j, other in enumerate(model.rows) if j != i),
                "Another source row is not strict")
        points.append(x)
    # The injection argument's key geometric fact, checked exactly.
    for x, y in combinations(points, 2):
        q = scale(Q(1, 2), add(x, y))
        require(all(r.slack(q) > 0 for r in model.rows), "Pair midpoint is not strict")
    return tuple(points)


def make_certified_row(model: Model, weights: Sequence[Q], extra: Q) -> CertifiedRow:
    if len(weights) != len(model.rows):
        raise ValueError("Weight count mismatch")
    if extra < 0 or any(w < 0 for w in weights):
        raise ValueError("Certificate is not a nonnegative implication")
    a = tuple(sum((w * r.normal[k] for w, r in zip(weights, model.rows)), Q(0))
              for k in range(model.dimension))
    b = sum((w * r.bound for w, r in zip(weights, model.rows)), Q(0)) + extra
    return CertifiedRow(Row(a, b), tuple(weights), extra)


def comparison(model: Model, seed: int) -> tuple[CertifiedRow, ...]:
    rng = random.Random(seed)
    n = len(model.rows)
    result = []
    # A positive multiple of EVERY original row certifies the reverse inclusion.
    for i in range(n):
        weights = [Q(0)] * n
        weights[i] = Q(rng.randint(1, 7), rng.randint(1, 7))
        result.append(make_certified_row(model, weights, Q(0)))
    # Includes duplicate facet rows, implied rows touching lower-dimensional
    # faces, strictly redundant inequalities, and both kinds of zero tautology.
    for k in range(2 * n + 7):
        weights = [Q(0)] * n
        if n and k % 5:
            for _ in range(1 + k % min(4, n)):
                weights[rng.randrange(n)] += Q(rng.randint(1, 5), rng.randint(1, 5))
        extra = Q(0) if k % 3 else Q(rng.randint(1, 5), rng.randint(1, 5))
        result.append(make_certified_row(model, weights, extra))
    result.append(make_certified_row(model, [Q(0)] * n, Q(0)))
    result.append(make_certified_row(model, [Q(0)] * n, Q(1)))
    rng.shuffle(result)
    return tuple(result)


def check_equivalence_certificate(model: Model, target: Sequence[CertifiedRow]) -> None:
    n = len(model.rows)
    reverse = set()
    for cert in target:
        require(all(w >= 0 for w in cert.weights) and cert.extra_slack >= 0,
                "Invalid implication signs")
        rebuilt = make_certified_row(model, cert.weights, cert.extra_slack)
        require(rebuilt.row == cert.row, "Incorrect coefficient identity")
        active = [i for i, w in enumerate(cert.weights) if w]
        if len(active) == 1 and cert.extra_slack == 0:
            reverse.add(active[0])
    require(reverse == set(range(n)), "Missing reverse-inclusion row")


def check_blocker_injection(model: Model, points: Sequence[Vector],
                            target: Sequence[CertifiedRow]) -> int:
    check_equivalence_certificate(model, target)
    blockers = []
    for i, x in enumerate(points):
        require(all(c.row.slack(x) >= 0 for c in target), "Witness not comparison-feasible")
        active = {j for j, c in enumerate(target)
                  if any(c.row.normal) and c.row.slack(x) == 0}
        require(bool(active), f"No nonzero blocker for source row {i}")
        blockers.append(active)
    # This tests ALL blocker selections, not just one greedy matching.
    for left, right in combinations(blockers, 2):
        require(left.isdisjoint(right), "Two distinct source facets share a blocker")
    require(len(points) <= len(target), "Cardinality inequality failed")
    for c in target:
        if any(c.row.normal):
            require(c.row.slack(model.centre) > 0, "Nonzero valid row tight at strict centre")
    return sum(map(len, blockers))


def axis(d: int, i: int, sign: int = 1) -> Vector:
    return vector(sign if k == i else 0 for k in range(d))


def box(d: int, deformed: bool = False) -> Model:
    rows, witnesses = [], []
    for i in range(d):
        for sign in (-1, 1):
            a = list(axis(d, i, sign))
            if deformed and i:
                a[i - 1] = Q(1, 4)
            rows.append(Row(tuple(a), Q(1)))
            witnesses.append(scale(Q(2), axis(d, i, sign)))
    return Model(f"{'deformed-' if deformed else ''}box-{d}", d,
                 tuple(rows), vector([0] * d), tuple(witnesses))


def simplex(d: int) -> Model:
    rows = [Row(axis(d, i, -1), Q(0)) for i in range(d)]
    rows.append(Row(vector([1] * d), Q(1)))
    witnesses = [axis(d, i, -1) for i in range(d)] + [scale(Q(2), axis(d, 0))]
    return Model(f"simplex-{d}", d, tuple(rows), vector([Q(1, d + 1)] * d), tuple(witnesses))


def cross_polytope(d: int) -> Model:
    normals = [vector(s) for s in product((-1, 1), repeat=d)]
    return Model(f"cross-polytope-{d}", d, tuple(Row(a, Q(1)) for a in normals),
                 vector([0] * d), tuple(scale(Q(1, d - 1), a) for a in normals))


def orthant(d: int) -> Model:
    return Model(f"unbounded-orthant-{d}", d,
                 tuple(Row(axis(d, i, -1), Q(0)) for i in range(d)),
                 vector([1] * d), tuple(axis(d, i, -1) for i in range(d)))


def transformed(model: Model) -> Model:
    d = model.dimension
    translation = vector(Q(k + 1, 3) for k in range(d))
    def transform_point(x: Vector) -> Vector:
        y = list(x)
        if d >= 2:
            y[0] += x[1]
        return add(tuple(y), translation)
    rows = []
    for r in model.rows:
        a = list(r.normal)
        if d >= 2:
            a[1] -= a[0]
        rows.append(Row(tuple(a), r.bound + dot(tuple(a), translation)))
    return Model(model.name + "-sheared-translated", d, tuple(rows),
                 transform_point(model.centre), tuple(map(transform_point, model.deletion_witnesses)))


def models() -> tuple[Model, ...]:
    base = [box(d) for d in range(1, 6)] + [simplex(d) for d in range(1, 6)]
    base += [cross_polytope(d) for d in range(2, 6)]
    base += [box(3, True), box(5, True), orthant(2), orthant(4)]
    base.append(Model("carrier-hexagon", 2,
        tuple(Row(vector(a), Q(b)) for a, b in
              [((1, 0), 1), ((-1, 0), 1), ((0, 1), 1), ((0, -1), 1),
               ((1, 1), Q(3, 2)), ((-1, -1), Q(3, 2))]), vector([0, 0]),
        tuple(vector(w) for w in [(Q(5, 4), Q(-1, 2)), (Q(-5, 4), Q(1, 2)),
                                 (Q(-1, 2), Q(5, 4)), (Q(1, 2), Q(-5, 4)), (1, 1), (-1, -1)])))
    base.append(Model("unbounded-halfspace-3", 3, (Row(vector([-1, 0, 0]), Q(0)),),
                      vector([1, 0, 0]), (vector([-1, 0, 0]),)))
    base.append(Model("empty-row-system-3", 3, (), vector([0, 0, 0]), ()))
    return tuple(base + [transformed(m) for m in base])


def check_full_dimension_counterexample() -> dict[str, object]:
    a = tuple(Row(vector(v), Q(0)) for v in [(1, 0), (-1, 0), (0, 1), (0, -1)])
    b = tuple(Row(vector(v), Q(0)) for v in [(1, 0), (0, 1), (-1, -1)])
    check_irredundancy(a, tuple(r.normal for r in a))
    check_irredundancy(b, tuple(vector(v) for v in [(1, 0), (0, 1), (-1, -1)]))
    # Every row of either description is an exact nonnegative combination
    # of the other's rows. Hence equality holds for all real x, not samples.
    def check_direction(source: Sequence[Row], target: Sequence[Row], weights: Sequence[Sequence[int]]) -> None:
        for r, ws in zip(target, weights):
            require(all(w >= 0 for w in ws), "Invalid counterexample combination")
            normal = tuple(sum((Q(w) * s.normal[k] for w, s in zip(ws, source)), Q(0)) for k in range(2))
            bound = sum((Q(w) * s.bound for w, s in zip(ws, source)), Q(0))
            require(Row(normal, bound) == r, "Counterexample implication identity failed")
    check_direction(b, a, [[1, 0, 0], [0, 1, 1], [0, 1, 0], [1, 0, 1]])
    check_direction(a, b, [[1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]])
    # A positive linear dependence summing all left sides and bounds to zero
    # certifies that simultaneous strict inequalities are impossible.
    for rows in (a, b):
        require(all(sum((r.normal[k] for r in rows), Q(0)) == 0 for k in range(2)),
                "Missing strict-infeasibility certificate")
        require(sum((r.bound for r in rows), Q(0)) == 0, "Wrong strict-infeasibility bounds")
    return {"same_set": "singleton origin in R^2", "irredundant_row_counts": [4, 3],
            "strict_feasibility": False, "both_directions_exactly_certified": True}


def run() -> dict[str, object]:
    systems = models()
    point_count = midpoint_count = comparisons = blocker_checks = 0
    names = []
    for m in systems:
        points = singleton_tight_points(m)
        names.append(m.name)
        point_count += len(points)
        midpoint_count += len(points) * (len(points) - 1) // 2
        for seed in range(6):
            blocker_checks += check_blocker_injection(m, points, comparison(m, seed))
            comparisons += 1
    return {
        "status": "PASS",
        "evidence_level": "exact rational finite certificates; not Lean or Prove2Me verification",
        "source_models": len(systems), "comparison_presentations": comparisons,
        "single_tight_points": point_count, "strict_pair_midpoints": midpoint_count,
        "nonzero_tight_blockers_checked": blocker_checks,
        "lower_dimensional_counterexample": check_full_dimension_counterexample(),
        "models": names,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Print a structured certificate receipt")
    args = parser.parse_args()
    result = run()
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"PASS: {result['source_models']} source models; "
              f"{result['comparison_presentations']} equivalent comparison presentations; "
              f"{result['single_tight_points']} singleton-tight witnesses.")
        print("The strict-feasibility counterexample also passed (4 rows versus 3 for the same point).")
        print("No Lean compilation or Prove2Me publication was performed.")


if __name__ == "__main__":
    main()
