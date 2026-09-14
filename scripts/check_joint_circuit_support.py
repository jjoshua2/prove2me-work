#!/usr/bin/env python3
"""Exact regressions for the joint-circuit support/zero-deficit theorem.

Standard library only. Enumeration uses rational RREF; returned circuit
minimality is checked independently by a nonzero minor, using Bareiss
elimination. This is executable mathematical evidence, NOT Lean verification
or a proof of the Python enumerator's universal correctness.

Run: python3 scripts/check_joint_circuit_support.py --out receipt.json
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
from typing import Iterable, Sequence

Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def dot(x: Sequence[F], y: Sequence[F]) -> F:
    require(len(x) == len(y), "dot-product dimension mismatch")
    return sum((a * b for a, b in zip(x, y)), F(0))


@dataclass(frozen=True)
class JointRows:
    m: int
    r: int
    k: int
    a: tuple[tuple[Vector, ...], ...]

    def __post_init__(self) -> None:
        require(min(self.m, self.r, self.k) >= 0, "negative dimension")
        require(len(self.a) == self.m, "original-row count mismatch")
        for row in self.a:
            require(len(row) == self.r, "block count mismatch")
            for block in row:
                require(len(block) == self.k, "generator count mismatch")
                require(all(isinstance(x, F) for x in block), "use exact Fractions")

    @property
    def n(self) -> int:
        return self.m + self.r * (self.k + 1)

    def total(self, l: int) -> int:
        return self.m + l * (self.k + 1)

    def nonneg(self, l: int, j: int) -> int:
        return self.total(l) + 1 + j

    def transpose(self) -> Matrix:
        rows = []
        for l in range(self.r):
            for j in range(self.k):
                row = [F(0)] * self.n
                for i in range(self.m):
                    row[i] = -self.a[i][l][j]
                row[self.total(l)] = F(1)
                row[self.nonneg(l, j)] = F(-1)
                rows.append(tuple(row))
        return tuple(rows)

    def supports(self) -> tuple[Vector, ...]:
        return tuple(tuple(max((F(0), *self.a[i][l])) for i in range(self.m))
                     for l in range(self.r))

    def value(self, i: int, l: int, q: int) -> F:
        # q=0 is the anchor; q=j+1 is listed generator j.
        return F(0) if q == 0 else self.a[i][l][q - 1]


def kernel_basis(matrix: Matrix, width: int) -> list[Vector]:
    """Rational RREF, used ONLY by the small-instance enumerator."""
    a = [list(row) for row in matrix]
    require(all(len(row) == width for row in a), "matrix width mismatch")
    pivots: list[int] = []
    rank = 0
    for col in range(width):
        p = next((i for i in range(rank, len(a)) if a[i][col]), None)
        if p is None:
            continue
        a[rank], a[p] = a[p], a[rank]
        scale = a[rank][col]
        a[rank] = [x / scale for x in a[rank]]
        for i in range(len(a)):
            if i != rank and a[i][col]:
                q = a[i][col]
                a[i] = [u - q * v for u, v in zip(a[i], a[rank])]
        pivots.append(col)
        rank += 1
    result = []
    for free in (j for j in range(width) if j not in pivots):
        x = [F(0)] * width
        x[free] = F(1)
        for i, p in enumerate(pivots):
            x[p] = -a[i][free]
        result.append(tuple(x))
    return result


def determinant(matrix: Sequence[Sequence[F]]) -> F:
    """Independent Bareiss determinant; no use of the RREF routine."""
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "minor is not square")
    if not n:
        return F(1)
    a = [list(row) for row in matrix]
    previous, sign = F(1), F(1)
    for k in range(n - 1):
        p = next((i for i in range(k, n) if a[i][k]), None)
        if p is None:
            return F(0)
        if p != k:
            a[p], a[k] = a[k], a[p]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                a[i][j] = (pivot * a[i][j] - a[i][k] * a[k][j]) / previous
        for i in range(k + 1, n):
            a[i][k] = F(0)
        previous = pivot
    return sign * a[-1][-1]


def validate_null(system: JointRows, w: Vector, *, nonzero: bool = True) -> None:
    require(len(w) == system.n, "multiplier dimension mismatch")
    require(all(isinstance(x, F) for x in w), "multipliers must be exact Fractions")
    require(all(x >= 0 for x in w), "negative multiplier")
    require(not nonzero or any(w), "zero multiplier")
    require(all(dot(row, w) == 0 for row in system.transpose()), "not an original-matrix null vector")


def check_circuit(system: JointRows, w: Vector) -> dict:
    """Certify rank = support size minus one by a nonzero minor and A*w=0.

    Strict positivity on the support then implies support-minimality. This
    checker searches for a rank witness; it never calls the RREF enumerator.
    """
    validate_null(system, w)
    support = tuple(i for i, x in enumerate(w) if x)
    rank = len(support) - 1
    matrix = system.transpose()
    require(rank <= len(matrix), "support exceeds the rank-plus-one cutoff")
    for rs in itertools.combinations(range(len(matrix)), rank):
        for cs in itertools.combinations(support, rank):
            det = determinant([[matrix[i][j] for j in cs] for i in rs])
            if det:
                return {"support": list(support), "minor_rows": list(rs),
                        "minor_columns": list(cs), "determinant": str(det)}
    raise ValueError("no rank witness: support is not minimal")


def enumerate_circuits(system: JointRows, *, max_supports: int = 100000) -> tuple[list[Vector], int]:
    matrix = system.transpose()
    cutoff = min(system.n, system.r * system.k + 1)
    from math import comb
    total = sum(comb(system.n, s) for s in range(1, cutoff + 1))
    require(total <= max_supports, "enumeration cap exceeded; no partial catalogue returned")
    result = []
    for size in range(1, cutoff + 1):
        for support in itertools.combinations(range(system.n), size):
            restricted = tuple(tuple(row[j] for j in support) for row in matrix)
            basis = kernel_basis(restricted, size)
            if len(basis) != 1:
                continue
            z = basis[0]
            if all(x < 0 for x in z):
                z = tuple(-x for x in z)
            if not all(x > 0 for x in z):
                continue
            mass = sum(z)
            w = [F(0)] * system.n
            for j, x in zip(support, z):
                w[j] = x / mass
            result.append(tuple(w))
    return result, total


def validate_support_bounds(system: JointRows, h: tuple[Vector, ...]) -> None:
    require(len(h) == system.r and all(len(row) == system.m for row in h), "support-bound dimensions")
    for l in range(system.r):
        for i in range(system.m):
            require(h[l][i] >= 0 and all(x <= h[l][i] for x in system.a[i][l]),
                    "invalid candidate support bound")


def coefficients(system: JointRows, w: Vector, h: tuple[Vector, ...]) -> Vector:
    validate_support_bounds(system, h)
    return tuple(dot(w[:system.m], h[l]) - w[system.total(l)] for l in range(system.r))


def check_external_support(system: JointRows, w: Vector, h: tuple[Vector, ...]) -> dict:
    rank_witness = check_circuit(system, w)
    require(any(w[:system.m]), "internal-only circuit is not external")
    gamma = coefficients(system, w, h)
    common_sets = []
    for l in range(system.r):
        weighted = [sum((w[i] * system.value(i, l, q) for i in range(system.m)), F(0))
                    for q in range(system.k + 1)]
        require(w[system.total(l)] == max(weighted), "total multiplier is not exact support")
        require(any(w[system.total(l) + q] == 0 for q in range(system.k + 1)),
                "no zero auxiliary coordinate")
        require(gamma[l] >= 0, "negative external-circuit deficit")
        common = [q for q in range(system.k + 1)
                  if all(system.value(i, l, q) == h[l][i]
                         for i in range(system.m) if w[i] > 0)]
        require((gamma[l] == 0) == bool(common), "zero-deficit/common-maximizer mismatch")
        common_sets.append(common)
    return {"rank_witness": rank_witness, "gamma": [str(x) for x in gamma],
            "common_maximizers": common_sets}


def tighten(system: JointRows, w: Vector) -> tuple[Vector, Vector]:
    """Remove internal slack from ANY nonnegative null vector, keeping lambda.

    The removed multiplier is a nonnegative sum of internal simplex circuits.
    This routine does not assert that the tightened vector is itself minimal.
    """
    validate_null(system, w, nonzero=False)
    z = list(w)
    removed = []
    for l in range(system.r):
        v = [sum((w[i] * system.a[i][l][j] for i in range(system.m)), F(0))
             for j in range(system.k)]
        nu = max((F(0), *v))
        delta = w[system.total(l)] - nu
        require(delta >= 0, "negative internal slack")
        removed.append(delta)
        z[system.total(l)] = nu
        for j in range(system.k):
            z[system.nonneg(l, j)] = nu - v[j]
    zt = tuple(z)
    validate_null(system, zt, nonzero=False)
    require(all(0 <= x <= y for x, y in zip(zt, w)), "tightening expanded support")
    for l, delta in enumerate(removed):
        require(all(w[system.total(l) + q] - zt[system.total(l) + q] == delta
                    for q in range(system.k + 1)), "internal reconstruction mismatch")
    return zt, tuple(removed)


def make_system(m: int, r: int, k: int, values: Iterable[int | F]) -> JointRows:
    it = iter(values)
    a = tuple(tuple(tuple(F(next(it)) for _ in range(k)) for _ in range(r)) for _ in range(m))
    require(next(it, None) is None, "too many matrix entries")
    return JointRows(m, r, k, a)


def run() -> dict:
    rng = random.Random(20260913)
    systems = [make_system(m, r, k, [0] * (m*r*k))
               for m, r, k in [(0,0,0), (0,1,0), (0,2,2), (1,0,0), (3,2,0), (2,1,2)]]
    systems += [make_system(1,1,1,[1]), make_system(2,1,1,[1,-1]),
                make_system(2,1,2,[1,1,-1,-1]),
                make_system(2,2,2,[1,0,0,1,0,1,1,0]),
                make_system(3,1,2,[0,0,1,-1,-1,1])]
    for _ in range(48):
        m, r, k = rng.randint(1,3), rng.randint(1,2), rng.randint(1,2)
        systems.append(make_system(m,r,k,[F(rng.randint(-3,3),rng.randint(1,3))
                                         for _ in range(m*r*k)]))
    counts = dict(systems=len(systems), enumerated_supports=0, circuits=0,
                  external_circuits=0, internal_circuits=0, rank_certificates=0,
                  block_support_checks=0, zero_deficit_checks=0,
                  downward_inequality_checks=0, tightening_cases=0, rejected_controls=0)
    examples = []
    for index, system in enumerate(systems):
        rays, tried = enumerate_circuits(system)
        counts['enumerated_supports'] += tried
        h = system.supports()
        for w in rays:
            check_circuit(system, w)
            counts['rank_certificates'] += 1
            counts['circuits'] += 1
            if any(w[:system.m]):
                evidence = check_external_support(system, w, h)
                counts['external_circuits'] += 1
                counts['block_support_checks'] += system.r
                counts['zero_deficit_checks'] += system.r
                # The theorem permits conservative support bounds as well.
                h2 = tuple(tuple(x + F(rng.randint(0,1),2) for x in row) for row in h)
                check_external_support(system, w, h2)
                counts['zero_deficit_checks'] += system.r
                gamma = coefficients(system,w,h)
                for _ in range(3):
                    t = tuple(F(rng.randint(0,5),3) for _ in range(system.r))
                    s = tuple(x * F(rng.randint(0,3),3) for x in t)
                    require(dot(gamma,s) <= dot(gamma,t), "downward-row inequality failed")
                    counts['downward_inequality_checks'] += 1
                if not examples and any(gamma):
                    examples.append({"system": index, "multiplier": list(map(str,w)), **evidence})
            else:
                counts['internal_circuits'] += 1
                positive_blocks = [l for l in range(system.r) if w[system.total(l)] > 0]
                require(len(positive_blocks) == 1, "internal minimal circuit crosses blocks")
                l = positive_blocks[0]
                require(all(w[system.nonneg(l,j)] == w[system.total(l)] for j in range(system.k)),
                        "internal simplex ray identity failed")
            tight, removed = tighten(system,w)
            if any(w[:system.m]):
                require(tight == w and not any(removed), "external circuit had removable internal slack")
        for _ in range(6):
            lam = tuple(F(rng.randint(0,3),2) for _ in range(system.m))
            w = list(lam) + [F(0)] * (system.n-system.m)
            for l in range(system.r):
                v = [sum((lam[i]*system.a[i][l][j] for i in range(system.m)),F(0))
                     for j in range(system.k)]
                nu = max((F(0),*v)) + F(rng.randint(0,3),2)
                w[system.total(l)] = nu
                for j in range(system.k):
                    w[system.nonneg(l,j)] = nu-v[j]
            w = tuple(w)
            tight, removed = tighten(system,w)
            gamma, tightgamma = coefficients(system,w,h), coefficients(system,tight,h)
            require(all(x >= 0 for x in tightgamma), "tightened deficit became negative")
            t = tuple(F(rng.randint(0,4),3) for _ in range(system.r))
            require(-dot(gamma,t) == -dot(tightgamma,t)+dot(removed,t), "budget identity failed")
            counts['tightening_cases'] += 1
    one = make_system(1,1,1,[1])
    h = one.supports()
    def rejects(name, action):
        try:
            action()
        except ValueError:
            counts['rejected_controls'] += 1
            return
        raise AssertionError(f"negative control accepted: {name}")
    rejects('external nonminimal ray', lambda: check_external_support(one,(F(1),F(2),F(1)),h))
    rejects('internal ray mislabeled external', lambda: check_external_support(one,(F(0),F(1),F(1)),h))
    rejects('invalid support upper bound', lambda: check_external_support(one,(F(1),F(1),F(0)),((F(0),),)))
    rejects('negative multiplier', lambda: check_circuit(one,(F(-1),F(0),F(1))))
    rejects('false null relation', lambda: check_circuit(one,(F(1),F(0),F(0))))
    rejects('zero vector', lambda: check_circuit(one,(F(0),)*3))
    rejects('partial vector', lambda: check_circuit(one,(F(1),)))
    rejects('enumeration truncation', lambda: enumerate_circuits(one,max_supports=1))
    rejects('floating point', lambda: validate_null(one,(1.0,1.0,0.0)))
    rejects('ragged rows', lambda: JointRows(1,1,2,(((F(1),),),)))
    # A nonminimal external row can even lose downward closure by itself.
    two = make_system(2,2,1,[1,1,-1,-1])
    wbad = (F(1),F(1),F(2),F(2),F(0),F(0))
    validate_null(two,wbad)
    gbad = coefficients(two,wbad,two.supports())
    require(gbad == (F(-1),F(1)), 'signed nonminimal control coefficient mismatch')
    require(dot(gbad,(F(1),F(1))) == 0 and dot(gbad,(F(0),F(1))) > 0,
            'nonminimal halfspace control failed')
    rejects('nonminimal multiblock ray', lambda: check_circuit(two,wbad))
    # Independent determinant checks against Leibniz expansion.
    det_checks = 0
    for n in range(5):
        for _ in range(12):
            a = [[F(rng.randint(-3,3)) for _ in range(n)] for _ in range(n)]
            leibniz = F(0)
            for perm in itertools.permutations(range(n)):
                inversions = sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
                term = F((-1)**inversions)
                for i,j in enumerate(perm): term *= a[i][j]
                leibniz += term
            require(determinant(a)==leibniz,"independent determinant regression failed")
            det_checks += 1
    return {"status":"PASS", "seed":20260913, "counts":counts,
            "independent_determinant_checks":det_checks,
            "example_with_positive_deficit":examples,
            "counterexample_without_minimality":{
                "a":[1], "ordering":["lambda","nu","mu"],
                "external_minimal":[1,1,0], "internal":[0,1,1],
                "nonminimal_sum":[1,2,1], "support_bound":1, "deficit":-1},
            "nonminimal_row_not_downward":{"a":[[[1],[1]],[[-1],[-1]]],
                "multiplier":[1,1,2,2,0,0], "gamma":[-1,1],
                "rhs":0, "admissible_for_this_row":[1,1],
                "smaller_but_inadmissible_for_this_row":[0,1],
                "scope":"Single nonminimal inequality only; the complete tight system rejects [1,1]."},
            "scope":"Exact finite regressions; no Lean compilation, platform acceptance, universal Python correctness, or Hirsch diameter claim."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    result = run()
    result['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text = json.dumps(result,indent=2)+'\n'
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True)
        args.out.write_text(text,encoding='utf-8')
    print(text,end='')


if __name__ == '__main__':
    main()
