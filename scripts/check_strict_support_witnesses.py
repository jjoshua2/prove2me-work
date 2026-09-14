#!/usr/bin/env python3
"""Exact rational regression tests for strict-feasibility support witnesses.

No Lean, network, floating point, or external LP solver is used. These finite
checks are NOT formal verification of the universal Lean candidate.
Run from the repository root, optionally with --out receipt.json.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path
from typing import Sequence

Vector = tuple[F, ...]
Matrix = tuple[Vector, ...]


def dot(x: Sequence[F], y: Sequence[F]) -> F:
    if len(x) != len(y):
        raise ValueError("dimension mismatch")
    return sum((a * b for a, b in zip(x, y)), F(0))


def solve_unique(A: Sequence[Sequence[F]], b: Sequence[F], n: int) -> Vector | None:
    """Gauss-Jordan solve, rejecting inconsistent or underdetermined systems."""
    if len(A) != len(b) or any(len(row) != n for row in A):
        raise ValueError("bad linear system dimensions")
    aug = [list(row) + [rhs] for row, rhs in zip(A, b)]
    pivots: list[int] = []
    for j in range(n):
        pivot = next((i for i in range(len(pivots), len(aug)) if aug[i][j]), None)
        if pivot is None:
            continue
        r = len(pivots)
        aug[r], aug[pivot] = aug[pivot], aug[r]
        q = aug[r][j]
        aug[r] = [v / q for v in aug[r]]
        for i in range(len(aug)):
            if i != r:
                q = aug[i][j]
                aug[i] = [u - q * v for u, v in zip(aug[i], aug[r])]
        pivots.append(j)
    if any(not any(row[:n]) and row[n] for row in aug) or len(pivots) != n:
        return None
    result = [F(0)] * n
    for r, j in enumerate(pivots):
        result[j] = aug[r][n]
    return tuple(result)


def vertices(A: Matrix, b: Vector, d: int) -> tuple[list[Vector], int]:
    found: set[Vector] = set()
    checked = 0
    for S in itertools.combinations(range(len(A)), d):
        checked += 1
        x = solve_unique([A[i] for i in S], [b[i] for i in S], d)
        if x is not None and all(dot(row, x) <= rhs for row, rhs in zip(A, b)):
            found.add(x)
    return sorted(found), checked


def dual_at(A: Matrix, b: Vector, f: Vector, x: Vector) -> Vector:
    active = [i for i, row in enumerate(A) if dot(row, x) == b[i]]
    for size in range(min(len(f), len(active)) + 1):
        for S in itertools.combinations(active, size):
            u = solve_unique([[A[i][j] for i in S] for j in range(len(f))], f, size)
            if u is not None and all(v >= 0 for v in u):
                alpha = [F(0)] * len(A)
                for i, v in zip(S, u):
                    alpha[i] = v
                return tuple(alpha)
    raise AssertionError("no exact active-row dual witness")


def check_witness(A: Matrix, b: Vector, f: Vector, o: Vector,
                  x: Vector, alpha: Vector, maximum: F) -> bool:
    m, d = len(A), len(f)
    if len(b) != m or len(alpha) != m or len(x) != d or len(o) != d:
        return False
    return (
        all(dot(A[i], o) < b[i] for i in range(m))
        and all(dot(A[i], x) <= b[i] for i in range(m))
        and all(v >= 0 for v in alpha)
        and all(sum((alpha[i] * A[i][j] for i in range(m)), F(0)) == f[j] for j in range(d))
        and dot(alpha, b) == dot(f, x) == maximum
        and all(alpha[i] * (b[i] - dot(A[i], x)) == 0 for i in range(m))
    )


def check_homogenization(A: Matrix, b: Vector, f: Vector, o: Vector,
                         M: F, y: Vector, lam: F, nu: F) -> bool:
    """Check the ACTUAL stacked dual-variable system and its RHS identity."""
    m, d = len(A), len(f)
    delta = tuple(b[i] - dot(A[i], o) for i in range(m))
    assert all(z > 0 for z in delta)
    R = sum((1 / z for z in delta), F(0))
    assert all(R * z >= 1 for z in delta)
    p = tuple(max(-t, F(0)) for t in y)
    q = tuple(max(t, F(0)) for t in y)
    # Alpha-coordinate inequality rows: A^T, -A^T, and the cost row b.
    C = tuple(tuple(A[i][j] for i in range(m)) for j in range(d))
    C += tuple(tuple(-A[i][j] for i in range(m)) for j in range(d))
    C += (b,)
    rhs = f + tuple(-t for t in f) + (M,)
    v = p + q + (lam,)
    eta = lam + nu
    mu = tuple(sum((v[u] * C[u][i] for u in range(2 * d + 1)), F(0))
               + nu * delta[i] for i in range(m))
    expected = tuple(eta * b[i] - dot(A[i], y) - nu * dot(A[i], o) for i in range(m))
    assert mu == expected
    assert all(sum((v[u] * C[u][i] for u in range(2 * d + 1)), F(0))
               + nu * delta[i] - mu[i] == 0 for i in range(m))
    value = dot(v, rhs) + nu * (M - dot(f, o))
    assert value == eta * M - dot(f, y) - nu * dot(f, o)
    if not all(z >= 0 for z in mu):
        return False
    if eta > 0:
        recovered = tuple((y[j] + nu * o[j]) / eta for j in range(d))
        assert all(dot(row, recovered) <= bound for row, bound in zip(A, b))
    else:
        assert lam == nu == 0
        assert all(dot(row, y) <= 0 for row in A)
    return value >= 0


def make_box(rng: random.Random, d: int) -> tuple[Matrix, Vector, Vector, list[Vector]]:
    # Invertible triangular chart: T(x-o) lies in [-radius,radius].
    T = tuple(tuple(F(rng.choice([-3, -2, -1, 1, 2, 3])) if i == j
                    else F(rng.randint(-3, 3)) if j > i else F(0)
                    for j in range(d)) for i in range(d))
    o = tuple(F(rng.randint(-5, 5), rng.randint(1, 3)) for _ in range(d))
    radii = tuple(F(rng.randint(1, 5), rng.randint(1, 3)) for _ in range(d))
    A = list(T) + [tuple(-v for v in row) for row in T]
    b = [dot(T[i], o) + radii[i] for i in range(d)]
    b += [-dot(T[i], o) + radii[i] for i in range(d)]
    # Redundant active combinations, repeated/scaled facets, and a harmless zero row.
    if d:
        for _ in range(2):
            weights = [F(rng.randint(0, 2)) for _ in range(2 * d)]
            if not any(weights):
                weights[0] = F(1)
            A.append(tuple(sum((weights[i] * A[i][j] for i in range(2 * d)), F(0)) for j in range(d)))
            b.append(sum((weights[i] * b[i] for i in range(2 * d)), F(0)) + F(rng.randint(0, 1)))
        A.append(tuple(2 * v for v in A[0]))
        b.append(2 * b[0])
    A.append(tuple(F(0) for _ in range(d)))
    b.append(F(1))
    corners = []
    for signs in itertools.product((-1, 1), repeat=d):
        u = solve_unique(T, [signs[i] * radii[i] for i in range(d)], d)
        assert u is not None
        corners.append(tuple(o[i] + u[i] for i in range(d)))
    return tuple(A), tuple(b), o, sorted(corners)


def run() -> dict:
    rng = random.Random(20260913)
    counts = {k: 0 for k in (
        "bounded_systems", "active_bases_checked", "vertices_compared",
        "optimality_certificates", "nonsharp_valid_bounds", "positive_eta_tests",
        "zero_eta_tests", "unbounded_certificates", "rejected_controls")}
    digest_rows: list[str] = []
    for d in range(4):
        for _ in range(12):
            A, b, o, corners = make_box(rng, d)
            verts, checks = vertices(A, b, d)
            assert verts == corners, "original-H and chart-corner enumerations disagree"
            counts["bounded_systems"] += 1
            counts["active_bases_checked"] += checks
            counts["vertices_compared"] += len(verts)
            objectives = [tuple(F(0) for _ in range(d))]
            objectives += [tuple(F(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(d)) for _ in range(6)]
            for f in objectives:
                x = max(verts, key=lambda u: dot(f, u))
                M = dot(f, x)
                alpha = dual_at(A, b, f, x)
                assert check_witness(A, b, f, o, x, alpha, M)
                counts["optimality_certificates"] += 1
                delta = tuple(b[i] - dot(A[i], o) for i in range(len(A)))
                assert dot(alpha, delta) == M - dot(f, o)
                epsilon = min(delta)
                assert sum(alpha, F(0)) <= (M - dot(f, o)) / epsilon
                assert dot(alpha, b) <= M + 1
                counts["nonsharp_valid_bounds"] += 1
                for lam, nu in [(F(1), F(0)), (F(0), F(1)), (F(2, 3), F(5, 2))]:
                    eta = lam + nu
                    y = tuple(eta * x[j] - nu * o[j] for j in range(d))
                    assert check_homogenization(A, b, f, o, M, y, lam, nu)
                    counts["positive_eta_tests"] += 1
                assert not check_witness(A, b, f, o, x, alpha, M + 1)
                counts["rejected_controls"] += 1
                # A too-small M produces a genuine negative dual RHS, not an allocation witness.
                assert not check_homogenization(A, b, f, o, M - 1, x, F(1), F(0))
                counts["rejected_controls"] += 1
                digest_rows.append(str((A, b, f, x, alpha)))
    # An unbounded strip: x<=3, -1<=y<=1. Strict point (0,0), recession (-1,0).
    A = ((F(1), F(0)), (F(0), F(1)), (F(0), F(-1)))
    b, o = (F(3), F(1), F(1)), (F(0), F(0))
    for a0 in (F(0), F(1, 2), F(2)):
        for a1 in (F(-3), F(0), F(5, 2)):
            f = a0, a1
            x = F(3), (F(1) if a1 >= 0 else F(-1))
            alpha = a0, max(a1, F(0)), max(-a1, F(0))
            M = dot(f, x)
            assert check_witness(A, b, f, o, x, alpha, M)
            counts["unbounded_certificates"] += 1
            for q in (F(1), F(2, 3), F(5)):
                assert check_homogenization(A, b, f, o, M, (-q, F(0)), F(0), F(0))
                counts["zero_eta_tests"] += 1
    # Strictness must never be inferred from a lower-dimensional feasible set.
    assert not check_witness(((F(1),), (F(-1),)), (F(0), F(0)),
                             (F(1),), (F(0),), (F(0),), (F(1), F(0)), F(0))
    counts["rejected_controls"] += 1
    # Negative multipliers and false objective representation are rejected.
    assert not check_witness(A, b, (F(1), F(0)), o, (F(3), F(0)),
                             (F(-1), F(0), F(0)), F(3))
    assert not check_witness(A, b, (F(1), F(1)), o, (F(3), F(1)),
                             (F(1), F(0), F(0)), F(4))
    counts["rejected_controls"] += 2
    return {"kind": "executed_exact_rational_regression_not_Lean_verification", "status": "PASS",
            "seed": 20260913, "counts": counts,
            "case_sha256": hashlib.sha256("\n".join(digest_rows).encode()).hexdigest(),
            "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    receipt = run()
    text = json.dumps(receipt, indent=2) + "\n"
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
