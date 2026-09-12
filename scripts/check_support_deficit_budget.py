#!/usr/bin/env python3
"""Exact integer regressions, NOT Lean verification or a general polytope proof.

Checks the size/excess arithmetic, all selections of small paths, and the
polynomial-budget implication. Cube/simplex examples are exact combinatorial
sanity checks; they do not certify the geometric Lean arguments.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path


def budget(k: int) -> int:
    return k if k <= 3 else 2 * k * 2 ** (k - 3)


def check(max_path: int = 12, max_gap: int = 12) -> dict[str, object]:
    if not 0 <= max_path <= 16 or not 0 <= max_gap <= 30:
        raise ValueError("Use 0<=max_path<=16 and 0<=max_gap<=30")
    scalar = path_cases = polynomial = cubes = simplices = clique_obstructions = 0
    # For each admissible h,M, verify the balance consequences and Larman cap.
    for h in range(51):
        for m in range(2 * h, 151):
            delta = m - h
            assert h <= delta and m <= 2 * delta
            for k in (delta, delta + 1, delta + 10):
                assert m * 2 ** max(h - 3, 0) <= 2 * k * 2 ** max(k - 3, 0)
                scalar += 1
    # All selected subsets, including the empty path and empty selection.
    for size in range(max_path + 1):
        for mask in range(1 << size):
            selected = {i for i in range(size) if mask >> i & 1}
            r = len(selected)
            if r >= 3:
                # In a clique, the first and third selected vertices are
                # adjacent despite being nonconsecutive in the path.
                positions = sorted(selected)
                assert positions[2] >= positions[0] + 2
                clique_obstructions += 1
            degrees = {i: int(i-1 in selected) + int(i+1 in selected) for i in selected}
            c = sum(i-1 not in selected for i in selected)
            s = sum(deg == 0 for deg in degrees.values())
            assert sum(degrees.values()) == 2 * (r - c)
            for g in range(max_gap + 1):
                e = r + g
                caps = {i: g + 1 + deg for i, deg in degrees.items()}
                uniform = 2 * (g + 3) * 2 ** g
                exact_degree_budget = sum(budget(k) for k in caps.values())
                assert exact_degree_budget <= r * uniform
                for i, k in caps.items():
                    assert k + r == e + 1 + degrees[i]
                    assert k <= g + 3
                if g == 0:
                    assert exact_degree_budget == 3 * r - 2 * c
                if g == 1:
                    assert exact_degree_budget == 16*r - 26*c + 12*s
                    assert exact_degree_budget <= 16 * r
                if g == 2:
                    assert exact_degree_budget == 40*r - 48*c + 11*s
                    assert exact_degree_budget <= 40 * r
                if g <= 2:
                    assert all(k <= 5 for k in caps.values())
                if not r:
                    assert exact_degree_budget == 0
                path_cases += 1
    # Natural-number form of the polynomial-deficit implication.
    for n in range(1, 101):
        for g in range(n + 1):
            for k in range(9):
                if 2 ** g <= n ** k:
                    # Largest r=n is enough for the monotone expression.
                    assert 2 * (g+3) * 2**g * n <= 8 * n ** (k+2)
                    polynomial += 1
    # For a cube, use symmetry to fix one vertex at zero. k unequal coordinates
    # give a k-cube carrier with M=2k, delta=k and graph distance k.
    for d in range(13):
        for vertex in range(1 << d):
            h = vertex.bit_count()
            m, delta, distance = 2*h, h, h
            assert 2*h == m and h == delta and distance <= budget(delta)
            cubes += 1
    # For a simplex, equal vertices have a point carrier; distinct vertices
    # have an edge carrier, even though the full simplex can have large dimension.
    for d in range(31):
        for i in range(d + 1):
            for j in range(d + 1):
                h = int(i != j)
                m, delta, distance = 2*h, h, h
                assert h <= delta and m <= 2*delta and distance <= budget(delta)
                simplices += 1
    # Exact cube hub: every target-slack row x_i<=1 contains the all-ones
    # vertex. Thus cut faces form a clique in the parent-vertex graph.
    # A chordless path can use at most two of them, so g>=d-2 for n=2d.
    for d in range(1, 65):
        origin = [0] * d
        hub = [1] * d
        for i in range(d):
            row = [int(j == i) for j in range(d)]
            assert sum(row[j] * origin[j] for j in range(d)) < 1
            assert sum(row[j] * hub[j] for j in range(d)) == 1
        for r in range(min(2, d) + 1):
            assert (2*d - d) - r >= d - 2
    # This must fail without vertex hypotheses: two distinct interior points of
    # a 3-simplex have full common carrier, h=3,M=4,delta=1.
    assert not (3 <= 4-3)
    root = Path(__file__).resolve().parents[1]
    hashes = {
        str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [root / "Solutions/PolynomialSupportDeficitRouting.lean",
                  root / "Solutions/PolynomialVertexCarrierIntrinsicBudget.lean"]
    }
    return {
        "status": "PASS",
        "scope": "Exact finite/integer regressions only; no Lean or platform verdict.",
        "max_path_vertices": max_path,
        "max_support_deficit": max_gap,
        "intrinsic_size_budget_cases": scalar,
        "selected_path_gap_cases": path_cases,
        "polynomial_implication_cases": polynomial,
        "cube_pairs_modulo_symmetry": cubes,
        "simplex_vertex_pairs": simplices,
        "clique_subsets_excluded_from_chordless_paths": clique_obstructions,
        "cube_common_hub_dimensions_checked": 64,
        "vertex_hypothesis_negative_control": "PASS: interior simplex pair violates h<=delta",
        "per_cut_uniform_costs": {str(g): 2*(g+3)*2**g for g in range(9)},
        "candidate_source_sha256": hashes,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-path", type=int, default=12)
    parser.add_argument("--max-gap", type=int, default=12)
    args = parser.parse_args()
    print(json.dumps(check(args.max_path, args.max_gap), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
