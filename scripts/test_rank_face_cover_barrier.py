#!/usr/bin/env python3
"""Exact, credential-free regression certificates for face-cover research.

The assertions check finite incidence/cost models, not the Lean source and not
Polynomial Hirsch. Fractions are exact. No network access or solver is used.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import product
from math import comb
from pathlib import Path
import argparse
import json
import random


def check_general_cover_barrier(seed: int = 20260910, trials: int = 2000) -> int:
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randrange(1, 15)
        vertices = range(n)
        # Singletons make every randomly generated weighted cover feasible.
        faces = [{v} for v in vertices]
        faces += [{v for v in vertices if rng.randrange(2)}
                  for _ in range(rng.randrange(1, 20))]
        weights = [1] * n + [rng.randrange(6) for _ in faces[n:]]
        budgets = [max(0, len(face) - 1) + rng.randrange(3) for face in faces]
        incidence = [sum(w for face, w in zip(faces, weights) if v in face)
                     for v in vertices]
        q = min(incidence)
        incidence_cost = sum(w * len(face) for face, w in zip(faces, weights))
        total_cost = sum(w * (b + 1) for w, b in zip(weights, budgets))
        assert q > 0
        assert sum(incidence) == incidence_cost
        assert q * n <= incidence_cost <= total_cost
        assert total_cost // q - 1 >= n - 1
    return trials


def cube_faces(d: int):
    """-1 is a free coordinate; all-free (the parent) is excluded."""
    for face in product((-1, 0, 1), repeat=d):
        if any(c != -1 for c in face):
            yield face


def contains(face: tuple[int, ...], vertex: tuple[int, ...]) -> bool:
    return all(c == -1 or c == v for c, v in zip(face, vertex))


def child_cost(r: int, seed_dimension: int) -> int:
    """Budget plus one: true cube diameter seeds, propagated costs above them."""
    if r <= seed_dimension:
        return r + 1
    return (seed_dimension + 1) * 2 ** (r - seed_dimension)


def cube_primal_dual_certificate(d: int, k: int) -> dict[str, int | str]:
    if not 0 <= k < d:
        raise ValueError('need 0 <= seed dimension < parent dimension')
    vertices = list(product((0, 1), repeat=d))
    faces = list(cube_faces(d))
    # Uniform dual mass on vertices bounds EVERY proper face, of EVERY rank.
    dual_mass = Fraction(k + 1, 2 ** k)
    face_checks = 0
    for face in faces:
        r = face.count(-1)
        incident_count = sum(contains(face, v) for v in vertices)
        assert incident_count == 2 ** r
        assert dual_mass * incident_count <= child_cost(r, k)
        face_checks += 1
    # Matching primal: all k-faces, each with weight 1 / binomial(d,k).
    chosen = [f for f in faces if f.count(-1) == k]
    q = comb(d, k)
    for v in vertices:
        assert sum(contains(f, v) for f in chosen) == q
    primal_cost = Fraction(len(chosen) * (k + 1), q)
    dual_cost = dual_mass * len(vertices)
    assert primal_cost == dual_cost == (k + 1) * 2 ** (d - k)
    # Integer-scaled certificate produces the same bound without rounding loss.
    integer_cost = len(chosen) * (k + 1)
    assert integer_cost % q == 0
    return {
        'dimension': d,
        'seed_dimension': k,
        'vertices': len(vertices),
        'all_proper_faces_checked': face_checks,
        'selected_seed_faces': len(chosen),
        'coverage_q': q,
        'dual_mass_per_vertex': str(dual_mass),
        'optimal_certificate_budget': integer_cost // q - 1,
        'actual_cube_diameter': d,
    }


def saturation_counterexample() -> dict:
    """The valid redundant row -x-y <= 0 supports an edge of the 3-cube.

    Its own rank-one span omits -e_x, even though x=0 already holds everywhere
    on that edge. The saturated span has rank two and excludes the fake cut.
    """
    vertices = list(product((0, 1), repeat=3))
    initial_normal = (-1, -1, 0)
    extra_normal = (-1, 0, 0)
    dot = lambda a, v: sum(x * y for x, y in zip(a, v))
    assert all(dot(initial_normal, v) <= 0 for v in vertices)
    assert all(dot(extra_normal, v) <= 0 for v in vertices)
    face = [v for v in vertices if dot(initial_normal, v) == 0]
    cut = [v for v in face if dot(extra_normal, v) == 0]
    assert face == cut == [(0, 0, 0), (0, 0, 1)]
    # The nonzero two-by-two determinant proves the two normals independent.
    det = initial_normal[0] * extra_normal[1] - initial_normal[1] * extra_normal[0]
    assert det != 0
    # Both -e_x and -e_y are universally tight on this face.
    assert all(v[0] == v[1] == 0 for v in face)
    return {
        'cube_dimension': 3,
        'selected_supporting_row': list(initial_normal),
        'apparently_new_row': list(extra_normal),
        'unsaturated_normal_rank': 1,
        'saturated_normal_rank': 2,
        'independence_minor_determinant': det,
        'face_vertices': face,
        'cut_leaves_face_unchanged': face == cut,
    }


def run(max_dimension: int = 6) -> dict:
    if not 1 <= max_dimension <= 8:
        raise ValueError('max dimension must be between 1 and 8 for exhaustive checks')
    records = [cube_primal_dual_certificate(d, k)
               for d in range(1, max_dimension + 1) for k in range(d)]
    # Formula-only illustrations, separate from the exhaustive finite checks.
    illustrations = [
        {'dimension': d, 'seed_dimension': k,
         'optimal_certificate_budget': (k + 1) * 2 ** (d - k) - 1,
         'actual_cube_diameter': d}
        for d, k in [(8, 0), (8, 2), (8, 7), (16, 0), (16, 2), (20, 2)]
    ]
    return {
        'arithmetic': 'exact integers and fractions; no floating-point optimization',
        'lean_verification': 'not performed by this script',
        'general_random_cover_cases_passed': check_general_cover_barrier(),
        'cube_primal_dual_certificates_passed': len(records),
        'cube_face_dual_constraints_checked': sum(r['all_proper_faces_checked'] for r in records),
        'exhaustive_cube_records': records,
        'saturation_counterexample': saturation_counterexample(),
        'formula_only_illustrations': illustrations,
        'scope': ('Lower bounds concern the weighted averaging certificate with the specified '
                  'child costs, not graph diameter. No conclusion about Polynomial Hirsch.'),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-dimension', type=int, default=6)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.max_dimension)
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding='utf-8')
    print(text)


if __name__ == '__main__':
    main()
