#!/usr/bin/env python3
"""Exact additional tests for the three-dimensional carrier/Euler refinement.

This is an ordinary mathematical refinement, not a Lean theorem. It reuses
all 40 instances, enumerates each encountered 3D new-cut-only relaxation in
its affine span, and checks the same explicit parent-edge routes.
"""
from __future__ import annotations
import argparse
import json
from itertools import combinations, combinations_with_replacement
from math import comb
from pathlib import Path

from test_cone_carrier_descent import CarrierCertificate, budget, instances
from test_face_preserving_checkpoints import dot, rank, solve


def refined_budget(m: int, k: int) -> int:
    base = budget(m, k)
    return base if k < 3 else base - comb(m, 3) + min(comb(m, 3), 2*m - 2)


def main() -> None:
    if not __debug__:
        raise RuntimeError('Run without -O: assertions verify certificates')
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = []
    for name, cone, cuts in instances():
        cert = CarrierCertificate(cone, cuts)
        for v in range(len(cert.P.v)):
            cert.route(v)
            assert len(cert.routes[v]) - 1 <= refined_budget(cert.m, cert.dim[v])
        counts = []
        for J, (k, face, interior, boundary, assignment) in cert.shells.items():
            if k != 3:
                continue
            old_basis = []
            for i in sorted(J):
                row = cone.rows[i]
                if rank([a for a, _ in old_basis] + [row[0]]) > len(old_basis):
                    old_basis.append(row)
            assert len(old_basis) == cone.d - 3
            vertices = set()
            for selected in combinations(cert.cuts, 3):
                x = solve(old_basis + list(selected))
                if x is not None and all(dot(a, x) <= b for a, b in cert.cuts):
                    assert all(dot(cone.rows[i][0], x) == cone.rows[i][1] for i in J)
                    vertices.add(x)
            assert all(cert.P.v[v] in vertices for v in interior)
            assert len(vertices) <= 2 * cert.m - 2
            assert len(interior) <= min(comb(cert.m, 3), 2 * cert.m - 2)
            counts.append({'interior_vertices': len(interior),
                           'relaxation_vertices': len(vertices),
                           'euler_upper_bound': 2 * cert.m - 2})
        pair_count = 0
        for u, v in combinations_with_replacement(range(len(cert.P.v)), 2):
            length = len(cert.routes[u]) + len(cert.routes[v]) - 2
            assert length <= refined_budget(cert.m, cert.dim[u]) + refined_budget(cert.m, cert.dim[v])
            pair_count += 1
        if cert.r == 3:
            assert 2 * refined_budget(cert.m, 3) <= 5 * cert.m - 2
        rows.append({'name': name, 'pairs': pair_count, 'new_rank': cert.r,
                     'new_cuts': cert.m, 'three_dimensional_relaxations': counts,
                     'original_diameter_budget': 2 * budget(cert.m, cert.r),
                     'refined_diameter_budget': 2 * refined_budget(cert.m, cert.r)})
    result = {'instances': len(rows), 'pairs': sum(x['pairs'] for x in rows),
              'three_dimensional_relaxations': sum(len(x['three_dimensional_relaxations']) for x in rows),
              'all_explicit_routes_pass': True, 'lean_verified': False,
              'general_theorem_proved_by_tests': False, 'results': rows}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print({k:v for k,v in result.items() if k != 'results'})

if __name__ == '__main__':
    main()
