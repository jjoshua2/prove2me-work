#!/usr/bin/env python3
"""Exact near-uniform positive packing normalization at a supplied simple vertex.

Input: A,b; simple_rows (d independent rows tight at one vertex); eta in (0,1).
Optional bounding_weights are nonnegative multipliers on the remaining
normalized rows with a strictly positive combined normal. Otherwise a capped
exact dual-basis search finds such multipliers. Failure of a cap is unresolved.

All original rows are retained and matched. Verification never calls discovery,
an LP solver, or vertex enumeration. This certificate proves a geometric
normalization, NOT a short diameter for arbitrary packing polytopes.
"""
from __future__ import annotations
import argparse
from itertools import combinations
import json
from pathlib import Path
from typing import Any
from hirsch_exact_geometry import *


def setup(data: dict[str, Any], cert: dict[str, Any] | None = None) -> dict[str, Any]:
    require(isinstance(data, dict), 'Input must be an object')
    require('keep' not in data and 'redundancy' not in data, 'No row deletion is allowed')
    a, b = matrix(data['A']), vector(data['b'])
    d = len(a[0]) if a else 0
    require(d > 0 and len(a) == len(b) and all(len(row) == d for row in a), 'A/b shape')
    ids = data['simple_rows']
    require(isinstance(ids, list) and len(ids) == d and len(set(ids)) == d and
            all(type(i) is int and 0 <= i < len(a) for i in ids), 'Bad simple-row list')
    eta = rational(data.get('eta', '1/100'))
    require(0 < eta < 1, 'eta must lie strictly between zero and one')
    L = [a[i] for i in ids]
    if cert is None:
        Li = inverse(L)
    else:
        Li = matrix(cert['simple_basis_inverse'])
        require(len(Li) == d and all(len(row) == d for row in Li), 'Inverse shape')
        require(matmul(L, Li) == eye(d) and matmul(Li, L) == eye(d), 'False basis inverse')
    v = [dot(row, [b[i] for i in ids]) for row in Li]
    upper = [i for i in range(len(a)) if i not in ids]
    require(bool(upper), 'No bounding rows')
    beta = [b[i]-dot(a[i], v) for i in upper]
    require(all(t > 0 for t in beta), 'Anchor is infeasible or not simple in this row description')
    RR = matmul([a[i] for i in upper], Li)
    R = [[-value/t for value in row] for row, t in zip(RR, beta)]
    return {'A': a, 'b': b, 'd': d, 'simple_rows': ids, 'upper_rows': upper,
            'inverse': Li, 'origin': v, 'upper_slacks': beta, 'R': R, 'eta': eta}


def bounding_witness(R: Matrix, max_bases: int) -> tuple[Vector, dict[str, Any]]:
    m, d = len(R), len(R[0])
    # Fast candidates are checked, not assumed valid.
    for lam in [[Q(1)]*m] + [[Q(i == j) for i in range(m)] for j in range(m)]:
        if all(dot(lam, col) > 0 for col in zip(*R)):
            return lam, {'method': 'checked-positive-combination', 'bases_examined': 0}
    # R^T lambda - nu = 1, lambda,nu>=0. Any feasible system has a BFS.
    columns = R + [[-v for v in row] for row in eye(d)]
    checked = 0
    for ids in combinations(range(m+d), d):
        if checked >= max_bases:
            raise ValueError(f'Dual search capped at {max_bases} bases; no nonexistence claim')
        checked += 1
        basis = transpose([columns[i] for i in ids])
        if rank(basis) != d:
            continue
        z = solve(basis, [Q(1)]*d)
        if all(x >= 0 for x in z):
            lam = [Q(0)]*m
            for i, x in zip(ids, z):
                if i < m:
                    lam[i] = x
            return lam, {'method': 'exact-dual-basis', 'bases_examined': checked}
    raise ValueError('No bounding witness found in exhaustive dual-basis search')


def verify(data: dict[str, Any], cert: dict[str, Any]) -> dict[str, Any]:
    p = setup(data, cert); R = p['R']; d = p['d']; m = len(R)
    require(vector(cert['origin']) == p['origin'], 'Wrong vertex origin')
    require(cert['upper_rows'] == p['upper_rows'], 'Original upper rows omitted or reordered')
    require(vector(cert['upper_slacks']) == p['upper_slacks'], 'Wrong normalization scales')
    require(matrix(cert['normalized_upper_rows']) == R, 'Wrong normalized rows')
    lam = vector(cert['bounding_weights'])
    require(len(lam) == m and all(x >= 0 for x in lam), 'Nonnegative bounding weights required')
    mu = [dot(lam, col) for col in zip(*R)]; sigma = sum(lam, Q(0))
    require(all(x > 0 for x in mu) and sigma > 0, 'Combined bounding normal is not strictly positive')
    scale = rational(cert['scale'])
    require(scale > 0, 'Positive projective scale required')
    H = [[1+value/scale for value in row] for row in R]
    require(matrix(cert['packing_rows']) == H, 'Wrong packing-row identity')
    require(all(1-p['eta'] < v < 1+p['eta'] for row in H for v in row),
            'Requested near-uniform coefficient bounds fail')
    # Check a finite target inverse-denominator certificate on the UNSCALED
    # sheared system -z<=0, (R_i+scale*1)z<=1.
    all_rows = [[-x for x in row] for row in eye(d)] + [[v+scale for v in row] for row in R]
    all_rhs = [Q(0)]*d+[Q(1)]*m
    weights = vector(cert['target_denominator_weights'])
    require(len(weights) == d+m and all(v >= 0 for v in weights), 'Bad denominator weights')
    require(all(dot(weights, col) == scale for col in zip(*all_rows)), 'Denominator normal mismatch')
    margin = 1-dot(weights, all_rhs)
    require(margin > 0, 'Inverse denominator not certified strictly positive')
    exact_margin = min(mu)/(scale*sigma+min(mu))
    require(rational(cert['uniform_inverse_margin']) == exact_margin, 'Wrong uniform inverse margin')
    # y=scale*z maps the positive system into [0,1)^d; no cube upper facet is active.
    return {'dimension': d, 'original_rows': d+m, 'packing_cut_rows': m,
            'coordinate_lower_rows': d, 'all_rows_retained': True,
            'same_dimension_and_face_lattice_by_positive_chart': True,
            'coefficient_interval': [1-p['eta'], 1+p['eta']],
            'exact_cut_rank': rank(H), 'inverse_denominator_margin': exact_margin,
            'multiplier_inverse_margin': margin,
            'redundant_cube_upper_rows': d,
            'scope': 'Exact normalization; no diameter bound or Lean/platform verdict.'}


def certificate(data: dict[str, Any], *, max_bases: int = 200000) -> dict[str, Any]:
    p = setup(data); R = p['R']; d = p['d']
    if 'bounding_weights' in data:
        lam = vector(data['bounding_weights']); info = {'method': 'supplied-and-checked'}
    else:
        lam, info = bounding_witness(R, max_bases)
    require(len(lam) == len(R) and all(t >= 0 for t in lam), 'Bad bounding weight shape/sign')
    mu = [dot(lam, col) for col in zip(*R)]; sigma = sum(lam, Q(0))
    require(all(t > 0 for t in mu) and sigma > 0, 'Invalid boundedness certificate')
    scale = 1+max(abs(value) for row in R for value in row)/p['eta']
    t = 1+max(scale/value for value in mu)
    den = 1+t*sigma
    weights = [(t*value-scale)/den for value in mu]+[t*value/den for value in lam]
    cert = {'simple_basis_inverse': p['inverse'], 'origin': p['origin'],
            'upper_rows': p['upper_rows'], 'upper_slacks': p['upper_slacks'],
            'normalized_upper_rows': R, 'bounding_weights': lam, 'scale': scale,
            'packing_rows': [[1+v/scale for v in row] for row in R],
            'target_denominator_weights': weights,
            'uniform_inverse_margin': min(mu)/(scale*sigma+min(mu))}
    return {'certificate': cert, 'verified': verify(data, cert), 'search': info}


def forward(data: dict[str, Any], cert: dict[str, Any], point: Vector) -> Vector:
    verify(data, cert); p = setup(data, cert)
    require(len(point) == p['d'], 'Point dimension mismatch')
    active_set(p['A'], p['b'], point)
    x = [p['b'][i]-dot(p['A'][i], point) for i in p['simple_rows']]
    scale = rational(cert['scale']); den = 1+scale*sum(x, Q(0))
    return [scale*value/den for value in x]


def backward(data: dict[str, Any], cert: dict[str, Any], y: Vector) -> Vector:
    verify(data, cert); p = setup(data, cert)
    require(len(y) == p['d'] and all(v >= 0 for v in y), 'Bad packing point')
    H = matrix(cert['packing_rows'])
    require(all(dot(row, y) <= 1 for row in H), 'Infeasible packing point')
    delta = 1-sum(y, Q(0)); require(delta > 0, 'Inverse crosses infinity')
    x = [v/(rational(cert['scale'])*delta) for v in y]
    return [o-dot(row, x) for o, row in zip(p['origin'], p['inverse'])]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path); parser.add_argument('--output', type=Path)
    parser.add_argument('--max-dual-bases', type=int, default=200000)
    args = parser.parse_args()
    try:
        result = certificate(json.loads(args.input.read_text()), max_bases=args.max_dual_bases)
        text = json.dumps(jsonable(result), indent=2, sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text, end='')
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        parser.exit(2, f'Not certified: {exc}\n')


if __name__ == '__main__': main()
