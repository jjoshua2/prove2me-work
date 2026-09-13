#!/usr/bin/env python3
"""Generate and audit complete positive-circuit catalogues using rational identities.

The generator may use elimination; the verifier never does. Every support of
size <= number_of_rows+1 has either a left inverse of [A_S; ones] or a nonzero
zero-mass null witness. The Lean packet proves that precisely filtering the
first kind returns ALL normalized positive circuits, including real vectors.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from math import comb
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int, str, Q), 'exact integers/rational strings required; floats and bools are refused')
    return Q(x)


def matrix(A: list[list[Any]], n: int) -> list[list[Q]]:
    require(type(n) is int and n >= 0, 'invalid coordinate dimension')
    require(type(A) is list and all(type(row) is list and len(row) == n for row in A), 'invalid rectangular matrix')
    return [[rat(x) for x in row] for row in A]


def support_list(n: int, k: int, cap: int) -> list[tuple[int, ...]]:
    count = sum(comb(n, j) for j in range(min(n, k + 1) + 1))
    require(type(cap) is int and cap >= count, 'support cap exceeded; no partial catalogue is certified')
    return [s for j in range(min(n, k + 1) + 1) for s in combinations(range(n), j)]


def dot(a, b):
    return sum((x * y for x, y in zip(a, b)), Q(0))


def rref(rows: list[list[Q]], width: int):
    """UNTRUSTED search helper: all consequences are checked by rational identities."""
    M = [row[:] for row in rows]
    pivots = []
    at = 0
    for j in range(width):
        i = next((i for i in range(at, len(M)) if M[i][j]), None)
        if i is None:
            continue
        M[at], M[i] = M[i], M[at]
        scale = M[at][j]
        M[at] = [x / scale for x in M[at]]
        for i in range(len(M)):
            if i != at and M[i][j]:
                scale = M[i][j]
                M[i] = [x - scale * y for x, y in zip(M[i], M[at])]
        pivots.append(j)
        at += 1
        if at == len(M):
            break
    return M, pivots


def inverse(M: list[list[Q]]):
    n = len(M)
    aug = [row + [Q(i == j) for j in range(n)] for i, row in enumerate(M)]
    R, pivots = rref(aug, n)
    require(pivots == list(range(n)), 'search selected a singular square submatrix')
    return [row[n:] for row in R]


def generate(A, n: int, cap: int = 100000) -> dict[str, Any]:
    A = matrix(A, n)
    k = len(A)
    cells = []
    for s in support_list(n, k, cap):
        m = len(s)
        D = [[row[j] for j in s] for row in A] + [[Q(1)] * m]
        R, pivots = rref(D, m)
        if len(pivots) < m:
            free = next(j for j in range(m) if j not in pivots)
            z = [Q(0)] * m
            z[free] = Q(1)
            for i, p in enumerate(pivots):
                z[p] = -R[i][free]
            cells.append({'support': list(s), 'kind': 'dependent', 'null': [str(x) for x in z]})
        else:
            # Choose independent rows of D, and embed their inverse in a left inverse.
            _, chosen = rref([list(row) for row in zip(*D)], k + 1)
            require(len(chosen) == m, 'search failed to find enough independent rows')
            B = inverse([D[i] for i in chosen])
            L = [[Q(0)] * (k + 1) for _ in s]
            for i in range(m):
                for j, r in enumerate(chosen):
                    L[i][r] = B[i][j]
            cells.append({'support': list(s), 'kind': 'left_inverse',
                          'left_inverse': [[str(x) for x in row] for row in L]})
    cert = {'format': 'normalized-circuit-audit-v1', 'n': n, 'k': k,
            'matrix': [[str(x) for x in row] for row in A], 'cells': cells}
    # Output is derived from the VERIFIED identities, never from the search's rank.
    result = audit(A, n, cert, cap=cap, require_catalogue=False)
    cert['catalogue'] = result['catalogue']
    audit(A, n, cert, cap=cap)
    return cert


def audit(A, n: int, cert: dict[str, Any], cap: int = 100000,
          require_catalogue: bool = True) -> dict[str, Any]:
    """No rref, inverse, rank computation, LP, vertex oracle, or tolerance here."""
    A = matrix(A, n)
    k = len(A)
    expected = support_list(n, k, cap)
    require(type(cert) is dict and cert.get('format') == 'normalized-circuit-audit-v1', 'unknown certificate format')
    require(type(cert.get('n')) is int and cert['n'] == n and type(cert.get('k')) is int and cert['k'] == k,
            'changed certificate dimensions')
    require(matrix(cert.get('matrix'), n) == A, 'certificate does not bind the original matrix')
    cells = cert.get('cells')
    require(type(cells) is list and len(cells) == len(expected), 'missing or extra support cells')
    rays = []
    dependent = left = inconsistent = nonpositive = identities = 0
    for s, cell in zip(expected, cells):
        require(type(cell) is dict and cell.get('support') == list(s)
                and all(type(i) is int for i in cell['support']), 'support coverage/order changed')
        m = len(s)
        if cell.get('kind') == 'dependent':
            require(set(cell) == {'support', 'kind', 'null'}, 'unexpected dependent-cell fields')
            z = [rat(x) for x in cell['null']]
            require(len(z) == m and any(z), 'zero or malformed dependency witness')
            require(sum(z) == 0, 'dependency has nonzero total mass')
            require(all(dot([row[j] for j in s], z) == 0 for row in A), 'dependency is not in original matrix kernel')
            dependent += 1
            identities += k + 1
        elif cell.get('kind') == 'left_inverse':
            require(set(cell) == {'support', 'kind', 'left_inverse'}, 'unexpected inverse-cell fields')
            L = matrix(cell['left_inverse'], k + 1)
            require(len(L) == m, 'wrong number of left-inverse rows')
            for i in range(m):
                for j in range(m):
                    require(dot(L[i][:-1], [row[s[j]] for row in A]) + L[i][-1] == Q(i == j),
                            'left-inverse identity failed')
                    identities += 1
            v = tuple(row[-1] for row in L)
            feasible = sum(v) == 1 and all(dot([row[j] for j in s], v) == 0 for row in A)
            if not feasible:
                inconsistent += 1
            elif not all(x > 0 for x in v):
                nonpositive += 1
            else:
                rays.append({'support': list(s), 'positive': [str(x) for x in v]})
            left += 1
        else:
            raise ValueError('unknown cell kind')
    if require_catalogue:
        require(cert.get('catalogue') == rays, 'emitted catalogue differs from exact audited filter')
    return {'status': 'PASS', 'support_cells': len(expected), 'dependent_cells': dependent,
            'left_inverse_cells': left, 'inconsistent_normalized_cells': inconsistent,
            'nonpositive_normalized_cells': nonpositive, 'identity_checks': identities,
            'circuits': len(rays), 'catalogue': rays}


def jsonable(obj):
    if isinstance(obj, Q): return str(obj)
    if isinstance(obj, dict): return {k: jsonable(v) for k, v in obj.items()}
    if isinstance(obj, (list, tuple)): return [jsonable(v) for v in obj]
    return obj


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON containing A and n')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cap', type=int, default=100000)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text())
        cert = generate(data['A'], data['n'], args.cap)
        args.output.write_text(json.dumps(cert, indent=2) + '\n')
    except (ValueError, KeyError, TypeError, OSError, ZeroDivisionError) as exc:
        parser.exit(2, f'Certificate generation failed: {exc}\n')

if __name__ == '__main__':
    main()


def lean_smoke_certificate() -> str:
    """Export finite data; Lean's own decidable checker rechecks it independently.
    This exporter is untrusted. A malformed export fails the kernel examples.
    """
    cert = generate([[1, 1, -1, 0]], 4)
    n, k = 4, 1
    def qlit(x):
        x = Q(x)
        return f'({x.numerator} : ℚ)' if x.denominator == 1 else f'(({x.numerator} : ℚ) / {x.denominator})'
    def vec(xs): return '![' + ', '.join(qlit(x) for x in xs) + ']'
    def supp(s): return '({' + ', '.join(map(str, s)) + '} : Finset (Fin 4))'
    out = ['namespace Hirsch.CheckedCatalogue.KernelSmoke',
           'def A : Fin 1 → Fin 4 → ℚ := fun _ => ![1, 1, -1, 0]',
           'def tag (s : Finset (Fin 4)) : Bool :=']
    deps = [cell for cell in cert['cells'] if cell['kind'] == 'dependent']
    out += ['  ' + ''.join(f'if s = {supp(cell["support"])} then true else ' for cell in deps) + 'false']
    out += ['def z (s : Finset (Fin 4)) (i : Fin 4) : ℚ :=']
    for cell in deps:
        v = [Q(0)] * n
        for j,x in zip(cell['support'],cell['null']): v[j]=Q(x)
        out += [f'  if s = {supp(cell["support"])} then {vec(v)} i else']
    out += ['  0', 'def L (s : Finset (Fin 4)) (i : Fin 4) (r : Option (Fin 1)) : ℚ :=']
    for cell in cert['cells']:
        if cell['kind'] != 'left_inverse' or not cell['support']: continue
        columns=[[Q(0)]*n for _ in range(k+1)]
        for j,row in zip(cell['support'],cell['left_inverse']):
            for a,x in enumerate(row):columns[a][j]=Q(x)
        out += [f'  if s = {supp(cell["support"])} then',
                f'    match r with | none => {vec(columns[-1])} i | some _ => {vec(columns[0])} i',
                '  else']
    out += ['  0', '',
            'example : check 4 1 A tag L z = true := by decide',
            'example : (catalogue 4 1 A tag L).card = 3 := by decide',
            'example : check 4 1 A (fun _ => false) (fun _ _ _ => 0) (fun _ _ => 0) = false := by decide',
            'end Hirsch.CheckedCatalogue.KernelSmoke', '']
    return '\n'.join(out)
