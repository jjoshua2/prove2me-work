#!/usr/bin/env python3
"""Exact rational row-block certificates for actual ordinary-edge cost.

Input JSON: A (rows), b, feasible_point, positive_balance (on kept rows),
optionally keep and redundancy (one nonnegative multiplier vector per dropped
row, keyed by its original index). No floats are accepted. Output is a checked
linear change of coordinates and factor budgets, conditional only on the
project's existing excess-at-most-three H-polyhedron theorem. Large connected
blocks are reported as unresolved by this sufficient criterion, never as easy.

The checker performs exact rational arithmetic; it does not emit Lean proof
terms for individual numerical instances. See PolynomialRowBlockRouting.lean
for the universal row-block-to-graph-bound implication.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
from typing import Any, Sequence

Matrix = list[list[Q]]


def rational(x: Any) -> Q:
    if isinstance(x, bool) or not isinstance(x, (int, str, Q)):
        raise ValueError('Use integers or rational strings, not floats/bools')
    return Q(x)


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def dot(x: Sequence[Q], y: Sequence[Q]) -> Q:
    require(len(x) == len(y), 'vector length mismatch')
    return sum((a*b for a, b in zip(x, y)), Q(0))


def rank(rows: Sequence[Sequence[Q]]) -> int:
    if not rows:
        return 0
    a = [list(r) for r in rows]
    n = len(a[0]); k = 0
    require(all(len(r) == n for r in a), 'ragged matrix')
    for j in range(n):
        pivot = next((i for i in range(k, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[k], a[pivot] = a[pivot], a[k]
        v = a[k][j]; a[k] = [x/v for x in a[k]]
        for i in range(k+1, len(a)):
            v = a[i][j]
            if v:
                a[i] = [x-v*y for x,y in zip(a[i], a[k])]
        k += 1
        if k == len(a):
            break
    return k


def identity(n: int) -> Matrix:
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def inverse(a: Matrix) -> Matrix:
    n = len(a)
    require(n > 0 and all(len(r) == n for r in a), 'need positive square matrix')
    aug = [r[:] + s for r,s in zip(a, identity(n))]
    for j in range(n):
        p = next((i for i in range(j,n) if aug[i][j]), None)
        require(p is not None, 'singular matrix')
        aug[j], aug[p] = aug[p], aug[j]
        v = aug[j][j]; aug[j] = [x/v for x in aug[j]]
        for i in range(n):
            if i != j:
                v = aug[i][j]
                if v:
                    aug[i] = [x-v*y for x,y in zip(aug[i], aug[j])]
    return [r[n:] for r in aug]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    require(bool(b), 'empty right matrix')
    require(all(len(r) == len(b[0]) for r in b), 'ragged right matrix')
    cols = list(zip(*b))
    return [[dot(r,c) for c in cols] for r in a]


def normalize(data: dict[str,Any]) -> tuple[Matrix,list[Q],list[int],Matrix,list[Q]]:
    a = [[rational(x) for x in r] for r in data['A']]
    b = [rational(x) for x in data['b']]
    require(bool(a) and bool(a[0]), 'empty/zero-dimensional input is not supported by this CLI')
    d = len(a[0]); n = len(a)
    require(len(b) == n and all(len(r) == d for r in a), 'A/b shape mismatch')
    keep = data.get('keep', list(range(n)))
    require(all(type(i) is int and 0 <= i < n for i in keep), 'invalid kept index')
    require(len(set(keep)) == len(keep) and bool(keep), 'duplicate or empty kept rows')
    kept = [a[i] for i in keep]; rhs = [b[i] for i in keep]
    for i in range(n):
        if i in keep:
            continue
        raw = data.get('redundancy', {}).get(str(i))
        if raw is None and not any(a[i]) and b[i] >= 0:
            raw = [0]*len(keep)
        require(raw is not None, f'dropped row {i} lacks a redundancy certificate')
        lam = [rational(x) for x in raw]
        require(len(lam) == len(keep) and all(x >= 0 for x in lam), 'bad redundancy weights')
        require(all(sum((lam[j]*kept[j][c] for j in range(len(keep))), Q(0)) == a[i][c]
                    for c in range(d)), f'redundancy normal mismatch at row {i}')
        require(dot(lam,rhs) <= b[i], f'redundancy bound fails at row {i}')
    x = [rational(v) for v in data['feasible_point']]
    require(len(x) == d and all(dot(r,x) <= t for r,t in zip(a,b)), 'invalid feasibility witness')
    balance = [rational(v) for v in data['positive_balance']]
    require(len(balance) == len(keep) and all(v > 0 for v in balance), 'balance weights must be strictly positive')
    require(all(sum((balance[j]*kept[j][c] for j in range(len(keep))), Q(0)) == 0
                for c in range(d)), 'balance does not annihilate the normals')
    require(rank(kept) == d, 'normals do not span: boundedness is not certified')
    # Positive balance and full column rank exclude every nonzero recession ray.
    require(all(any(r) for r in kept), 'drop tautological zero rows before block detection')
    return a,b,keep,kept,rhs


def verify_certificate(data: dict[str,Any], cert: dict[str,Any]) -> dict[str,Any]:
    """Verify identities/partitions directly, independently of component discovery."""
    _,_,keep,a,_ = normalize(data)
    n,d = len(a),len(a[0])
    B = [[rational(x) for x in r] for r in cert['basis_matrix']]
    Bi = [[rational(x) for x in r] for r in cert['inverse_basis']]
    require(len(B) == d and len(Bi) == d and all(len(r) == d for r in B+Bi), 'basis shape')
    require(matmul(B,Bi) == identity(d) and matmul(Bi,B) == identity(d), 'incorrect inverse')
    C = [[rational(x) for x in r] for r in cert['transformed_rows']]
    require(C == matmul(a,Bi), 'transformed row identity fails')
    blocks = cert['coordinate_blocks']; groups = cert['row_blocks']
    require(len(blocks) == len(groups) and bool(blocks), 'block shape')
    require(all(block and all(type(j) is int for j in block) for block in blocks), 'empty/invalid coordinate block')
    require(sorted(j for block in blocks for j in block) == list(range(d)), 'coordinates not partitioned')
    require(all(all(type(j) is int for j in group) for group in groups), 'invalid row block')
    require(sorted(j for group in groups for j in group) == list(range(n)), 'rows not partitioned')
    details=[]
    for block,group in zip(blocks,groups):
        require(all(all(not C[r][j] for j in range(d) if j not in block) for r in group), 'cross-block coupling was omitted')
        local = [[C[r][j] for j in block] for r in group]
        require(rank(local) == len(block), 'factor rank mismatch')
        ex = len(group)-len(block)
        require(ex >= 0, 'negative factor excess')
        details.append({'dimension':len(block),'rows':len(group),'excess':ex})
    budget = sum(x['excess'] for x in details)
    require(budget == n-d, 'excess sum mismatch')
    return {'bounded_nonempty_certified':True,'retained_rows':n,'dimension':d,
            'retained_original_indices':keep,'total_excess':budget,'factors':details,
            'all_factor_excesses_at_most_three':all(x['excess'] <= 3 for x in details),
            'ordinary_edge_bound_using_existing_small_excess_theorem':
                budget if all(x['excess'] <= 3 for x in details) else None,
            'unresolved_factor_indices':[i for i,x in enumerate(details) if x['excess'] > 3]}


def certificate(data: dict[str,Any]) -> dict[str,Any]:
    _,_,_,a,_ = normalize(data)
    d = len(a[0]); basis=[]
    for row in a:
        if rank(basis+[row]) > len(basis):
            basis.append(row)
        if len(basis) == d:
            break
    Bi = inverse(basis); C = matmul(a,Bi)
    parent = list(range(d))
    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]; i = parent[i]
        return i
    for row in C:
        support = [j for j,x in enumerate(row) if x]
        for j in support[1:]:
            parent[find(j)] = find(support[0])
    components: dict[int,list[int]] = {}
    for j in range(d):
        components.setdefault(find(j),[]).append(j)
    blocks = sorted(components.values(),key=lambda s:s[0])
    groups = [[r for r,row in enumerate(C) if any(row[j] for j in block)] for block in blocks]
    cert={'basis_matrix':basis,'inverse_basis':Bi,'transformed_rows':C,
          'coordinate_blocks':blocks,'row_blocks':groups}
    return {'certificate':cert,'verified':verify_certificate(data,cert)}


def jsonable(obj: Any) -> Any:
    if isinstance(obj,Q): return str(obj)
    if isinstance(obj,dict): return {str(k):jsonable(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)): return [jsonable(v) for v in obj]
    return obj


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('--output',type=Path)
    args=p.parse_args()
    try:
        result=certificate(json.loads(args.input.read_text()))
    except (ValueError, KeyError, TypeError, ZeroDivisionError) as exc:
        p.exit(2,f'Certificate rejected: {exc}\n')
    text=json.dumps(jsonable(result),indent=2)+'\n'
    if args.output: args.output.write_text(text)
    else: print(text,end='')

if __name__ == '__main__': main()
