#!/usr/bin/env python3
"""Exact discovery and verification of recursive projective product certificates.

Inputs are rational A,b plus an interior_point and strictly positive
positive_balance annihilating A. No proposed chart or factor partition is needed.
Discovery searches homogeneous rank-one separators. A search cap is NEVER a
nonexistence certificate. The independent verifier checks only exact identities,
positive margins, row/coordinate partitions, and recursive leaf row counts.

The route implication uses the repository's projective/affine transport and
small-excess theorem; this program is not a Lean kernel or platform verdict.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import combinations
import json
from pathlib import Path
from typing import Any, Iterator, Sequence

Vector = list[Q]
Matrix = list[Vector]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rational(x: Any) -> Q:
    require(not isinstance(x, bool) and isinstance(x, (int, str, Q)),
            'Use integers or rational strings, not floats/bools')
    return Q(x)


def dot(a: Sequence[Q], b: Sequence[Q]) -> Q:
    require(len(a) == len(b), 'Vector dimension mismatch')
    return sum((x*y for x,y in zip(a,b)), Q(0))


def rref(rows: Sequence[Sequence[Q]], width: int | None = None) -> tuple[Matrix,list[int]]:
    a = [[Q(x) for x in row] for row in rows]
    n = len(a[0]) if a else (width or 0)
    require(all(len(row) == n for row in a), 'Ragged matrix')
    pivots: list[int] = []
    for j in range(n):
        p = next((i for i in range(len(pivots),len(a)) if a[i][j]), None)
        if p is None:
            continue
        k = len(pivots)
        a[k],a[p] = a[p],a[k]
        a[k] = [x/a[k][j] for x in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                t = a[i][j]
                a[i] = [x-t*y for x,y in zip(a[i],a[k])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return a[:len(pivots)],pivots


def rank(rows: Sequence[Sequence[Q]]) -> int:
    return len(rref(rows)[0])


def nullspace(rows: Matrix, width: int) -> Matrix:
    rr,piv = rref(rows,width)
    result=[]
    for j in range(width):
        if j not in piv:
            v=[Q(0)]*width; v[j]=Q(1)
            for i,p in enumerate(piv):
                v[p]=-rr[i][j]
            result.append(v)
    return result


def identity(n: int) -> Matrix:
    return [[Q(i==j) for j in range(n)] for i in range(n)]


def transpose(a: Matrix) -> Matrix:
    return [list(col) for col in zip(*a)]


def inverse(a: Matrix) -> Matrix:
    n=len(a)
    require(n>0 and all(len(row)==n for row in a), 'Need positive square matrix')
    aug=[row+unit for row,unit in zip(a,identity(n))]
    rr,piv=rref(aug)
    require(piv[:n]==list(range(n)) and len(piv)==n, 'Singular matrix')
    require([row[:n] for row in rr]==identity(n), 'Singular matrix')
    return [row[n:] for row in rr]


def matmul(a: Matrix, b: Matrix) -> Matrix:
    require(bool(b), 'Empty right matrix')
    return [[dot(row,col) for col in transpose(b)] for row in a]


def combination(weights: Sequence[Q], rows: Matrix) -> Vector:
    require(len(weights)==len(rows) and bool(rows), 'Combination dimensions')
    return [dot(weights,col) for col in transpose(rows)]


def decode(data: dict[str,Any]) -> tuple[Matrix,Vector,Vector,Vector]:
    require(isinstance(data,dict), 'Input must be an object')
    a=[[rational(x) for x in row] for row in data['A']]
    b=[rational(x) for x in data['b']]
    center=[rational(x) for x in data['interior_point']]
    w=[rational(x) for x in data['positive_balance']]
    d=len(center); n=len(a)
    require(d>0 and n>0 and len(b)==n and all(len(row)==d for row in a), 'Input dimensions')
    require(all(any(row) for row in a), 'Remove tautological zero rows in a separately certified step')
    require(len(w)==n and all(x>0 for x in w), 'Balance must be strictly positive')
    require(combination(w,a)==[Q(0)]*d, 'Balance fails to annihilate target normals')
    require(rank(a)==d, 'Target normals do not have full rank')
    require(all(dot(row,center)<rhs for row,rhs in zip(a,b)), 'Point must be strictly interior')
    return a,b,center,w


def centered(data: dict[str,Any]) -> tuple[Matrix,Vector,Vector,Vector]:
    a,b,z,w=decode(data)
    return a,[rhs-dot(row,z) for row,rhs in zip(a,b)],z,w


def homogeneous_candidates(a: Matrix,b: Vector,max_side: int | None=None
                           ) -> Iterator[dict[str,Any]]:
    """Every nontrivial projective product has a rank-one bipartition here.

    Exhaustive iff max_side >= floor(n/2). Up to complement, each partition
    is visited once. Distinct partitions may determine the same chart.
    """
    n=len(a); d=len(a[0]); rows=[row+[-rhs] for row,rhs in zip(a,b)]
    require(rank(rows)==d+1, 'Homogeneous rows must span d+1 dimensions')
    limit=n//2 if max_side is None else min(n//2,max_side)
    seen=set()
    for size in range(2,limit+1):
        for ids in combinations(range(n),size):
            if size*2==n and 0 not in ids:
                continue
            selected=set(ids); other=[i for i in range(n) if i not in selected]
            u,_=rref([rows[i] for i in ids]); v,_=rref([rows[i] for i in other])
            if len(u)<2 or len(v)<2 or len(u)+len(v)!=d+2:
                continue
            dependence=nullspace(transpose(u+v),len(u)+len(v))
            require(len(dependence)==1, 'Separator intersection must be a line')
            horizon=combination(dependence[0][:len(u)],u)
            require(any(horizon), 'Zero separator')
            # An admissible infinity hyperplane cannot pass through the center.
            if not horizon[-1]:
                continue
            c=[-x/horizon[-1] for x in horizon[:-1]]
            key=tuple(c)
            if key in seen:
                continue
            seen.add(key)
            yield {'chart_normal':c,'separator_rows':list(ids),
                   'homogeneous_ranks':[len(u),len(v),d+1]}


def multiplier_bases(a: Matrix) -> Iterator[tuple[tuple[int,...],Matrix]]:
    d=len(a[0])
    for ids in combinations(range(len(a)),d):
        sub=[a[i] for i in ids]
        if rank(sub)==d:
            yield ids,inverse(transpose(sub))


def dual_weights(a: Matrix,b: Vector,c: Vector) -> Vector | None:
    """Exact finite dual search for lambda*A=c, lambda*b<1, lambda>=0.

    Bounded full-dimensional input has an optimum at a dual basic solution.
    This finite routine is exponential and does not use floating point or an LP
    success status as proof. None means no such strict certificate exists.
    """
    if not any(c):
        return [Q(0)]*len(a)
    # Sparse witnesses are common (especially for interval towers). This fast
    # path changes neither the exact checks nor the complete fallback.
    for size in range(1,min(2,len(a[0]))+1):
        for ids in combinations(range(len(a)),size):
            equations=[list(col)+[wanted] for col,wanted in zip(transpose([a[i] for i in ids]),c)]
            rr,piv=rref(equations)
            if piv!=list(range(size)):
                continue
            coeff=[row[-1] for row in rr]
            if min(coeff)>=0 and combination(coeff,[a[i] for i in ids])==c and dot(coeff,[b[i] for i in ids])<1:
                lam=[Q(0)]*len(a)
                for i,x in zip(ids,coeff): lam[i]=x
                return lam
    for ids,inv in multiplier_bases(a):
        coeff=[dot(row,c) for row in inv]
        if min(coeff)>=0 and dot(coeff,[b[i] for i in ids])<1:
            lam=[Q(0)]*len(a)
            for i,x in zip(ids,coeff): lam[i]=x
            return lam
    return None


def transferred_witnesses(a: Matrix,b: Vector,w: Vector,c: Vector,lam: Vector
                         ) -> tuple[Vector,Vector]:
    """Derive both source witnesses from target balance and one dual witness."""
    n=len(a); W=dot(w,b); t=1-dot(lam,b)
    require(W>0 and t>0, 'Strict positive margins required')
    beta=[t*w[i]+W*lam[i] for i in range(n)]
    # alpha is positive and leaves every coefficient w_i-alpha*lambda_i positive.
    ratios=[w[i]/lam[i] for i in range(n) if lam[i]>0]
    alpha=min(ratios)/2 if ratios else Q(1)
    mu=[(w[i]-alpha*lam[i])/(W+alpha*t) for i in range(n)]
    return beta,mu


def row_blocks(a: Matrix) -> dict[str,Any]:
    """Find the finest linear row-matroid components by fundamental supports."""
    d=len(a[0]); basis=[]
    for row in a:
        if rank(basis+[row])>len(basis): basis.append(row)
        if len(basis)==d: break
    require(len(basis)==d, 'Unsheared rows lost full rank')
    inv=inverse(basis); transformed=matmul(a,inv)
    parent=list(range(d))
    def find(j: int)->int:
        while parent[j]!=j:
            parent[j]=parent[parent[j]]; j=parent[j]
        return j
    for row in transformed:
        support=[j for j,x in enumerate(row) if x]
        require(bool(support), 'Unshearing produced a zero row')
        for j in support[1:]: parent[find(j)]=find(support[0])
    parts: dict[int,list[int]]={}
    for j in range(d): parts.setdefault(find(j),[]).append(j)
    blocks=sorted(parts.values(),key=lambda xs:xs[0])
    groups=[[i for i,row in enumerate(transformed) if any(row[j] for j in part)] for part in blocks]
    return {'basis_matrix':basis,'inverse_basis':inv,'transformed_rows':transformed,
            'coordinate_blocks':blocks,'row_blocks':groups}


def split(data: dict[str,Any],candidate: dict[str,Any]) -> dict[str,Any] | None:
    a,b,z,w=centered(data); n=len(a); d=len(z); c=candidate['chart_normal']
    lam=dual_weights(a,b,c)
    if lam is None: return None
    beta,mu=transferred_witnesses(a,b,w,c,lam)
    source=[[x-rhs*t for x,t in zip(row,c)] for row,rhs in zip(a,b)]
    # A positive chart can make a redundant inequality tautological. This
    # version never drops rows: skip that candidate rather than certify a
    # different problem. Completeness of geometric nonexistence claims requires
    # an irredundant facet input.
    if any(not any(row) for row in source): return None
    cert=row_blocks(source)
    if len(cert['coordinate_blocks'])<2: return None
    children=[]
    for coords,ids in zip(cert['coordinate_blocks'],cert['row_blocks']):
        children.append({'A':[[cert['transformed_rows'][i][j] for j in coords] for i in ids],
                         'b':[b[i] for i in ids], 'interior_point':[Q(0)]*len(coords),
                         'positive_balance':[beta[i] for i in ids]})
    return {'kind':'split','center':z,'chart_normal':c,'target_weights':lam,
            'source_weights':mu,'source_balance':beta,'blocks':cert,
            'separator_rows':candidate.get('separator_rows'),
            'child_inputs':children}


def all_splits(data: dict[str,Any],max_side: int | None=3) -> Iterator[dict[str,Any]]:
    a,b,_,_=centered(data)
    # A zero chart cheaply recovers ordinary affine products of any block size.
    zero=[Q(0)]*len(a[0])
    plain=split(data,{'chart_normal':zero})
    if plain is not None: yield plain
    for candidate in homogeneous_candidates(a,b,max_side):
        if candidate['chart_normal']==zero: continue
        result=split(data,candidate)
        if result is not None: yield result


def discover(data: dict[str,Any],max_side: int | None=3,leaf_excess: int=3,
             *,depth: int=0) -> dict[str,Any]:
    a,b,_,_=decode(data); n=len(a); d=len(a[0])
    require(type(leaf_excess) is int and 1<=leaf_excess<=3, 'Leaf excess must be 1,2 or 3')
    if n-d<=leaf_excess:
        return {'kind':'leaf','dimension':d,'rows':n,'excess':n-d}
    best=None; best_unresolved=n-d; tried=0
    for node in all_splits(data,max_side):
        tried+=1
        children=[discover(child,max_side,leaf_excess,depth=depth+1) for child in node.pop('child_inputs')]
        node['children']=children
        unresolved=sum(tree_stats(ch)['unresolved_excess'] for ch in children)
        if unresolved<best_unresolved:
            best=node; best_unresolved=unresolved
        if unresolved==0: return node
    if best is not None: return best
    return {'kind':'unresolved','dimension':d,'rows':n,'excess':n-d,
            'admissible_splits_tried':tried,
            'all_bipartitions_searched':max_side is None or max_side>=n//2,
            'reason':'No complete small-leaf tree found in the searched candidates; not a diameter lower bound.'}


def tree_stats(tree: dict[str,Any]) -> dict[str,int]:
    if tree['kind'] in ('leaf','unresolved'):
        return {'leaves':1,'nodes':0,'depth':0,'unresolved_excess':
                tree['excess'] if tree['kind']=='unresolved' else 0}
    children=[tree_stats(ch) for ch in tree['children']]
    return {'leaves':sum(ch['leaves'] for ch in children),'nodes':1+sum(ch['nodes'] for ch in children),
            'depth':1+max(ch['depth'] for ch in children),
            'unresolved_excess':sum(ch['unresolved_excess'] for ch in children)}


def verify(data: dict[str,Any],tree: dict[str,Any],*,depth: int=0,max_depth: int | None=None
           ) -> dict[str,Any]:
    """Verify without calling discovery, dual search, or component detection."""
    require(isinstance(tree,dict), 'Certificate node must be an object')
    a,b,z,w=centered(data); n=len(a); d=len(z)
    if max_depth is None: max_depth=d
    require(depth<=max_depth, 'Certificate too deep')
    kind=tree.get('kind')
    if kind in ('leaf','unresolved'):
        require(tree.get('dimension')==d and tree.get('rows')==n and tree.get('excess')==n-d,
                'Leaf metadata mismatch')
        if kind=='leaf': require(0<=n-d<=3,'Leaf not covered by small-excess theorem')
        return {'ordinary_edge_bound':n-d if kind=='leaf' else None,
                'dimension':d,'rows':n,'excess':n-d,'leaves':1,'nodes':0,'depth':0}
    require(kind=='split','Unknown certificate node')
    center=[rational(x) for x in tree['center']]
    require(center==z,'Translation differs from supplied interior point')
    c=[rational(x) for x in tree['chart_normal']]
    lam=[rational(x) for x in tree['target_weights']]
    mu=[rational(x) for x in tree['source_weights']]
    beta=[rational(x) for x in tree['source_balance']]
    require(len(c)==d and len(lam)==n and len(mu)==n and len(beta)==n,'Witness dimensions')
    source=[[x-rhs*t for x,t in zip(row,c)] for row,rhs in zip(a,b)]
    require(min(lam)>=0 and combination(lam,a)==c and dot(lam,b)<1,'Target denominator invalid')
    require(min(mu)>=0 and combination(mu,source)==[-x for x in c] and dot(mu,b)<1,
            'Source denominator invalid')
    require(min(beta)>0 and combination(beta,source)==[Q(0)]*d,'Source balance invalid')
    cert=tree['blocks']
    B=[[rational(x) for x in row] for row in cert['basis_matrix']]
    inv=[[rational(x) for x in row] for row in cert['inverse_basis']]
    require(len(B)==d and len(inv)==d and all(len(row)==d for row in B+inv),'Basis dimensions')
    require(matmul(B,inv)==identity(d) and matmul(inv,B)==identity(d),'Bad inverse')
    C=[[rational(x) for x in row] for row in cert['transformed_rows']]
    require(C==matmul(source,inv),'Transformed row identity invalid')
    parts=cert['coordinate_blocks']; groups=cert['row_blocks']; children=tree['children']
    require(2<=len(parts)==len(groups)==len(children),'A split needs at least two children')
    require(all(isinstance(part,list) and part and all(type(j) is int for j in part) for part in parts),
            'Coordinate groups must be nonempty integer lists')
    require(all(isinstance(ids,list) and ids and all(type(i) is int for i in ids) for ids in groups),
            'Row groups must be nonempty integer lists')
    require(sorted(j for part in parts for j in part)==list(range(d)),'Coordinates not partitioned')
    require(sorted(i for ids in groups for i in ids)==list(range(n)),'Rows not partitioned')
    results=[]
    for coords,ids,child in zip(parts,groups,children):
        require(0<len(coords)<d,'Dimension must strictly decrease')
        require(all(C[i][j]==0 for i in ids for j in range(d) if j not in coords),'Omitted cross coupling')
        child_data={'A':[[C[i][j] for j in coords] for i in ids], 'b':[b[i] for i in ids],
                    'interior_point':[Q(0)]*len(coords),'positive_balance':[beta[i] for i in ids]}
        results.append(verify(child_data,child,depth=depth+1,max_depth=max_depth))
    require(sum(res['excess'] for res in results)==n-d,'Excess did not telescope')
    bound=None if any(res['ordinary_edge_bound'] is None for res in results) else sum(res['ordinary_edge_bound'] for res in results)
    return {'ordinary_edge_bound':bound,'dimension':d,'rows':n,'excess':n-d,
            'leaves':sum(res['leaves'] for res in results), 'nodes':1+sum(res['nodes'] for res in results),
            'depth':1+max(res['depth'] for res in results)}


def jsonable(value: Any) -> Any:
    if isinstance(value,Q): return str(value)
    if isinstance(value,dict): return {str(k):jsonable(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)): return [jsonable(x) for x in value]
    return value


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--max-side',type=int,default=3,help='Largest side searched; default 3, 0 means exhaustive')
    parser.add_argument('--leaf-excess',type=int,default=3,choices=(1,2,3))
    parser.add_argument('--verify',type=Path,help='Verify an existing tree instead of discovering')
    args=parser.parse_args()
    try:
        require(args.max_side>=0,'max-side cannot be negative')
        data=json.loads(args.input.read_text())
        tree=(json.loads(args.verify.read_text())['certificate'] if args.verify else
              discover(data,None if args.max_side==0 else args.max_side,args.leaf_excess))
        result={'certificate':tree,'verified':verify(data,tree),
                'scope':'Exact rational checks conditional on geometric transport and small-excess theorem, not a Lean verdict.'}
        text=json.dumps(jsonable(result),indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:
        parser.exit(2,f'Certificate rejected: {exc}\n')

if __name__=='__main__': main()
