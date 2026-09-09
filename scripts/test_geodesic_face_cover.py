#!/usr/bin/env python3
"""Exact d5 hull/graph regression for the geodesic face-cover argument.

Coordinates and expected hull facets are from
research/SelectableTwoFaceBridgeCounterexampleD5.md, commit
4b09066a5e7a68e664790d56f4e11d24cf9475ee in jjoshua2/prove2me-work.
All certification here uses integer arithmetic and finite graph traversal.
This is a computational regression, not a Lean proof of the geometric hull.
"""
from __future__ import annotations
from collections import deque
from itertools import combinations
import json

POINTS = [
    (-7906,-3779,3765,2536,-1617),(-2479,-1913,3968,8624,277),
    (-8136,213,4395,1773,-3361),(1815,-3255,7206,5567,1784),
    (2471,-9137,-2139,-1790,1623),(-183,-2801,99,9569,738),
    (-1635,4562,-7049,2145,-4714),(-6786,4628,-3912,3784,-1704),
    (1614,2189,-3607,-8899,-636),(-4161,-60,1196,-7692,4700),
]
EXPECTED = '''01235 01239 01257 01279 01345 01349 01459 01579
02345 02349 02456 02468 02489 02567 02678 02789
04567 04579 04678 04789 12356 12367 12379 12567
13459 13567 13579 23456 23468 23489 23678 23789
34568 34589 35678 35789 45679 45689 46789 56789'''.split()

def determinant(rows: list[list[int]]) -> int:
    """Fraction-free Bareiss elimination, checking every exact division."""
    a = [list(r) for r in rows]
    n = len(a)
    assert all(len(r) == n for r in a)
    if n == 0:
        return 1
    prev = sign = 1
    for k in range(n-1):
        pivot = next((i for i in range(k,n) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k],a[pivot] = a[pivot],a[k]
            sign *= -1
        p = a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                v = a[i][j]*p-a[i][k]*a[k][j]
                assert v % prev == 0
                a[i][j] = v//prev
        for i in range(k+1,n):
            a[i][k] = 0
        prev = p
    return sign*a[-1][-1]

def hull_facets() -> list[frozenset[int]]:
    facets = []
    for inds in combinations(range(10),5):
        p = POINTS[inds[0]]
        base = [[POINTS[i][j]-p[j] for j in range(5)] for i in inds[1:]]
        signs=[]
        for k in set(range(10))-set(inds):
            v=determinant(base+[[POINTS[k][j]-p[j] for j in range(5)]])
            assert v != 0, 'This regression expects general position'
            signs.append(v>0)
        if all(signs) or not any(signs):
            facets.append(frozenset(inds))
    assert {''.join(map(str,sorted(f))) for f in facets} == set(EXPECTED)
    return facets

def distances(adj: list[set[int]], source: int, allowed: set[int]) -> dict[int,int]:
    ds={source:0}; todo=deque([source])
    while todo:
        x=todo.popleft()
        for y in adj[x]&allowed:
            if y not in ds:
                ds[y]=ds[x]+1; todo.append(y)
    assert set(ds)==allowed, 'Disconnected induced face graph'
    return ds

def analyze() -> dict:
    facets=hull_facets(); N=len(facets); allverts=set(range(N))
    adj=[{j for j in range(N) if len(facets[i]&facets[j])==4} for i in range(N)]
    assert all(len(x)==5 for x in adj)
    ds=[distances(adj,i,allverts) for i in range(N)]
    X=facets.index(frozenset([0,1,2,3,5])); Y=facets.index(frozenset([4,6,7,8,9]))
    dual_degree=[len(set().union(*(f for f in facets if i in f)))-1 for i in range(10)]
    goodX=[i for i in facets[X] if dual_degree[i]<=8]
    goodY=[i for i in facets[Y] if dual_degree[i]<=8]
    assert goodX==[1] and goodY==[8]
    assert max(len(f&facets[Y]) for f in facets if 1 in f)==2
    assert max(len(f&facets[X]) for f in facets if 8 in f)==2
    assert ds[X][Y]==5
    faceverts=[{j for j,f in enumerate(facets) if i in f} for i in range(10)]
    budgets=[max(max(distances(adj,j,S).values()) for j in S) for S in faceverts]
    cover_budget=sum(b+1 for b in budgets)
    diameter=max(max(x.values()) for x in ds)
    assert 5*(diameter+1)<=cover_budget
    disjoint_classes=[{j for j in range(N) if not (facets[s]&facets[j])} for s in range(N)]
    K=max(map(len,disjoint_classes)); B=max(budgets)
    assert K==1 and B+K==diameter==5
    # Exact dual certificate for all fractional covers by proper faces.
    dual_vertices={1,3,4,11,18,23,24,31,34,37}
    assert len(dual_vertices)==10
    proper_face_keys={frozenset(k) for f in facets for r in range(1,6)
                      for k in combinations(sorted(f),r)}
    for key in proper_face_keys:
        S={j for j,f in enumerate(facets) if key<=f}
        b=max(max(distances(adj,j,S).values()) for j in S)
        assert len(S&dual_vertices)<=b+1
    assert len(proper_face_keys)==290
    assert cover_budget==5*len(dual_vertices)
    paths_checked=0; visits_checked=0
    # Every shortest path for every unordered endpoint pair, including
    # zero-length paths. No sampling or truncation is used.
    for s in range(N):
        for t in range(s,N):
            L=ds[s][t]
            def visit(path: list[int]) -> None:
                nonlocal paths_checked, visits_checked
                x=path[-1]
                if x==t:
                    assert len(path)==L+1
                    for i,S in enumerate(faceverts):
                        positions=[k for k,j in enumerate(path) if j in S]
                        assert len(positions)<=budgets[i]+1
                        if positions:
                            assert positions[-1]-positions[0]<=budgets[i]
                        visits_checked+=1
                    assert 5*(L+1)<=cover_budget
                    tail=path[B+1:]
                    assert set(tail)<=disjoint_classes[s]
                    assert len(tail)==len(set(tail))<=K
                    assert L<=B+K
                    paths_checked+=1
                    return
                for y in sorted(adj[x]):
                    if ds[s][y]==ds[s][x]+1 and ds[s][y]+ds[y][t]==L:
                        visit(path+[y])
            visit([s])
    return {
        'hull_candidate_facets':252, 'integer_determinants_checked':1260,
        'hull_facets':N,'primal_graph_edges':sum(map(len,adj))//2,
        'dantzig_pair_distance':ds[X][Y], 'graph_diameter':diameter,
        'dual_vertex_degrees':dual_degree,
        'unique_good_source_rows_both_orientations':[goodX,goodY],
        'intrinsic_primal_facet_diameters':budgets,
        'cover_multiplicity':5,'sum_diameter_plus_one':cover_budget,
        'face_cover_upper_bound':cover_budget//5-1,
        'proper_faces_in_fractional_cover_audit':len(proper_face_keys),
        'optimal_fractional_incidence_cover_cost':len(dual_vertices),
        'max_face_disjoint_class_size':K,'order_sensitive_tail_bound':B+K,
        'all_shortest_paths_checked':paths_checked,'face_visit_checks':visits_checked,
        'scope':'exact integer hull test and finite graph regression; not a Lean hull certificate',
    }

if __name__=='__main__':
    print(json.dumps(analyze(),indent=2))
