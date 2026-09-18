#!/usr/bin/env python3
"""Exact finite regression for the separate alternating-complement Lean theorem.

This tests the explicitly constructed route, not a supplied short-path oracle.
The optional moment interpretation is rational arithmetic, not Lean verification.
"""
from __future__ import annotations
from collections import Counter, deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import random


def legal(m: int, h: tuple[int, ...]) -> bool:
    return (all(0 <= x < m for x in h)
            and all(x < y for x, y in zip(h, h[1:]))
            and (not h or all(x % 2 == (h[0] + i) % 2 for i, x in enumerate(h))))


def pack(m: int, h: tuple[int, ...]) -> list[tuple[int, ...]]:
    if not legal(m, h):
        raise ValueError('invalid alternating complement')
    b = h[0] % 2 if h else 0
    return [tuple(b+i if i < t else x for i, x in enumerate(h))
            for t in range(len(h)+1)]


def construct(m: int, h: tuple[int, ...], k: tuple[int, ...]) -> list[tuple[int, ...]]:
    if len(h) != len(k):
        raise ValueError('unequal complement sizes')
    raw = pack(m, h) + list(reversed(pack(m, k)))
    path: list[tuple[int, ...]] = []
    for point in raw:
        if not path or path[-1] != point:
            path.append(point)
    return path


def audit(m: int, h: tuple[int, ...], k: tuple[int, ...], path: list[tuple[int, ...]]) -> int:
    r = len(h)
    if not path or len(k) != r or path[0] != h or path[-1] != k:
        raise ValueError('endpoints')
    if len(path)-1 > 2*r+1:
        raise ValueError('length')
    U = set(range(m))
    for H in path:
        if not legal(m, H) or len(H) != r or len(U-set(H)) != m-r:
            raise ValueError('configuration')
    for H, K in zip(path, path[1:]):
        if H == K or len(set(H)&set(K))+1 != r:
            raise ValueError('complement exchange')
        S, T = U-set(H), U-set(K)
        if S == T or len(S&T)+1 != m-r:
            raise ValueError('root exchange')
    return len(path)-1


def distances(V: list[tuple[int, ...]]) -> dict[tuple[int, ...], dict[tuple[int, ...], int]]:
    if not V:
        return {}
    r = len(V[0])
    sets = {v: set(v) for v in V}
    graph = {u: [v for v in V if u != v and len(sets[u]&sets[v])+1 == r] for u in V}
    all_dist = {}
    for u in V:
        dist = {u: 0}; queue = deque([u])
        while queue:
            x = queue.popleft()
            for y in graph[x]:
                if y not in dist:
                    dist[y] = dist[x]+1
                    queue.append(y)
        if len(dist) != len(V):
            raise AssertionError('independent graph disconnected')
        all_dist[u] = dist
    return all_dist


def polynomial(roots: list[Q]) -> list[Q]:
    coeff = [Q(1)]
    for x in roots:
        new = [Q(0)]*(len(coeff)+1)
        for j, c in enumerate(coeff):
            new[j] -= x*c
            new[j+1] += c
        coeff = new
    return coeff


def evaluate(coeff: list[Q], x: Q) -> Q:
    v = Q(0)
    for c in reversed(coeff):
        v = v*x+c
    return v


def moment_check(a: list[Q], H: tuple[int, ...]) -> dict[str, int]:
    m, d = len(a), len(a)-len(H)
    # No original moment instance exists when the complement is empty (d=m).
    if not H:
        return {'excluded_d_equals_m': 1}
    S = sorted(set(range(m))-set(H))
    coeff = polynomial([a[i] for i in S])
    vals = [evaluate(coeff, x) for x in a]
    mean = sum(vals)/m
    assert mean != 0 and all(z/mean >= 0 for z in vals)
    point = [-coeff[j]/mean for j in range(1, d+1)]
    means = [sum(x**j for x in a)/m for j in range(1, d+1)]
    rows = [sum(((x**j-means[j-1])*point[j-1] for j in range(1, d+1)), Q(0)) for x in a]
    assert all(row == 1-v/mean and row <= 1 for row, v in zip(rows, vals))
    assert [i for i, row in enumerate(rows) if row == 1] == S
    return {'moment_instances': 1, 'moment_rows': m,
            'negative_mean_instances': int(mean < 0)}


def run() -> tuple[dict, list[dict]]:
    counts: Counter[str] = Counter()
    model_records = []
    saved = []
    adverse = None
    target_loss = None
    for m in range(11):
        for r in range(m+1):
            V = [h for h in combinations(range(m), r) if legal(m, h)]
            dist = distances(V)
            model = Counter(models=1, configurations=len(V))
            for h in V:
                if m:
                    model.update(moment_check([Q(i*i+3*i, 7) for i in range(m)], h))
                for k in V:
                    route = construct(m, h, k)
                    L = audit(m, h, k, route)
                    model.update(endpoint_pairs=1, edges=L, shortest_edges=dist[h][k])
                    model['nonshortest'] += L > dist[h][k]
                    model['repeated_vertex_routes'] += len(set(route)) < len(route)
                    lost = any(not ((set(range(m))-set(H)) & (set(range(m))-set(k))) <= (set(range(m))-set(K))
                               for H, K in zip(route, route[1:]))
                    model['target_row_loss_routes'] += lost
                    if L > dist[h][k] and adverse is None:
                        adverse = {'m':m, 'h':h, 'k':k, 'path':route, 'length':L, 'distance':dist[h][k]}
                    if lost and target_loss is None:
                        target_loss = {'m':m, 'h':h, 'k':k, 'path':route}
                    if h != k and not any(z['m']==m and z['r']==r for z in saved):
                        saved.append({'m':m,'r':r,'h':h,'k':k,'path':route})
            counts.update(model)
            model_records.append({'m':m,'r':r,**model})
    large = []
    for m, r in [(65,1),(65,32),(65,64),(1000,3),(1000,100),(10000,64)]:
        h = tuple(2*(m-r)//4+i for i in range(r))
        k = tuple(m-r+i for i in range(r))
        # Both are consecutive configurations but may have opposite phases.
        route = construct(m,h,k); L = audit(m,h,k,route)
        large.append({'m':m,'r':r,'length':L,'bound':2*r+1,'full_graph_enumerated':False})
        saved.append({'m':m,'r':r,'h':h,'k':k,'path':route})
    # Add disconnected-looking, separated hole pairs with opposite phases.
    for m,r in [(127,32),(257,64)]:
        h=tuple(3*i for i in range(r)); k=tuple(3*i+1 for i in range(r))
        route=construct(m,h,k); L=audit(m,h,k,route)
        large.append({'m':m,'r':r,'length':L,'bound':2*r+1,'full_graph_enumerated':False})
        saved.append({'m':m,'r':r,'h':h,'k':k,'path':route})
    # A finite test of the written moment interpretation on a separated,
    # phase-changing path. It is NOT an all-real geometric Lean theorem.
    large_numeric=Counter()
    h,k=(0,3,6,9),(1,4,7,10)
    for H in construct(13,h,k):
        large_numeric.update(moment_check([Q(i,13) for i in range(13)],H))
    oldpack,oldconstruct=globals()['pack'],globals()['construct']
    def forbidden(*args,**kwargs):
        raise AssertionError('route producer used during saved audit')
    try:
        globals()['pack']=globals()['construct']=forbidden
        replay_edges=sum(audit(c['m'],tuple(c['h']),tuple(c['k']),[tuple(x) for x in c['path']]) for c in saved)
    finally:
        globals()['pack'],globals()['construct']=oldpack,oldconstruct
    fixture=next(c for c in saved if c['m']==8 and c['r']==3)
    rejected=[]
    mutations=[('wrong endpoint',lambda c:c.update(k=(0,1,2))),
               ('stationary step',lambda c:c['path'].insert(1,c['path'][0])),
               ('out of range',lambda c:c['path'].__setitem__(0,(0,1,100))),
               ('wrong size',lambda c:c['path'].__setitem__(1,(0,1))),
               ('broken parity',lambda c:c['path'].__setitem__(1,(0,2,4))),
               ('unsorted labels',lambda c:c['path'].__setitem__(1,(3,1,0)))]
    # Change a target to a definitely different tuple, including in the first control.
    for name, mutate in mutations:
        c=deepcopy(fixture); mutate(c)
        if name=='wrong endpoint': c['k']=tuple(range(c['m']-c['r'],c['m']))
        try:
            audit(c['m'],tuple(c['h']),tuple(c['k']),[tuple(x) for x in c['path']])
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError('malformed record accepted: '+name)
    return ({'status':'PASS','counts':dict(counts),'models':model_records,'large':large,
             'large_numeric':dict(large_numeric),'nonshortest_example':adverse,
             'target_loss_example':target_loss,'saved_records':len(saved),'saved_edges':replay_edges,
             'construction_disabled_replay':True,'rejected':rejected,
             'scope':'Exact finite regression; not Lean verification, a shortest-path policy, target-locking theorem, or unrestricted Polynomial Hirsch.'},saved)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    report,saved=run()
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    for name,data in [('exact-tests.json',report),('fixtures.json',saved)]:
        (args.out/name).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))

if __name__=='__main__':
    main()
