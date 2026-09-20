#!/usr/bin/env python3
"""Exact endpoint discovery and full-face route tests, separate from Lean."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random
import test_zonotope_regular_routes as route
sweep = route.sweep


def hull(points):
    p=sorted(set(points))
    if len(p)<=1:return p
    def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    low=[];high=[]
    for x in p:
        while len(low)>=2 and cross(low[-2],low[-1],x)<=0:low.pop()
        low.append(x)
    for x in reversed(p):
        while len(high)>=2 and cross(high[-2],high[-1],x)<=0:high.pop()
        high.append(x)
    return low[:-1]+high[:-1]


def corners(w,d):
    return {tuple(sum((Q(bits[i])*w[i][j] for i in range(len(w))),Q(0)) for j in range(d))
            for bits in product((0,1),repeat=len(w))}


def exposing(H,i):
    u=H[i]
    if len(H)==1:return (Q(0),Q(0))
    if len(H)==2:return sweep.sub(u,H[1-i])
    prev=H[i-1];nxt=H[(i+1)%len(H)]
    a=sweep.sub(u,prev);b=sweep.sub(nxt,u)
    return (a[1]+b[1],-a[0]-b[0])


def audit_endpoint(w,u,f,points=None):
    d=len(u)
    if len(f)!=d or any(len(x)!=d for x in w):raise ValueError('dimension')
    if any(not sweep.zero(x) and sweep.dot(f,x)==0 for x in w):raise ValueError('nonregular')
    chosen=tuple(sum((x[j] for x in w if sweep.dot(f,x)>0),Q(0)) for j in range(d))
    if chosen!=u:raise ValueError('wrong requested endpoint')
    if points is not None:
        if u not in points or any(x!=u and sweep.dot(f,x)>=sweep.dot(f,u) for x in points):
            raise ValueError('not unique over complete corners')
    return len(points) if points is not None else 0


def record(w,u,v,f,g,d):
    r=route.construct(w,f,g,d);r.update(requested_start=u,requested_target=v)
    return r


def audit(rec,exhaustive=True):
    w=[tuple(map(Q,x)) for x in rec['w']];d=rec['d']
    u,v=[tuple(map(Q,rec[k])) for k in ('requested_start','requested_target')]
    f,g=[tuple(map(Q,rec[k])) for k in ('f','g')]
    pts=corners(w,d) if exhaustive else None
    checks=audit_endpoint(w,u,f,pts)+audit_endpoint(w,v,g,pts)
    result=route.audit(rec,exhaustive)
    if tuple(map(Q,rec['vertices'][0]))!=u or tuple(map(Q,rec['vertices'][-1]))!=v:
        raise ValueError('route endpoints')
    result['requested_endpoint_comparisons']=checks
    return result


def run():
    rng=random.Random(316)
    systems=[[],[(0,0)],[(1,0)],[(1,0),(2,0),(-3,0)],[(1,0),(0,1)],
             [(1,0),(0,1),(1,1)],[(1,0),(0,1),(-1,0),(0,0)]]
    for _ in range(11):
        m=rng.randrange(2,7);w=[tuple(rng.randrange(-3,4) for _ in range(2)) for _ in range(m)]
        if m>3:w[-1]=tuple(-x for x in w[0])
        systems.append(w)
    counts=Counter();models=[];saved=[]
    for no,ww in enumerate(systems):
        w=[tuple(map(Q,x)) for x in ww];C=corners(w,2);H=hull(C)
        F=[exposing(H,i) for i in range(len(H))]
        for u,f in zip(H,F):counts['discovered_vertex_support_checks']+=audit_endpoint(w,u,f,C)
        counts['discovered_vertices']+=len(H);counts['nonvertex_corner_images']+=len(C)-len(H)
        counts['duplicate_boolean_images']+=2**len(w)-len(C)
        stats=Counter()
        for i,u in enumerate(H):
            for j,v in enumerate(H):
                r=record(w,u,v,F[i],F[j],2);stats.update(audit(r))
                V=[tuple(x) for x in r['vertices']]
                for a,b in zip(V,V[1:]):
                    ia,ib=H.index(a),H.index(b)
                    assert (ia-ib)%len(H) in (1,len(H)-1)
                    stats['independent_hull_edges']+=1
                shortest=min((j-i)%len(H),(i-j)%len(H)) if len(H)>1 else 0
                stats['nonshortest_routes']+=len(V)-1>shortest
                stats['zero_length_routes']+=len(V)==1
                if i==0 and j==len(H)-1:saved.append(r)
        counts.update(stats);models.append(dict(model=no,presented_generators=len(w),corner_images=len(C),vertices=len(H),**stats))
    # Zero-dimensional and higher-dimensional zero generator systems.
    for d,w in [(0,[]),(0,[()]),(3,[]),(3,[(Q(0),)*3])]:
        u=(Q(0),)*d;f=u;r=record(w,u,u,f,f,d);audit(r);saved.append(r)
    large=[]
    for d,rank in [(8,8),(16,16),(32,6),(64,6)]:
        w=[tuple(Q(j==i) for j in range(d)) for i in range(rank)]
        w += [sweep.scale(2,w[0]),sweep.scale(-3,w[0]),(Q(0),)*d]
        def endpoint(bits):
            return tuple((Q(3) if bits[j] else Q(-3)) if j==0 else Q(bits[j]) if j<rank else Q(0) for j in range(d))
        bits0=[0]*rank;bits1=[1]*rank
        u,v=endpoint(bits0),endpoint(bits1)
        # Objectives are recovered from the requested box-boundary coordinates.
        def objective(x):
            return tuple(Q(1) if j<rank and x[j]>0 else Q(-1) if j<rank else Q(0) for j in range(d))
        r=record(w,u,v,objective(u),objective(v),d);res=audit(r,False);saved.append(r)
        large.append(dict(ambient_dimension=d,rank=rank,full_graph_enumerated=False,**res))
    originals={name:getattr(route,name) for name in ('construct',)}
    old_hull,old_exposing=hull,exposing
    def fail(*a,**k):raise AssertionError('construction during replay')
    try:
        route.construct=fail;globals()['hull']=fail;globals()['exposing']=fail
        for r in saved:audit(r,len(r['w'])<=6)
    finally:
        route.construct=originals['construct'];globals()['hull']=old_hull;globals()['exposing']=old_exposing
    base=next(r for r in saved if len(r['crossings'])>=2);bad=[]
    mutations=[('wrong requested endpoint',lambda r:r.update(requested_start=(Q(999),)*r['d'])),
      ('zero objective',lambda r:r.update(f=(Q(0),)*r['d'])),
      ('wrong target sign',lambda r:r.update(g=tuple(-x for x in r['g']))),
      ('removed crossing',lambda r:r['crossings'].pop()),
      ('stationary step',lambda r:r['vertices'].__setitem__(1,r['vertices'][0]))]
    for name,fn in mutations:
        r=deepcopy(base);fn(r)
        try:audit(r)
        except (ValueError,AssertionError,ZeroDivisionError,StopIteration):bad.append(name)
        else:raise AssertionError('forgery accepted '+name)
    # Finite corner membership alone must not be mistaken for extremality.
    w=[(Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(1))];C=corners(w,2)
    assert (Q(1),Q(1)) in C and (Q(1),Q(1)) not in hull(C)
    return dict(status='PASS',counts=dict(counts),models=models,large=large,saved_records=len(saved),
      constructors_disabled=True,rejected=bad,nonvertex_corner_control=True,
      scope='Exact finite support/endpoint/edge checks, not Lean extraction or a generic input parser.'),saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r,s=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    r['dependency_hashes']={Path(m.__file__).name:hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest() for m in (route,sweep)}
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',r),('fixtures.json',s)]:
        (a.out/name).write_text(json.dumps(sweep.encode(obj),sort_keys=True,indent=2)+'\n')
    print(json.dumps(r['counts'],sort_keys=True),flush=True)
if __name__=='__main__':main()
