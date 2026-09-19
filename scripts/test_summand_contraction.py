#!/usr/bin/env python3
"""Exact finite support/edge tests; not a Lean-extracted solver or proof by samples."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random


def add(x, y): return tuple(a+b for a,b in zip(x,y))
def sub(x, y): return tuple(a-b for a,b in zip(x,y))
def dot(x, y): return sum((a*b for a,b in zip(x,y)),F(0))
def cross(x,y): return x[0]*y[1]-x[1]*y[0]


def hull(points):
    pts=sorted(set(tuple(map(F,p)) for p in points))
    if len(pts)<=1:return pts
    halves=[]
    for seq in (pts, list(reversed(pts))):
        part=[]
        for p in seq:
            while len(part)>=2 and cross(sub(part[-1],part[-2]),sub(p,part[-1]))<=0:part.pop()
            part.append(p)
        halves.append(part[:-1])
    return halves[0]+halves[1]


def consecutive(H,x,y):
    if x==y:return False
    return any({x,y}=={H[i],H[(i+1)%len(H)]} for i in range(len(H)))


def segment_parameter(x,y,z):
    D=sub(y,x)
    if all(t==0 for t in D):
        if z!=x:raise ValueError('not a singleton member')
        return F(0)
    j=next(j for j,t in enumerate(D) if t)
    t=(z[j]-x[j])/D[j]
    if not 0<=t<=1 or any(c!=a+t*b for a,b,c in zip(x,D,z)):
        raise ValueError('not in whole segment')
    return t


def unique_components(P,Q,z):
    choices=[(p,q) for p in P for q in Q if add(p,q)==z]
    if len(choices)!=1:raise ValueError('nonunique or absent vertex split')
    return choices[0]


def contract(w):
    out=[]
    for z in w:
        if not out or z!=out[-1]:out.append(z)
    return out


def support_normal(R,x,y):
    if len(R)==2:return (F(0),F(0))
    D=sub(y,x);f=(D[1],-D[0])
    if max(dot(f,z) for z in R)>dot(f,x):f=tuple(-t for t in f)
    return f


def edge_record(P,Q,R,x,y):
    p,q=unique_components(P,Q,x);p1,q1=unique_components(P,Q,y)
    D=sub(y,x);j=next(j for j,t in enumerate(D) if t)
    alpha=(p1[j]-p[j])/D[j]
    return dict(P=P,Q=Q,R=R,x=x,y=y,p=p,q=q,p1=p1,q1=q1,
                f=support_normal(R,x,y),alpha=alpha)


def audit(c):
    P,Q,R=[list(map(lambda x:tuple(map(F,x)),c[k])) for k in ('P','Q','R')]
    x,y,p,q,p1,q1=[tuple(map(F,c[k])) for k in ('x','y','p','q','p1','q1')]
    f=tuple(map(F,c['f']));alpha=F(c['alpha'])
    if x==y or p not in P or p1 not in P or q not in Q or q1 not in Q:raise ValueError('endpoint membership')
    if add(p,q)!=x or add(p1,q1)!=y:raise ValueError('wrong split')
    # The complete input sum is checked without invoking hull or split discovery.
    rx=dot(f,x)
    for a in P:
        for b in Q:
            z=add(a,b)
            if dot(f,z)>rx:raise ValueError('invalid sum exposer')
            if dot(f,z)==rx:segment_parameter(x,y,z)
    if dot(f,y)!=rx:raise ValueError('endpoint not on exposed face')
    D=sub(y,x)
    if not 0<=alpha<=1:raise ValueError('negative component direction')
    if sub(p1,p)!=tuple(alpha*t for t in D):raise ValueError('bad left fraction')
    if sub(q1,q)!=tuple((1-alpha)*t for t in D):raise ValueError('bad right fraction')
    comparisons=0
    for S,a,b in ((P,p,p1),(Q,q,q1)):
        top=dot(f,a)
        if dot(f,b)!=top:raise ValueError('factor endpoint outside face')
        for z in S:
            comparisons+=1
            if dot(f,z)>top:raise ValueError('not a factor support')
            if dot(f,z)==top:segment_parameter(a,b,z)
    return dict(comparisons=comparisons,left_moves=int(p!=p1),right_moves=int(q!=q1),both_move=int(p!=p1 and q!=q1))


def run():
    rng=random.Random(309);counts=Counter();models=[];saved=[]
    squares=[(0,0),(1,0),(1,1),(0,1)]
    examples=[(squares,squares),(squares,[(0,0),(2,0)]),
              (squares,[(3,-2)]), ([(0,0),(1,0)],[(0,0),(0,1)]),
              ([(0,0),(1,0)],[(0,0),(2,0)]), ([(0,0)],[(1,1)])]
    for n in range(50):
        P=hull([(rng.randrange(-9,10),rng.randrange(-9,10)) for _ in range(8)])
        Q=hull([(rng.randrange(-7,8),rng.randrange(-7,8)) for _ in range(7)])
        examples.append((P,Q))
    for P,Q in examples:
        P,Q=hull(P),hull(Q);R=hull([add(p,q) for p in P for q in Q]);n=len(R)
        split={z:unique_components(P,Q,z) for z in R}
        stats=Counter()
        if n>1:
            for i,x in enumerate(R):
                y=R[(i+1)%n];c=edge_record(P,Q,R,x,y);a=audit(c);stats.update(a)
                assert (c['p']==c['p1'] or consecutive(P,c['p'],c['p1']))
                assert (c['q']==c['q1'] or consecutive(Q,c['q'],c['q1']))
                stats['sum_edges']+=1
                if len(saved)<18:saved.append(c)
        for i in range(n):
            for j in range(n):
                # Two orientations plus a full backtracking example at equal endpoints.
                for direction in (1,-1):
                    distance=(direction*(j-i))%n
                    path=[R[(i+direction*k)%n] for k in range(distance+1)]
                    A=contract([split[z][0] for z in path]);B=contract([split[z][1] for z in path])
                    assert len(A)<=len(path) and len(B)<=len(path)
                    assert A[0]==split[path[0]][0] and A[-1]==split[path[-1]][0]
                    assert B[0]==split[path[0]][1] and B[-1]==split[path[-1]][1]
                    assert all(consecutive(P,x,y) for x,y in zip(A,A[1:]))
                    assert all(consecutive(Q,x,y) for x,y in zip(B,B[1:]))
                    stats['walks']+=1;stats['sum_walk_edges']+=len(path)-1
                    stats['left_walk_edges']+=len(A)-1;stats['right_walk_edges']+=len(B)-1
        if n>1:
            path=[R[0],R[1],R[0]]
            assert all(consecutive(R,x,y) for x,y in zip(path,path[1:]))
            for side,S in ((0,P),(1,Q)):
                W=contract([split[z][side] for z in path])
                assert len(W)<=3 and all(consecutive(S,x,y) for x,y in zip(W,W[1:]))
            stats['backtrack_controls']+=1
        counts.update(stats);counts['models']+=1;counts['sum_vertices']+=n
        models.append(dict(left_vertices=len(P),right_vertices=len(Q),sum_vertices=n,**stats))
    # Exact product boxes. No full high-dimensional vertex enumeration.
    boxes=[]
    for d in (1,2,8,16,32,64):
        for qwidth in ([F(1,3)]*d,[F(2)]+[F(0)]*(d-1)):
            P=[F(0)]*d;Q=[F(0)]*d;Z=[F(0)]*d;la=lb=0
            for j in range(d):
                D=[F(0)]*d;D[j]=1+qwidth[j]
                A=[F(0)]*d;A[j]=1
                B=[F(0)]*d;B[j]=qwidth[j]
                alpha=1/(1+qwidth[j])
                assert A==[alpha*t for t in D] and B==[(1-alpha)*t for t in D]
                # The support functional fixes all other coordinates at their current endpoints.
                signs=[F(0) if i==j else F(1) if Z[i] else F(-1) for i in range(d)]
                fullmax=sum(max(F(0),signs[i]*(1+qwidth[i])) for i in range(d))
                assert dot(signs,Z)==fullmax and dot(signs,add(Z,D))==fullmax
                P=list(add(P,A));Q=list(add(Q,B));Z=list(add(Z,D));assert add(P,Q)==tuple(Z)
                la+=1;lb+=int(qwidth[j]>0)
            boxes.append(dict(dimension=d,sum_edges=d,left_edges=la,right_edges=lb,
                              mode='parallel_boxes' if all(qwidth) else 'segment_summand',full_graph_enumerated=False))
    # Ordinary linear projection is not a summand-vertex map: a tetrahedron edge
    # maps to a square diagonal under (x,y,z)->(x+z,y+z).
    image=hull([(0,0),(1,0),(0,1),(1,1)])
    assert not consecutive(image,(F(1),F(0)),(F(0),F(1)))
    # Replaying certificates must not call any hull, split or route constructor.
    old={n:globals()[n] for n in ('hull','unique_components','contract','edge_record')}
    def forbidden(*a,**k):raise AssertionError('constructor invoked by saved audit')
    try:
        for n in old:globals()[n]=forbidden
        for c in saved:audit(c)
    finally:globals().update(old)
    base=next(c for c in saved if c['p']!=c['p1'] and c['q']!=c['q1'])
    bad=[]
    for name,edit in [('false split',lambda c:c.update(p=c['p1'])),
                      ('wrong alpha',lambda c:c.update(alpha=F(3,2))),
                      ('stationary sum edge',lambda c:c.update(y=c['x'])),
                      ('bad support',lambda c:c.update(f=tuple(-v for v in c['f']))),
                      ('false component endpoint',lambda c:c.update(q1=c['q']))]:
        c=deepcopy(base);edit(c)
        try:audit(c)
        except (AssertionError,ValueError):bad.append(name)
        else:raise AssertionError('forgery accepted '+name)
    return dict(status='PASS',counts=dict(counts),models=models,boxes=boxes,saved_records=len(saved),
                discovery_disabled_replay=True,rejected=bad,
                projection_counterexample='tetrahedron edge e1-e2 maps to a nonedge square diagonal',
                scope='Exact finite support and edge tests; not Lean extraction or proof of a universal small completion.'),saved


def stringify(obj):
    if isinstance(obj,F):return str(obj)
    if isinstance(obj,dict):return {k:stringify(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)):return [stringify(x) for x in obj]
    return obj


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    report,records=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',records)]:
        (a.out/name).write_text(json.dumps(stringify(obj),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
