#!/usr/bin/env python3
"""Exact finite checks for a separate universal Lean theorem.

All vertices are reconstructed independently from the 15 original two-row
systems. Edge incidence is checked by common-row slices in the full vertex
reference. No numerical tolerances or floating-point linear algebra.
"""
from fractions import Fraction as Q
from itertools import combinations
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random


def dot(x,y): return sum((a*b for a,b in zip(x,y)),Q(0))


def rows(e):
    a=[-Q(1),Q(0),e,2*e,3*e,Q(1)]
    mean=sum(a)/6; square=sum(t*t for t in a)/6
    return a,[(t-mean,t*t-square) for t in a]


def solve(x,y):
    det=x[0]*y[1]-x[1]*y[0]
    if not det:return None
    return ((y[1]-x[1])/det,(x[0]-y[0])/det)


def explicit(e):
    D=1+4*e*e;E=1+10*e*e;F=2-7*e*e;G=1+3*e+7*e*e
    return [(9*e/D,-3/D),(3*e/D,-3/D),(15*e/E,-3/E),(Q(0),3/F),(-3/G,-3/G)]


def full_graph(A):
    V={}
    for i,j in combinations(range(6),2):
        x=solve(A[i],A[j])
        if x is not None and all(dot(r,x)<=1 for r in A):
            V[x]=frozenset(i for i,r in enumerate(A) if dot(r,x)==1)
    edges=set()
    for u,v in combinations(V,2):
        common=V[u]&V[v]
        if len(common)==1:
            # Full original reference: only these two vertices maximize row i.
            i=next(iter(common))
            assert {x for x in V if dot(A[i],x)==1}=={u,v}
            edges.add(frozenset((u,v)))
    return V,edges


def audit_saved(record):
    e=Q(record['e']);assert 0<e<Q(1,4)
    a,A=rows(e);pts=[tuple(map(Q,x)) for x in record['points']]
    assert len(pts)==5 and all(len(x)==2 for x in pts)
    expected=[{2,3},{1,2},{3,4},{0,5},{0,1}]
    for x,I in zip(pts,expected):
        vals=[dot(r,x) for r in A]
        assert all(y<=1 for y in vals) and {i for i,y in enumerate(vals) if y==1}==I
        i,j=sorted(I)
        assert A[i][0]*A[j][1]-A[i][1]*A[j][0]!=0
    u,l,r,v,b=pts
    f=lambda x:dot(A[0],x)+dot(A[5],x)
    gap=f(v)-f(u);gl=f(l)-f(u);gr=f(r)-f(u)
    assert gap>0 and 0<gr<gl<2*e*e*gap
    assert Q(record['gap'])==gap and Q(record['left_fraction'])==gl/gap and Q(record['right_fraction'])==gr/gap
    assert gl/gap==2*e*e/(1+2*e*e)
    assert gr/gap==2*e*e*(1-2*e*e)/((1+2*e*e)*(1+10*e*e))
    assert record['path']==[0,1,4,3]
    for i,j in zip(record['path'],record['path'][1:]):
        assert pts[i]!=pts[j] and len(expected[i]&expected[j])==1
        mid=tuple((x+y)/2 for x,y in zip(pts[i],pts[j]))
        assert all(dot(row,mid)<=1 for row in A)
        assert {k for k,row in enumerate(A) if dot(row,mid)==1}==expected[i]&expected[j]
    return 30


def run():
    rng=random.Random(304)
    es={Q(1,n) for n in range(5,41)}|{Q(1,2**k) for k in [8,16,32,64,128]}
    for _ in range(20):es.add(Q(rng.randrange(1,100),401))
    counts=dict(models=0,square_systems=0,vertices=0,edges=0,original_point_rows=0,
                neighbor_classifications=0,route_edges=0)
    saved=[]
    for e in sorted(es):
        a,A=rows(e);pts=explicit(e);V,E=full_graph(A)
        assert len(V)==6 and len(E)==6
        u,l,r,v,b=pts
        assert all(x in V for x in pts)
        neighbors={next(iter(edge-{u})) for edge in E if u in edge}
        assert neighbors=={l,r}
        f=lambda x:dot(A[0],x)+dot(A[5],x)
        gap=f(v)-f(u)
        rec=dict(e=str(e),points=[[str(y) for y in x] for x in pts],gap=str(gap),
                 left_fraction=str((f(l)-f(u))/gap),right_fraction=str((f(r)-f(u))/gap),
                 path=[0,1,4,3])
        audit_saved(rec)
        for i,j in zip(rec['path'],rec['path'][1:]):assert frozenset((pts[i],pts[j])) in E
        dist={u:0};q=deque([u])
        while q:
            x=q.popleft()
            for edge in E:
                if x in edge:
                    y=next(iter(edge-{x}))
                    if y not in dist:dist[y]=dist[x]+1;q.append(y)
        assert dist[v]==3
        saved.append(rec)
        counts['models']+=1;counts['square_systems']+=15;counts['vertices']+=6;counts['edges']+=6
        counts['original_point_rows']+=30;counts['neighbor_classifications']+=1;counts['route_edges']+=3
    deltas=[Q(1,2**k) for k in [0,1,4,16,64,128]]+[Q(2),Q(17,101)]
    for d in deltas:
        e=min(Q(1,8),d/4)
        assert 0<e<Q(1,4) and 2*e*e<d
        a,A=rows(e);u,l,r,v,b=explicit(e);f=lambda x:dot(A[0],x)+dot(A[5],x)
        assert all(0<f(x)-f(u)<d*(f(v)-f(u)) for x in [l,r])
    old_exp,old_solve,old_graph=explicit,solve,full_graph
    def disabled(*a,**k): raise AssertionError('construction called in saved audit')
    try:
        globals()['explicit']=globals()['solve']=globals()['full_graph']=disabled
        audit_rows=sum(audit_saved(r) for r in saved)
    finally:globals()['explicit'],globals()['solve'],globals()['full_graph']=old_exp,old_solve,old_graph
    forged=[]
    mutators=[('wrong source',lambda r:r['points'][0].__setitem__(0,'99')),
              ('wrong neighbor',lambda r:r['points'].__setitem__(1,r['points'][3])),
              ('wrong fraction',lambda r:r.update(left_fraction='1')),
              ('zero parameter',lambda r:r.update(e='0')),
              ('wrong route',lambda r:r.update(path=[0,3,4,3]))]
    for name,fn in mutators:
        r=deepcopy(saved[0]);fn(r)
        try:audit_saved(r)
        except (AssertionError,ZeroDivisionError):forged.append(name)
        else:raise AssertionError('forged record accepted: '+name)
    return dict(status='PASS',counts=counts,delta_choices=len(deltas),forgeries_rejected=forged,
                saved_audit=dict(records=len(saved),rows=audit_rows,all_constructors_disabled=True),
                examples=[saved[0],saved[-1]],
                scope='Exact finite arithmetic and complete small graphs, not Lean verification or a formal shortestness theorem.'),saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    report,fixture=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,data in [('report.json',report),('fixtures.json',fixture)]:
        (a.out/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
