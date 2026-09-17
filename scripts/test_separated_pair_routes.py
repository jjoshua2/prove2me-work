#!/usr/bin/env python3
"""Independent exact checks; the separate Lean theorem covers all real nodes."""
from fractions import Fraction as Q
from itertools import combinations
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, math


def support(b):
    return tuple(sorted(j for i in b for j in (i, i+1)))


def valid(m,b):
    return all(0 <= x and x+1 < m for x in b) and all(x+1 < y for x,y in zip(b,b[1:]))


def pack(m,b):
    if not valid(m,b): raise ValueError('invalid separated pairs')
    states=[tuple(b)]
    while states[-1] != tuple(2*i for i in range(len(b))):
        c=list(states[-1]);i=next(i for i,x in enumerate(c) if x!=2*i)
        assert c[i]>2*i and all(c[j]==2*j for j in range(i))
        c[i]-=1
        assert valid(m,c) and sum(c)+1==sum(states[-1])
        old,new=set(support(states[-1])),set(support(c))
        assert len(old-new)==len(new-old)==1
        states.append(tuple(c))
    assert len(states)-1==sum(b)-len(b)*(len(b)-1)
    return states


def route(m,b,c):
    p,q=pack(m,b),pack(m,c)
    r=p+list(reversed(q[:-1]))
    assert r[0]==tuple(b) and r[-1]==tuple(c)
    assert len(r)-1 <= 2*len(b)*m
    return r


def mul(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return r


def poly(a,S):
    r=[Q(1)]
    for i in S:r=mul(r,[-a[i],Q(1)])
    return r


def evaluate(p,t):
    z=Q(0)
    for c in reversed(p):z=z*t+c
    return z


def matrix(a,d):
    means=[sum(t**j for t in a)/len(a) for j in range(1,d+1)]
    return [tuple(t**j-means[j-1] for j in range(1,d+1)) for t in a]


def dot(a,x):return sum((r*s for r,s in zip(a,x)),Q(0))


def inverse(A):
    n=len(A);M=[list(r)+[Q(i==j) for j in range(n)] for i,r in enumerate(A)]
    for j in range(n):
        p=next((i for i in range(j,n) if M[i][j]),None)
        if p is None:return None
        M[j],M[p]=M[p],M[j];z=M[j][j];M[j]=[t/z for t in M[j]]
        for i in range(n):
            if i!=j:
                z=M[i][j];M[i]=[x-z*y for x,y in zip(M[i],M[j])]
    return tuple(tuple(r[n:]) for r in M)


def point(a,S):
    p=poly(a,S);vals=[evaluate(p,t) for t in a];h=sum(vals)/len(a)
    assert h>0 and all(z>=0 for z in vals)
    return tuple(-p[j]/h for j in range(1,len(p)))


def reference(a,d):
    A=matrix(a,d);V={};systems=0
    for S in combinations(range(len(a)),d):
        systems+=1;R=inverse([A[i] for i in S])
        if R is None:continue
        x=tuple(sum(r) for r in R)
        if all(dot(r,x)<=1 for r in A):
            I=tuple(i for i,r in enumerate(A) if dot(r,x)==1)
            assert len(I)==d;V[I]=x
    G={S:set() for S in V}
    for S,T in combinations(V,2):
        if len(set(S)&set(T))==d-1:G[S].add(T);G[T].add(S)
    return A,V,G,systems


def distance(G,S,T):
    q=deque([S]);D={S:0}
    while q:
        z=q.popleft()
        if z==T:return D[z]
        for y in G[z]:
            if y not in D:D[y]=D[z]+1;q.append(y)
    raise AssertionError('reference disconnected')


def run():
    counts=dict(models=0,square_systems=0,full_vertices=0,configurations=0,routes=0,
                route_edges=0,shortest_edges=0,nonshortest=0,exact_row_checks=0,common_rank_checks=0)
    reports=[];saved=[]
    for k,m in [(0,1),(1,5),(1,8),(2,7),(2,9),(3,9),(3,10)]:
        a=[Q(i*i+i,7) for i in range(m)];d=2*k
        A,V,G,ns=reference(a,d)
        B=[b for b in combinations(range(m-1),k) if valid(m,b)]
        cache={b:point(a,support(b)) for b in B}
        assert all(cache[b]==V[support(b)] for b in B)
        pairs=list(combinations(B,2))
        # Deterministic representative sample while all configurations are checked.
        pairs=pairs[:80]+[(B[-1],B[-1])]
        model=dict(dimension=d,rows=m,all_vertices=len(V),paired_vertices=len(B),pairs=len(pairs),max_route=0)
        seen_edges=set()
        for b,c in pairs:
            r=route(m,b,c);L=len(r)-1;D=distance(G,support(b),support(c))
            assert L>=D
            counts['routes']+=1;counts['route_edges']+=L;counts['shortest_edges']+=D;counts['nonshortest']+=L>D
            model['max_route']=max(model['max_route'],L)
            for B0,B1 in zip(r,r[1:]):
                S,T=support(B0),support(B1);x,y=cache[B0],cache[B1]
                assert T in G[S] and x!=y
                if (S,T) not in seen_edges:
                    seen_edges.add((S,T));C=set(S)&set(T)
                    # Recover a right inverse on d-1 common ORIGINAL rows from the full source inverse.
                    R=inverse([A[i] for i in S]);keep=[S.index(i) for i in sorted(C)]
                    assert all(sum(A[S[i]][h]*R[h][j] for h in range(d))==int(i==j) for i in keep for j in keep)
                    assert {z for z in V if sum(dot(A[i],V[z]) for i in C)==len(C)}=={S,T}
                    counts['common_rank_checks']+=1
            if len(saved)<7:saved.append(dict(a=list(map(str,a)),starts=list(b),ends=list(c),states=[list(t) for t in r],points=[[str(x) for x in cache[t]] for t in r]))
        for b,x in cache.items():
            assert {i for i,row in enumerate(A) if dot(row,x)==1}==set(support(b))
            assert all(dot(row,x)<=1 for row in A);counts['exact_row_checks']+=m
        counts['models']+=1;counts['square_systems']+=ns;counts['full_vertices']+=len(V);counts['configurations']+=len(B)
        reports.append(model)
    large=[]
    for k,m in [(4,16),(8,25),(16,41)]:
        b=[2*i+3+(i//3) for i in range(k)];c=[2*i+(i//4) for i in range(k)]
        a=[Q(i,3)+Q(i*i,101) for i in range(m)];A=matrix(a,2*k)
        r=route(m,b,c);checks=0
        for B in set(r):
            x=point(a,support(B));vals=[dot(row,x) for row in A]
            assert max(vals)<=1 and {i for i,v in enumerate(vals) if v==1}==set(support(B));checks+=m
        large.append(dict(dimension=2*k,rows=m,edges=len(r)-1,bound=2*k*m,unique_vertices=len(set(r)),row_checks=checks,full_graph_enumerated=False))
        saved.append(dict(a=list(map(str,a)),starts=b,ends=c,states=[list(t) for t in r],points=[[str(x) for x in point(a,support(t))] for t in r]))
    # Endpoint coverage boundary: wrapping root set is a valid vertex but not a line pairing.
    a=list(map(Q,range(5)));A=matrix(a,2);q=poly(a,[0,4]);mu=sum(evaluate(q,t) for t in a)/5
    wrap_x=tuple(-q[j]/mu for j in (1,2));assert mu<0 and all(dot(row,wrap_x)<=1 for row in A)
    assert all(support(b)!=(0,4) for b in combinations(range(4),1))
    # Saved path audit has no access to the route or polynomial producer.
    oldroute,oldpack,oldpoint=route,pack,point
    def kill(*args):raise AssertionError('producer during audit')
    try:
        globals()['route']=globals()['pack']=globals()['point']=kill
        replay_edges=0
        for s in saved:
            a=tuple(map(Q,s['a']));d=2*len(s['starts']);A=matrix(a,d);states=s['states'];points=[tuple(map(Q,v)) for v in s['points']]
            assert states[0]==s['starts'] and states[-1]==s['ends'] and len(points)==len(states)
            assert len(states)-1<=d*len(a)
            for b,x in zip(states,points):
                assert valid(len(a),b) and all(dot(row,x)<=1 for row in A)
                assert {i for i,row in enumerate(A) if dot(row,x)==1}==set(support(b))
            for b,c,x,y in zip(states,states[1:],points,points[1:]):
                assert x!=y and len(set(support(b))&set(support(c)))==d-1
                replay_edges+=1
    finally:globals()['route'],globals()['pack'],globals()['point']=oldroute,oldpack,oldpoint
    return dict(status='PASS',counts=counts,models=reports,large=large,
                excluded_wrapping_vertex=dict(roots=[0,4],mean=str(mu),point=list(map(str,wrap_x))),
                saved_replay=dict(records=len(saved),edges=replay_edges,route_and_polynomial_producers_disabled=True),
                scope='Exact supporting tests, not Lean verification. Separated line-pairs only; no all-moment or unrestricted diameter theorem.'),saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    report,saved=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for n,data in [('tests.json',report),('fixtures.json',saved)]:
        (a.out/n).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['counts'],sort_keys=True));print(report['large'])
if __name__=='__main__':main()
