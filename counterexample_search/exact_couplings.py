#!/usr/bin/env python3
"""Exact external Q28 scalar-coupling certificates; no Lean verdict is claimed.

All geometry uses Fraction and integer Bareiss elimination. Seed completeness
exhausts all chamber bases. Fiber completeness and sign-quotient correctness
are explained in RESEARCH.md. Distances are shortest undirected apex distances.
"""
from fractions import Fraction as F
from itertools import combinations
from collections import deque, Counter
from pathlib import Path
import json

Q28=[(18,0,0,0,1),(0,0,30,0,1),(0,0,0,30,1),
     (0,5,0,25,1),(0,0,18,18,1),(0,0,18,0,-1),
     (0,30,0,0,-1),(30,0,0,0,-1),(25,0,0,5,-1),(18,18,0,0,-1)]


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),F(0))


def rank(rows):
    if not rows:return 0
    A=[list(map(F,row)) for row in rows];k=0
    for j in range(len(A[0])):
        p=next((i for i in range(k,len(A)) if A[i][j]),None)
        if p is None:continue
        A[k],A[p]=A[p],A[k];c=A[k][j]
        for i in range(k+1,len(A)):
            if A[i][j]:
                f=A[i][j];A[i]=[c*x-f*y for x,y in zip(A[i],A[k])]
        k+=1
        if k==len(A):break
    return k


def solve(A,b):
    n=len(A);M=[list(map(int,r))+[int(y)] for r,y in zip(A,b)];prev=1
    for k in range(n-1):
        p=next((j for j in range(k,n) if M[j][k]),None)
        if p is None:return None
        if p!=k:M[k],M[p]=M[p],M[k]
        c=M[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n+1):
                val=c*M[i][j]-M[i][k]*M[k][j]
                assert val%prev==0
                M[i][j]=val//prev
            M[i][k]=0
        prev=c
    if M[-1][-2]==0:return None
    x=[F(0)]*n
    for i in reversed(range(n)):
        x[i]=(F(M[i][-1])-dot(M[i][i+1:n],x[i+1:]))/M[i][i]
    return tuple(x)


def active_span(T,p):
    common=[list(a) for a in T if dot(a,p)==1]
    d=len(p)
    for j in range(d-1):
        if p[j]==0 and any(a[j] for a in common):
            common.append([int(i==j) for i in range(d)])
    return common


def seed_vertices():
    d=5;C=Q28+[tuple(-int(i==j) for i in range(d)) for j in range(4)]
    b=[1]*10+[0]*4;candidates=set();counts=Counter()
    for basis in combinations(range(14),5):
        p=solve([C[i] for i in basis],[b[i] for i in basis])
        if p is None:counts['singular']+=1;continue
        if any(dot(a,p)>c for a,c in zip(C,b)):
            counts['infeasible']+=1;continue
        candidates.add(p);counts['feasible_bases']+=1
    V=sorted(p for p in candidates if rank(active_span(Q28,p))==5)
    assert sum(counts.values())==2002 and len(candidates)==60 and len(V)==20
    return V,dict(counts)


def graph(T,V):
    d=len(T[0]);active=[frozenset(i for i,a in enumerate(T) if dot(a,p)==1) for p in V]
    zeros=[frozenset(j for j in range(d-1) if p[j]==0) for p in V]
    G=[[] for _ in V];cache={}
    for i,j in combinations(range(len(V)),2):
        common=active[i]&active[j]
        if not common:continue
        z=frozenset(k for k in zeros[i]&zeros[j] if any(T[t][k] for t in common))
        if len(common)+len(z)<d-1:continue
        key=(common,z)
        if key not in cache:
            M=[T[t] for t in common]+[[int(k==c) for k in range(d)] for c in z]
            cache[key]=rank(M)
        r=cache[key];assert r<d
        if r==d-1:G[i].append(j);G[j].append(i)
    return G


def bfs(G,start):
    ds=[-1]*len(G);prev=[-1]*len(G);ds[start]=0;Q=deque([start])
    while Q:
        i=Q.popleft()
        for j in G[i]:
            if ds[j]==-1:ds[j]=ds[i]+1;prev[j]=i;Q.append(j)
    return ds,prev


def skew_vertex(p,r):
    r=F(r);D=(r+1)-(r-1)*p[-1];assert D>0
    return tuple(2*x/D for x in p[:-1])+(((r+1)*p[-1]-(r-1))/D,)


def skew_templates(T,r):
    return [tuple((F(r)*a if t[-1]==1 else F(a)) for a in t[:-1])+(F(t[-1]),) for t in T]


def independent_couple(T,S):
    m=len(T[0])-1;q=len(S[0])-1
    return [tuple(t[:-1])+(0,)*q+(t[-1],) for t in T]+[(0,)*m+tuple(t[:-1])+(t[-1],) for t in S]


def fiber_vertices(V,G,Y,H):
    pts=set()
    for swap,(P,E,Q) in enumerate(((V,G,Y),(Y,H,V))):
        for i in range(len(P)):
            for j in E[i]:
                if j<=i or P[i][-1]==P[j][-1]:continue
                p,p2=P[i],P[j];lo,hi=sorted((p[-1],p2[-1]))
                for z in Q:
                    t=z[-1]
                    if not lo<=t<=hi:continue
                    lam=(t-p[-1])/(p2[-1]-p[-1])
                    x=tuple((1-lam)*a+lam*b for a,b in zip(p,p2))
                    v=x[:-1]+z[:-1]+(t,) if swap==0 else z[:-1]+x[:-1]+(t,)
                    pts.add(v)
    for p in V:
        for z in Y:
            if p[-1]==z[-1]:pts.add(p[:-1]+z[:-1]+(p[-1],))
    return sorted(pts)


def certify(T,V,G,ratios,expected_distance,expected_vertices,output):
    d=len(T[0]);m=d-1
    for p in V:
        assert all(x>=0 for x in p[:-1])
        assert all(dot(a,p)<=1 for a in T)
        assert rank(active_span(T,p))==d
    u=V.index((F(0),)*m+(F(1),));v=V.index((F(0),)*m+(F(-1),))
    ds,prev=bfs(G,u);assert all(x>=0 for x in ds)
    path=[v]
    while path[-1]!=u:path.append(prev[path[-1]])
    path.reverse()
    assert ds[v]==expected_distance
    assert all(abs(ds[i]-ds[j])<=1 for i in range(len(G)) for j in G[i])
    full_vertices=sum(2**sum(x!=0 for x in p[:-1]) for p in V)
    assert full_vertices==expected_vertices
    rows=sum(2**sum(x!=0 for x in a[:-1]) for a in T)
    s=dict(dimension=d,describing_rows=rows,full_vertices=full_vertices,orbits=len(V),
           quotient_edges=sum(map(len,G))//2,apex_distance=ds[v],ratios=ratios)
    data=dict(status='Exact external certificate; not Lean-checked',summary=s,
              templates=[[str(x) for x in a] for a in T],
              vertices=[[str(x) for x in p] for p in V],adjacency=G,
              source=u,target=v,distance_potential=ds,attaining_path=path)
    output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(s),flush=True)
    return data


def main():
    output=Path(__file__).resolve().parent/'generated';output.mkdir(exist_ok=True)
    V,counts=seed_vertices();G=graph(Q28,V)
    seed=certify(Q28,V,G,[1],6,274,output/'q28_exact.json')
    h=[V[i][-1] for i in seed['attaining_path']]
    assert all(a>b for a,b in zip(h,h[1:]))
    print('Strict six-edge seed heights:',list(map(str,h)))
    for r,N,L in [(1,24194,6),(2,35202,11),(3,32898,11),(10,22402,11)]:
        S=skew_templates(Q28,r);Y=[skew_vertex(p,r) for p in V]
        T=independent_couple(Q28,S);Z=fiber_vertices(V,G,Y,G);H=graph(T,Z)
        certify(T,Z,H,[1,r],L,N,output/f'fiber_{r}_exact.json')
        if r==2:T2,Z2,H2=T,Z,H
    S=skew_templates(Q28,7);Y=[skew_vertex(p,7) for p in V]
    T=independent_couple(T2,S);Z=fiber_vertices(Z2,H2,Y,G);H=graph(T,Z)
    certify(T,Z,H,[1,2,7],16,2539522,output/'triple_1_2_7_exact.json')
    (output/'seed_basis_counts.json').write_text(json.dumps(counts,indent=2)+'\n')
    print('PASS: exact seed completeness and all selected coupled graph certificates')

if __name__=='__main__':main()
