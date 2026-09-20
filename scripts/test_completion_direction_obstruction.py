#!/usr/bin/env python3
"""Exact checks for a written all-completion obstruction, NOT Lean verification.

Enumerate original H bases only in explicitly labelled small models. Test the
explicit deformed-cube family, genuine whole-edge slices, and 2D whole-set
Minkowski completions. The general real theorem is not inferred from samples.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from copy import deepcopy
from fractions import Fraction as F
from functools import cmp_to_key
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import random
from typing import Sequence

Vec=tuple[F,...]

def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def scale(c,a):return tuple(c*x for x in a)
def direction(a):
    for x in a:
        if x:return tuple(y/x for y in a)
    raise ValueError('zero direction')

def solve(A,b):
    n=len(A)
    if any(len(row)!=n for row in A):raise ValueError('not square')
    M=[list(map(F,row))+[F(t)] for row,t in zip(A,b)]
    for j in range(n):
        p=next((i for i in range(j,n) if M[i][j]),None)
        if p is None:return None
        M[j],M[p]=M[p],M[j]
        q=M[j][j];M[j]=[x/q for x in M[j]]
        for i in range(n):
            if i!=j:
                q=M[i][j]
                M[i]=[x-q*y for x,y in zip(M[i],M[j])]
    return tuple(row[-1] for row in M)

def rank(A):
    if not A:return 0
    M=[list(map(F,row)) for row in A];r=0
    for j in range(len(M[0])):
        p=next((i for i in range(r,len(M)) if M[i][j]),None)
        if p is None:continue
        M[r],M[p]=M[p],M[r];c=M[r][j];M[r]=[v/c for v in M[r]]
        for i in range(len(M)):
            if i!=r:
                c=M[i][j];M[i]=[x-c*y for x,y in zip(M[i],M[r])]
        r+=1
    return r

def rows(d,e):
    if d<1 or not 0<e<F(1,2):raise ValueError('requires d>=1 and 0<epsilon<1/2')
    R=[]
    for i in range(d):
        lo=[F(0)]*d;up=[F(0)]*d;lo[i]=-1;up[i]=1
        if i:lo[i-1]=up[i-1]=e
        R.extend([(tuple(lo),F(0)),(tuple(up),F(1))])
    return R

def vertex(bits,e):
    if any(x not in (0,1) for x in bits):raise ValueError('nonbinary label')
    x=[]
    for i,b in enumerate(bits):
        t=e*x[-1] if i else F(0)
        x.append(1-t if b else t)
    return tuple(x)

def vector_formula(d,k,tail,e):
    D=[F(0)]*k+[F(1)];v=F(1)
    for b in tail:v*=e*(1-2*b);D.append(v)
    if len(D)!=d:raise ValueError('tail size')
    return tuple(D)

def make_edge(d,e,k,prefix,tail):
    if len(prefix)!=k or len(tail)!=d-k-1:raise ValueError('label size')
    p=vertex(tuple(prefix)+(0,)+tuple(tail),e)
    q=vertex(tuple(prefix)+(1,)+tuple(tail),e)
    return dict(d=d,epsilon=str(e),k=k,prefix=list(prefix),tail=list(tail),
                source=list(map(str,p)),target=list(map(str,q)),
                normalized_direction=list(map(str,vector_formula(d,k,tail,e))))

def audit_edge(c):
    d=c['d'];e=F(c['epsilon']);k=c['k'];R=rows(d,e)
    p=tuple(map(F,c['source']));q=tuple(map(F,c['target']));D=tuple(map(F,c['normalized_direction']))
    if len(p)!=d or len(q)!=d or not 0<=k<d:raise ValueError('dimension')
    if p==q:raise ValueError('stationary edge')
    ip=[i for i,(a,b) in enumerate(R) if dot(a,p)==b]
    iq=[i for i,(a,b) in enumerate(R) if dot(a,q)==b]
    if any(dot(a,p)>b or dot(a,q)>b for a,b in R):raise ValueError('infeasible')
    if len(ip)!=d or len(iq)!=d or rank([R[i][0] for i in ip])!=d or rank([R[i][0] for i in iq])!=d:
        raise ValueError('not proved vertex')
    common=set(ip)&set(iq)
    if len(common)!=d-1 or rank([R[i][0] for i in common])!=d-1:raise ValueError('not full edge slice')
    delta=sub(q,p)
    if delta[k]<=0 or any(delta[i] for i in range(k)) or D!=direction(delta):raise ValueError('wrong direction')
    if len(c['prefix'])!=k or len(c['tail'])!=d-k-1:raise ValueError('label dimension')
    bits0=list(c['prefix'])+[0]+list(c['tail']);bits1=list(c['prefix'])+[1]+list(c['tail'])
    if any(t not in (0,1) for t in bits0+bits1):raise ValueError('bad labels')
    if ip!=[2*i+b for i,b in enumerate(bits0)] or iq!=[2*i+b for i,b in enumerate(bits1)]:raise ValueError('wrong labels')
    for j in range(k+1,d):
        if D[j]!=e*(1-2*c['tail'][j-k-1])*D[j-1]:raise ValueError('wrong sign recurrence')
    return dict(rows_checked=2*len(R),common_rank=d-1,nonzero_direction=True)

def hull2(pts):
    p=sorted(set(pts))
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

def polygon_rows(P):
    if len(P)==1:
        x,y=P[0];return [((F(1),F(0)),x),((F(-1),F(0)),-x),((F(0),F(1)),y),((F(0),F(-1)),-y)]
    if len(P)==2:
        a,b=P;D=sub(b,a);n=(D[1],-D[0])
        return [(n,dot(n,a)),(scale(-1,n),-dot(n,a)),(D,dot(D,b)),(scale(-1,D),-dot(D,a))]
    return [((D[1],-D[0]),dot((D[1],-D[0]),a))
            for a,b in zip(P,P[1:]+P[:1]) for D in [sub(b,a)]]

def zonogon(gens):
    # Exact repeated segment addition with complete 2D hull reconstruction.
    P=[(F(0),F(0))]
    for w in gens:P=hull2(P+[add(x,w) for x in P])
    return P

def complete_by_erosion(P,gens):
    Z=zonogon(gens);A=polygon_rows(Z)
    Qrows=[(a,b-max(dot(a,p) for p in P)) for a,b in A]
    Q=set()
    for (a,b),(c,d) in combinations(Qrows,2):
        x=solve([a,c],[b,d])
        if x is not None and all(dot(e,x)<=f for e,f in Qrows):Q.add(x)
    if not Q:raise ValueError('empty or unrepresented erosion')
    Q=hull2(Q)
    if hull2([add(p,q) for p in P for q in Q])!=Z:raise ValueError('not an actual Minkowski completion')
    return Q,Z

def audit_completion(c):
    P=[tuple(map(F,x)) for x in c['P']];Q=[tuple(map(F,x)) for x in c['Q']]
    G=[tuple(map(F,x)) for x in c['generators']];Z=[tuple(map(F,x)) for x in c['Z']]
    if zonogon(G)!=Z or hull2([add(p,q) for p in P for q in Q])!=Z:raise ValueError('false whole-set identity')
    pdirs={direction(sub(y,x)) for x,y in zip(P,P[1:]+P[:1]) if x!=y}
    gdirs={direction(w) for w in G if any(w)}
    if not pdirs<=gdirs:raise ValueError('missing summand direction')
    if c['claimed_original_directions']!=len(pdirs):raise ValueError('false direction count')
    # A 2D zonotope with >=2 directions has a cycle graph on 2r actual vertices.
    if len(gdirs)>=2 and len(Z)!=2*len(gdirs):raise ValueError('bad zonogon direction count')
    return dict(original_directions=len(pdirs),completion_directions=len(gdirs),
                completion_vertices=len(Z),all_pair_sums=len(P)*len(Q))

def run():
    totals=Counter();models=[];saved=[]
    for e in (F(1,4),F(1,3),F(2,5)):
        for d in range(1,7):
            R=rows(d,e);V={bits:vertex(bits,e) for bits in product((0,1),repeat=d)}
            independent=set()
            for I in combinations(range(2*d),d):
                x=solve([R[i][0] for i in I],[R[i][1] for i in I]);totals['original_square_bases']+=1
                if x is not None and all(dot(a,x)<=b for a,b in R):independent.add(x)
            assert independent==set(V.values()) and len(independent)==2**d
            facet_checks=0
            for i in range(d):
                for side in (0,1):
                    x=[F(1,2)]*d;lo=e*x[i-1] if i else F(0);x[i]=1-lo if side else lo
                    assert all(dot(a,x)==b if j==2*i+side else dot(a,x)<b for j,(a,b) in enumerate(R))
                    facet_checks+=len(R)
            edges=[];dirs=set();support_checks=0
            for bits,p in V.items():
                active={2*i+b for i,b in enumerate(bits)}
                assert all(dot(a,p)<=b for a,b in R)
                for k in range(d):
                    if bits[k]:continue
                    bb=bits[:k]+(1,)+bits[k+1:];q=V[bb]
                    c=make_edge(d,e,k,bits[:k],bits[k+1:]);audit_edge(c)
                    C=active&{2*i+b for i,b in enumerate(bb)}
                    score=tuple(sum((R[i][0][j] for i in C),F(0)) for j in range(d))
                    rhs=sum((R[i][1] for i in C),F(0))
                    maximizers={x for x in independent if dot(score,x)==rhs}
                    assert maximizers=={p,q};support_checks+=len(independent)
                    edges.append((bits,bb));dirs.add(direction(sub(q,p)))
            assert len(edges)==d*2**(d-1) and len(dirs)==2**d-1
            # Independent H tight-intersection adjacency equals the label cube.
            if d<=5:
                actual={frozenset((a,b)) for a,b in combinations(V,2)
                        if len({2*i+x for i,x in enumerate(a)}&{2*i+x for i,x in enumerate(b)})==d-1}
                assert actual=={frozenset(e) for e in edges}
                G={a:set() for a in V}
                for a,b in edges:G[a].add(b);G[b].add(a)
                diameter=0
                for start in V:
                    dist={start:0};queue=deque([start])
                    while queue:
                        a=queue.popleft()
                        for b in G[a]:
                            if b not in dist:dist[b]=dist[a]+1;queue.append(b)
                    assert all(dist[b]==sum(x!=y for x,y in zip(start,b)) for b in V)
                    diameter=max(diameter,max(dist.values()))
                assert diameter==d
                totals['all_pair_distances']+=len(V)**2
            counts=dict(vertices=len(V),edges=len(edges),directions=len(dirs),support_checks=support_checks,
                        facet_checks=facet_checks,original_facets=2*d,all_bases_enumerated=True)
            totals.update({k:v for k,v in counts.items() if isinstance(v,int) and not isinstance(v,bool)})
            models.append(dict(d=d,epsilon=str(e),**counts))
            saved.append(make_edge(d,e,0,[],[i%2 for i in range(d-1)]))
    rng=random.Random(318)
    large=[]
    for d in (8,16,32,64):
        e=F(1,4);selected=[];Dset=set()
        for t in range(16):
            k=t%d;prefix=[rng.randrange(2) for _ in range(k)];tail=[rng.randrange(2) for _ in range(d-k-1)]
            c=make_edge(d,e,k,prefix,tail);res=audit_edge(c);selected.append(c);Dset.add(tuple(c['normalized_direction']))
        saved.extend(selected)
        large.append(dict(d=d,original_facets=2*d,checked_edges=len(selected),
                          sampled_distinct_directions=len(Dset),written_all_d_direction_formula=2**d-1,
                          full_vertices_or_directions_enumerated=False))
    completions=[]
    polygons=[hull2([vertex(b,F(1,4)) for b in product((0,1),repeat=2)]),
              hull2([(F(0),F(0)),(F(2),F(0)),(F(0),F(1))])]
    for _ in range(12):
        P=hull2([tuple(F(rng.randrange(-6,7)) for _ in range(2)) for _ in range(8)])
        if len(P)>=3:polygons.append(P)
    for P in polygons:
        bydir={}
        for p,q in zip(P,P[1:]+P[:1]):
            e=sub(q,p);D=direction(e);i=next(i for i,x in enumerate(e) if x)
            bydir[D]=max(bydir.get(D,F(0)),abs(e[i]))
        minimal=[scale(c,D) for D,c in bydir.items()]
        pair=[sub(q,p) for p in P for q in P]
        for kind,G in [('edge-direction',minimal),('all-pairs',pair)]:
            Q,Z=complete_by_erosion(P,G)
            c=dict(kind=kind,P=P,Q=Q,Z=Z,generators=G,claimed_original_directions=len(bydir))
            audit_completion(c);completions.append(c)
    originals=(make_edge,vertex,complete_by_erosion)
    def forbidden(*a,**k):raise AssertionError('construction during audit')
    try:
        globals()['make_edge']=forbidden;globals()['vertex']=forbidden;globals()['complete_by_erosion']=forbidden
        for c in saved:audit_edge(c)
        for c in completions:audit_completion(c)
    finally:globals()['make_edge'],globals()['vertex'],globals()['complete_by_erosion']=originals
    negative=[]
    b=next(c for c in saved if c['d']==4)
    edits=[('stationary',lambda c:c.update(target=c['source'])),
           ('infeasible',lambda c:c['source'].__setitem__(0,'100')),
           ('false direction',lambda c:c['normalized_direction'].__setitem__(1,'123')),
           ('wrong tail',lambda c:c['tail'].__setitem__(0,1-c['tail'][0])),
           ('zero epsilon',lambda c:c.update(epsilon='0')),
           ('collapsed width',lambda c:c.update(epsilon='1/2'))]
    for name,edit in edits:
        c=deepcopy(b);edit(c)
        try:audit_edge(c)
        except (AssertionError,ValueError,IndexError,ZeroDivisionError):negative.append(name)
        else:raise AssertionError('forgery accepted '+name)
    c=deepcopy(completions[0]);c['Q']=[(F(0),F(0))]
    try:audit_completion(c)
    except ValueError:negative.append('false summand equality')
    else:raise AssertionError('bad decomposition accepted')
    stats=[audit_completion(c) for c in completions]
    report=dict(status='PASS',Lean_verification=False,small_models=models,totals=dict(totals),large=large,
                actual_2d_completions=stats,completion_models=len(completions),saved_edge_audits=len(saved),
                construction_disabled=True,rejected=negative,
                scope='General direction-inheritance Lean candidate is uncompiled. All-dimensional deformed-cube application is a written proof, with exact finite tests, not a second Lean theorem.')
    return report,dict(edges=saved,completions=completions)

def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encode(v) for v in x]
    return x

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    report,data=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',data)]:
        (a.out/name).write_text(json.dumps(encode(obj),sort_keys=True,indent=2)+'\n')
    print(json.dumps({'totals':report['totals'],'completions':len(report['actual_2d_completions']),
      'saved_edges':report['saved_edge_audits'],'rejected':report['rejected']},sort_keys=True),flush=True)
if __name__=='__main__':main()
