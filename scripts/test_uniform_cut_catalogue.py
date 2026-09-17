#!/usr/bin/env python3
"""Exact recipe enumeration, independent H vertices, and support recovery.
This is supporting rational arithmetic, not Lean verification or extraction.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]

def solve(rows, rhs, n):
    a = [[Q(x) for x in row]+[Q(b)] for row,b in zip(rows,rhs)]
    piv=[]; r=0
    for j in range(n):
        i=next((i for i in range(r,len(a)) if a[i][j]),None)
        if i is None: continue
        a[r],a[i]=a[i],a[r]; scale=a[r][j]; a[r]=[x/scale for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][j]:
                q=a[i][j]; a[i]=[x-q*y for x,y in zip(a[i],a[r])]
        piv.append(j);r+=1
    if any(not any(row[:n]) and row[n] for row in a): return None, len(piv)
    x=[Q(0)]*n
    for row,j in zip(a,piv):x[j]=row[n]
    return tuple(x),len(piv)

def dot(a,x): return sum((p*q for p,q in zip(a,x)),Q(0))

def vertices(d,C,b):
    E=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
    A=[tuple(-x for x in a) for a in E]+E+list(C);rhs=[Q(0)]*d+[Q(1)]*d+list(b)
    V=set();systems=0
    for I in combinations(range(len(A)),d):
        systems+=1;x,rank=solve([A[i] for i in I],[rhs[i] for i in I],d)
        if x is not None and rank==d and all(dot(a,x)<=z for a,z in zip(A,rhs)):V.add(x)
    return sorted(V),systems

def catalogue(d,m,Omega,L,b):
    K=set();systems=codes=consistent=rankdef=0
    for n in range(min(d+1,m+1)+1):
        for mask in product([False,True],repeat=m):
            I=[j for j in range(m) if mask[j]]
            for zs in product(Omega,repeat=n):
                u,rank=solve([[Q(1)]*n]+[[z[j] for z in zs] for j in I],
                              [Q(1)]+[b[j] for j in I],n)
                systems+=1;consistent+=u is not None
                rankdef+=u is not None and rank<n
                if u is None:u=(Q(0),)*n
                for ls in product(L,repeat=n):
                    K.add(dot(u,ls));codes+=1
    expected=2**m*sum((len(Omega)*len(L))**n for n in range(min(d+1,m+1)+1))
    assert codes==expected and len(K)<=expected
    return K,dict(recipe_systems=systems,recipes=codes,consistent_systems=consistent,
                  rank_deficient_consistent=rankdef,catalogue_size=len(K),bound=expected)

def select(S,x):
    d=len(x)
    for n in range(1,min(d+1,len(S))+1):
        for I in combinations(range(len(S)),n):
            vs=[S[i] for i in I]
            w,r=solve([[1]*n]+[[v[j] for v in vs] for j in range(d)],[1]+list(x),n)
            if w is not None and r==n and all(z>0 for z in w):return vs,w
    raise AssertionError('positive independent support not found')

def main():
    cases=[(2,[],[],False),(2,[[1,1]],[Q(3,2)],False),
           (2,[[1,2],[-1,1]],[Q(7,5),Q(1,4)],False),
           (2,[[1,1]],[Q(3,2)],True),
           (3,[[1,1,1]],[Q(7,5)],False),
           (3,[[1,1,0],[0,1,1]],[1,1],False),
           (3,[[1,2,3],[-1,-2,-3]],[Q(13,4),-Q(13,4)],False)]
    records=[];fixtures=[]
    for d,C,b,extra in cases:
        C=tuple(tuple(map(Q,a)) for a in C);b=tuple(map(Q,b));m=len(C)
        S=list(product([Q(0),Q(1)],repeat=d))
        if extra:S.append((Q(1,2),)*d)
        Omega=tuple(sorted({tuple(dot(a,x) for a in C) for x in S}))
        L=tuple(sorted({z for x in S for z in x}))
        K,record=catalogue(d,m,Omega,L,b);V,systems=vertices(d,C,b)
        for x in V:
            vs,w=select(S,x);I=[j for j in range(m) if dot(C[j],x)==b[j]]
            zs=[tuple(dot(a,v) for a in C) for v in vs]
            decoded,rank=solve([[1]*len(vs)]+[[z[j] for z in zs] for j in I],
                               [1]+[b[j] for j in I],len(vs))
            assert rank==len(vs) and decoded==w
            assert len(vs)<=min(d+1,len(I)+1)
            assert all(z in K for z in x)
            assert all(dot(decoded,[v[j] for v in vs])==x[j] for j in range(d))
        record.update(dimension=d,cuts=m,base_generators=len(S),image_count=len(Omega),
            base_levels=len(L),cut_vertices=len(V),H_systems=systems,
            coordinate_memberships=d*len(V),positive_recipe_recoveries=len(V))
        records.append(record)
        fixtures.append(dict(C=C,b=b,S=S,Omega=Omega,L=L,K=sorted(K),vertices=V))
    # Invalid/incomplete image covers really can lose a newly created level.
    bad,_=catalogue(1,1,((Q(0),),),(Q(0),Q(1)),(Q(1,2),))
    assert Q(1,2) not in bad
    # Without extremality, no single finite set could cover the continuum.
    K,_=catalogue(1,0,((),),(Q(0),Q(1)),())
    assert Q(1,2) not in K
    # The dummy zero recipe handles inconsistent systems; it is not a vertex.
    z,r=solve([[]],[1],0);assert z is None
    # Empty generating levels need no coordinates in dimension zero.
    K,zero=catalogue(0,0,((),),(),());assert K=={Q(0)} and zero['bound']==1
    totals={key:sum(r[key] for r in records) for key in ['recipe_systems','recipes','consistent_systems',
        'rank_deficient_consistent','cut_vertices','H_systems','coordinate_memberships','positive_recipe_recoveries']}
    packet=ROOT/'research/publication_packets/cut_uniform_coordinate_catalogue'
    report=dict(status='PASS',scope='Exact rational support/recipe/H tests, not Lean or extracted code.',
        cases=records,totals=totals,controls=['incomplete image cover loses half level',
        'nonextreme point absent from vertex catalogue','empty recipe inconsistent','zero dimensional case'],
        solution_sha256=hashlib.sha256((packet/'solution.lean').read_bytes()).hexdigest(),
        test_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    def ser(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,dict):return {k:ser(v) for k,v in x.items()}
        if isinstance(x,(tuple,list)):return [ser(v) for v in x]
        return x
    (ROOT/'research/UNIFORM_CUT_CATALOGUE_TEST.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'fixtures').mkdir(exist_ok=True)
    (ROOT/'fixtures/uniform_cut_catalogue.json').write_text(json.dumps(ser(fixtures),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
