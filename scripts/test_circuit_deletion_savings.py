#!/usr/bin/env python3
"""Exact-rational regression for circuit-carrier deletion savings.

Uses only the Python standard library. Finite tests are not a universal proof.
The Lean file supplies the universal one-carrier identity. A separate Gray-walk
negative control rejects treating a per-carrier saving as a globally consumable
credit, even for simple walks in irredundant parents with distinct edge carriers.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import argparse, hashlib, json, random


def dot(a, b):
    return sum((u*v for u,v in zip(a,b)), Q(0))


def rref(rows, d):
    a=[list(map(Q,row)) for row in rows]
    pivots=[]; k=0
    for j in range(d):
        p=next((p for p in range(k,len(a)) if a[p][j]),None)
        if p is None: continue
        a[k],a[p]=a[p],a[k]
        c=a[k][j]; a[k]=[v/c for v in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                c=a[i][j]; a[i]=[v-c*w for v,w in zip(a[i],a[k])]
        pivots.append(j); k+=1
        if k==len(a): break
    return a,pivots


def rank(rows,d):
    return len(rref(rows,d)[1])


def kernel_basis(rows,d):
    a,pivots=rref(rows,d); out=[]
    for j in range(d):
        if j in pivots: continue
        v=[Q(0)]*d; v[j]=Q(1)
        for k,p in enumerate(pivots): v[p]=-a[k][j]
        out.append(v)
    return out


def cube_rows(d):
    a=[]; b=[]
    for j in range(d):
        for sign,rhs in [(1,1),(-1,0)]:
            v=[Q(0)]*d; v[j]=Q(sign); a.append(v); b.append(Q(rhs))
    return a,b


def append_valid_redundant(a,b,v):
    # The support function of [0,1]^d is the sum of positive coefficients.
    v=list(map(Q,v)); a.append(v); b.append(sum((max(q,Q(0)) for q in v),Q(0))+1)


def inspect(a,b,x,y,F=None):
    d=len(x); n=len(a); g=[t-s for s,t in zip(x,y)]
    assert any(g) and all(dot(row,x)<=rhs and dot(row,y)<=rhs for row,rhs in zip(a,b))
    assert rank(a,d)==d
    C={i for i in range(n) if any(a[i]) and dot(a[i],x)==b[i]==dot(a[i],y)}
    W=kernel_basis([a[i] for i in sorted(C)],d); h=len(W)
    assert h>0
    ar=[[dot(a[i],w) for w in W] for i in range(n)]
    E={i for i in range(n) if any(ar[i])}
    Z={i for i in range(n) if any(a[i]) and dot(a[i],g)==0}
    assert rank([a[i] for i in sorted(Z)],d)==d-1, 'not an ambient row circuit'
    assert rank([ar[i] for i in sorted(Z&E)],h)==h-1
    if F is None: F=set(range(2*d))&E
    assert F<=E and len(F)>=h
    selected_rank=rank([ar[i] for i in sorted(F&Z)],h)
    delta=h-1-selected_rank
    deleted=E-F; q=len(deleted&Z); s=len(deleted-Z)
    kappa=n+h-len(E)-d; tau=q-delta; e=len(F)-h; ambient=n-d
    assert min(delta,kappa,s,tau,e)>=0
    assert delta<=q
    assert e+delta+kappa+s+tau==ambient
    assert e+delta+s<=ambient
    assert (e+delta==ambient)==(kappa==s==tau==0)
    return dict(d=d,n=n,h=h,F=len(F),E=len(E),selected_rank=selected_rank,
                e=e,delta=delta,kappa=kappa,s=s,tau=tau,ambient=ambient), E


def verify_genuine_facets(a,b,inside,witnesses):
    """Strict feasible point plus a point tight on each row and no other row."""
    assert len(witnesses)==len(a)
    assert all(dot(row,inside)<rhs for row,rhs in zip(a,b))
    for j,w in enumerate(witnesses):
        assert any(a[j])
        assert dot(a[j],w)==b[j]
        assert all(dot(row,w)<rhs for i,(row,rhs) in enumerate(zip(a,b)) if i!=j)
    return len(witnesses)


def genuine_wedge_completion(d):
    # 0<=x_i<=1, t>=0, with x_0<=1 replaced by x_0+t<=1;
    # caps x_i-x_0+2*t<=5/2, i>0. Floor t=0 is the unchanged d-cube.
    a,b=cube_rows(d)
    a=[row+[Q(0)] for row in a]; a[0][-1]=Q(1)
    a.append([Q(0)]*d+[Q(-1)]); b.append(Q(0))
    for i in range(1,d):
        row=[Q(0)]*(d+1); row[0]=-1; row[i]=1; row[-1]=2
        a.append(row); b.append(Q(5,2))
    inside=[Q(1,2)]*d+[Q(1,8)]
    witnesses=[]
    for i in range(d):
        w=inside.copy(); w[i]=1
        if i==0: w[0]=Q(3,4); w[-1]=Q(1,4)
        witnesses.append(w)
        w=inside.copy(); w[i]=0; witnesses.append(w)
    witnesses.append([Q(1,2)]*d+[Q(0)])
    for i in range(1,d):
        w=[Q(1,2)]*d+[Q(17,20)]; w[0]=Q(1,10); w[i]=Q(9,10)
        witnesses.append(w)
    # d-2 additional wedges over the roof make the parent exactly balanced:
    # ambient dimension 2*d-1 and 4*d-2 genuine facets. The protected floor,
    # restricted rows, and all three savings remain unchanged.
    extra=d-2
    if extra>0:
        eps=Q(1,100*extra)
        a=[row+[Q(0)]*extra for row in a]
        for j in range(extra):a[0][d+1+j]=Q(1)
        witnesses=[w+[eps]*extra for w in witnesses]
        witnesses[0][d]-=extra*eps
        inside=inside+[eps]*extra
        for j in range(extra):
            row=[Q(0)]*len(inside); row[d+1+j]=-1
            a.append(row);b.append(Q(0))
            w=inside.copy();w[d+1+j]=0;witnesses.append(w)
    facet_count=verify_genuine_facets(a,b,inside,witnesses)
    return a,b,facet_count


def genuine_truncated_cube(d):
    # Ambient dimension D=d+1. The one corner cut is strict on the entire floor.
    D=d+1; a,b=cube_rows(D)
    a.append([Q(1)]*D); b.append(Q(2*D-1,2))
    inside=[Q(1,4)]*D; witnesses=[]
    for i in range(D):
        for value in [1,0]:
            w=inside.copy(); w[i]=Q(value); witnesses.append(w)
    witnesses.append([Q(2*D-1,2*D)]*D)
    facet_count=verify_genuine_facets(a,b,inside,witnesses)
    return a,b,facet_count


def run():
    rng=random.Random(20260911)
    count=0; source_nonvertices=0; target_nonvertices=0
    positive={k:0 for k in ['delta','kappa','s','tau']}
    samples=[]
    # Redundant rows create arbitrary ambient circuits while keeping cube geometry.
    for d in range(1,9):
        for trial in range(24):
            g=[Q(rng.choice([-2,-1,0,1,2])) for _ in range(d)]
            if not any(g):g[0]=Q(1)
            x=[Q(rng.choice([1,2,3]),4) if g[i] else Q(rng.choice([0,1,2,4]),4)
               for i in range(d)]
            if trial%4==0:
                x=[Q(0) if g[i]>=0 else Q(1) for i in range(d)]
            alpha=min([(1-x[i])/g[i] if g[i]>0 else x[i]/(-g[i])
                       for i in range(d) if g[i]])
            assert alpha>0
            y=[x[i]+alpha*g[i] for i in range(d)]
            a,b=cube_rows(d)
            # Basis of g-perp; all additions are strictly redundant on the cube.
            for v in kernel_basis([g],d):append_valid_redundant(a,b,v)
            for _ in range(trial%4):
                append_valid_redundant(a,b,[rng.choice([-2,-1,0,1,2]) for _ in range(d)])
            if trial%3==0 and d>1:
                v=kernel_basis([g],d)[0]; append_valid_redundant(a,b,v)
            if trial%5==0:append_valid_redundant(a,b,[0]*d)
            # Original cube inequalities give an equivalent minimum carrier model.
            rec,E=inspect(a,b,x,y)
            count+=1; samples.append(rec)
            source_nonvertices+=int(any(v not in (0,1) for v in x))
            target_nonvertices+=int(any(v not in (0,1) for v in y))
            for key in positive:positive[key]+=int(rec[key]>0)
            # The universal selected-row lemma also covers non-equivalent F.
            for _ in range(3):
                k=rng.randrange(rec['h'],len(E)+1)
                F=set(rng.sample(sorted(E),k))
                r,_=inspect(a,b,x,y,F)
                count+=1; samples.append(r)
                for key in positive:positive[key]+=int(r[key]>0)
    # Reject identities that omit one of the three real savings (or alter defect).
    mutation_rejected={
       'omit_disappearance_surplus':any(r['kappa'] for r in samples),
       'omit_nonneutral_savings':any(r['s'] for r in samples),
       'omit_neutral_redundancy':any(r['tau'] for r in samples),
       'negate_defect_term':any(r['delta'] for r in samples),
    }
    assert all(mutation_rejected.values())
    # High intrinsic excess with ZERO savings, now with every parent row genuine.
    zero_savings=[]; facet_witness_count=0
    for d in range(4,13):
        a,b,fc=genuine_wedge_completion(d); facet_witness_count+=fc
        x=[Q(0)]*len(a[0]); y=[Q(1)]*d+[Q(0)]*(len(a[0])-d)
        rec,_=inspect(a,b,x,y,set(range(2*d)))
        assert rec['e']==d and rec['delta']==d-1
        assert rec['kappa']==rec['s']==rec['tau']==0
        rec['all_parent_rows_genuine']=True; rec['facet_witnesses']=fc
        rec['exactly_balanced_parent']=(len(a)==2*len(a[0]))
        assert rec['exactly_balanced_parent']
        rec['floor_dimension']=d
        zero_savings.append(rec)
    # A LINEAR-length simple Gray prefix repeatedly spends the same facet saving.
    # Every parent row is genuine; the extra facet becomes redundant on each edge.
    gray=[]
    for d in range(3,9):
        a,b,fc=genuine_truncated_cube(d); facet_witness_count+=fc
        L=2*d+1
        points=[tuple(Q(((k^(k>>1))>>j)&1) for j in range(d))+(Q(0),)
                for k in range(L+1)]
        assert len(set(points))==len(points)
        edges=set(); total=0
        for x,y in zip(points,points[1:]):
            assert sum(u!=v for u,v in zip(x,y))==1
            edges.add(tuple(sorted((x,y))))
            rec,_=inspect(a,b,x,y)
            assert (rec['h'],rec['e'],rec['delta'],rec['s'])==(1,1,0,1)
            total+=rec['s']
        assert len(edges)==L
        assert total>len(a)-(d+1)
        assert L<=17*len(a)**3
        gray.append(dict(d=d+1,n=len(a),walk_length=L,
                         distinct_vertices=len(points),distinct_carriers=len(edges),
                         total_nonneutral_savings=total,ambient_budget=len(a)-(d+1),
                         all_parent_rows_genuine=True,facet_witnesses=fc))
    return dict(seed=20260911,selected_row_checks=count,
                minimum_cube_carrier_checks=192,nonvertex_sources=source_nonvertices,
                nonvertex_targets=target_nonvertices,positive_term_witnesses=positive,
                mutation_controls_rejected=mutation_rejected,
                genuine_facet_witnesses=facet_witness_count,
                high_excess_zero_savings=zero_savings,
                simple_walk_nontelescoping_controls=gray,
                scope='Exact finite regressions; universal identity is separately Lean-checked.')


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    result=run();text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text)
