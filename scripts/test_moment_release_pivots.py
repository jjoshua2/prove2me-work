#!/usr/bin/env python3
"""Exact rational tests for first-blocking original moment-edge construction.
The all-real claim belongs to the separate Lean source, not these finite tests.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random
import sympy as sp


def dump(p, x):
    def encode(z):
        if isinstance(z,Q): return str(z)
        if isinstance(z,dict): return {k:encode(v) for k,v in z.items()}
        if isinstance(z,(tuple,list)): return [encode(v) for v in z]
        return z
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(encode(x),sort_keys=True,indent=2)+'\n')


def rows(a,d):
    m=len(a)
    means=[sum(t**j for t in a)/m for j in range(1,d+1)]
    return tuple(tuple(t**j-means[j-1] for j in range(1,d+1)) for t in a)


def dot(a,x): return sum((u*v for u,v in zip(a,x)),Q(0))


def inverse(A):
    d=len(A); M=[list(a)+[Q(i==j) for j in range(d)] for i,a in enumerate(A)]
    for j in range(d):
        p=next((i for i in range(j,d) if M[i][j]),None)
        if p is None: return None
        M[j],M[p]=M[p],M[j]; z=M[j][j]; M[j]=[v/z for v in M[j]]
        for i in range(d):
            if i!=j:
                z=M[i][j]
                if z:M[i]=[x-z*y for x,y in zip(M[i],M[j])]
    return tuple(tuple(a[d:]) for a in M)


def make(a,d,u,p):
    A=rows(a,d); vals=[dot(r,u) for r in A]
    if any(z>1 for z in vals):raise ValueError('infeasible source')
    I=[i for i,z in enumerate(vals) if z==1]
    if len(I)!=d or p not in I:raise ValueError('not a tight row at a vertex')
    R=inverse([A[i] for i in I])
    if R is None:raise ValueError('dependent source rows')
    col=I.index(p);w=tuple(-r[col] for r in R);slopes=[dot(r,w) for r in A]
    pos=[i for i,c in enumerate(slopes) if c>0]
    if not pos:raise ValueError('no finite blocker')
    ratios={i:(1-vals[i])/slopes[i] for i in pos}
    t=min(ratios.values()); block=[i for i in pos if ratios[i]==t]
    if len(block)!=1:raise ValueError('not exactly one new row')
    q=block[0];v=tuple(x+t*z for x,z in zip(u,w))
    return dict(a=a,dimension=d,u=u,p=p,I=I,inverse=R,w=w,t=t,q=q,v=v)


def verify(c):
    d=c['dimension'];a=tuple(map(Q,c['a']));m=len(a)
    if not 0<d<m or len(set(a))!=m:raise ValueError('invalid dimension/nodes')
    A=rows(a,d);u=tuple(map(Q,c['u']));v=tuple(map(Q,c['v']));w=tuple(map(Q,c['w']))
    if len(u)!=d or len(v)!=d or len(w)!=d:raise ValueError('dimensions')
    I=c['I'];R=[list(map(Q,r)) for r in c['inverse']];p,q=c['p'],c['q'];t=Q(c['t'])
    if any(len(r)!=d for r in R) or len(R)!=d:raise ValueError('inverse dimensions')
    vals=[dot(r,u) for r in A]; slopes=[dot(r,w) for r in A];ends=[dot(r,v) for r in A]
    if any(z>1 for z in vals) or I!=[i for i,z in enumerate(vals) if z==1] or len(I)!=d or p not in I:raise ValueError('source vertex')
    if any(sum(A[I[i]][k]*R[k][j] for k in range(d))!=int(i==j) for i in range(d) for j in range(d)):raise ValueError('source inverse')
    if slopes[p]!=-1 or any(slopes[i]!=0 for i in I if i!=p):raise ValueError('release direction')
    if q in I or not 0<t or slopes[q]<=0 or t!=(1-vals[q])/slopes[q]:raise ValueError('false blocker')
    if any(t>(1-vals[i])/c for i,c in enumerate(slopes) if c>0):raise ValueError('not first blocker')
    if tuple(x+t*z for x,z in zip(u,w))!=v or any(z>1 for z in ends):raise ValueError('infeasible endpoint')
    J=[i for i,z in enumerate(ends) if z==1]
    if set(J)!=(set(I)-{p})|{q} or u==v:raise ValueError('not a single exchange')
    # The retained source rows have a right inverse by deleting one column of R.
    keep=[j for j in range(d) if I[j]!=p]
    if any(sum(A[I[i]][k]*R[k][j] for k in range(d))!=int(i==j) for i in keep for j in keep):raise ValueError('common row rank')
    for s in (Q(0),t/3,t/2,t,t*2):
        feasible=all(vals[i]+s*slopes[i]<=1 for i in range(m))
        if feasible!=(s<=t):raise ValueError('ray interval')
        if 0<s<t and {i for i in range(m) if vals[i]+s*slopes[i]==1}!=set(I)-{p}:raise ValueError('interior tight set')
    return dict(status='PASS',dimension=d,original_rows=m,leaving=p,entering=q,
                source_inverse_identities=d*d,common_original_rows=d-1)


def seed(a,d):
    p=[Q(1)]
    for t in sorted(a)[:d]:
        q=[Q(0)]*(len(p)+1)
        for j,c in enumerate(p):q[j]-=t*c;q[j+1]+=c
        p=q
    values=[sum(c*t**j for j,c in enumerate(p)) for t in a]
    h=sum(values)/len(a)
    assert h>0 and min(values)>=0
    return tuple(-p[j]/h for j in range(1,d+1))


def run(out):
    rng=random.Random(298)
    totals=dict(models=0,bases=0,vertices=0,pivots=0,objective_checks=0,inverse_identities=0)
    models=[];saved=[]
    for d,m in [(1,3),(2,5),(3,6),(4,7),(4,8),(5,8)]:
        a=[Q(x,5) for x in sorted(rng.sample(range(-30,50),m))];rng.shuffle(a)
        A=rows(a,d);V=set();bases=0;invalid=0
        # Independent SymPy active-system enumeration, no production inverse.
        for I in combinations(range(m),d):
            bases+=1;B=sp.Matrix([A[i] for i in I])
            if not B.det(): continue
            u=tuple(Q(z) for z in B.inv()*sp.ones(d,1))
            if all(dot(r,u)<=1 for r in A):V.add(u)
            else:invalid+=1
        pivots=0
        for u in sorted(V):
            for p in [i for i,r in enumerate(A) if dot(r,u)==1]:
                c=make(a,d,u,p);v=tuple(c['v']);res=verify(c);assert v in V
                C=set(c['I'])-{p}
                common=sp.Matrix([A[i] for i in sorted(C)]) if C else sp.zeros(0,d)
                assert common.rank()==d-1
                maxverts={z for z in V if sum(dot(A[i],z) for i in C)==len(C)}
                assert maxverts=={u,v}
                totals['objective_checks']+=len(V);totals['inverse_identities']+=res['source_inverse_identities']
                pivots+=1
                if not any(s['dimension']==d and len(s['a'])==m for s in saved):saved.append(c)
        models.append(dict(dimension=d,rows=m,bases=bases,vertices=len(V),pivots=pivots,infeasible_square_solutions=invalid))
        for key,val in [('models',1),('bases',bases),('vertices',len(V)),('pivots',pivots)]:totals[key]+=val
    large=[]
    for d in (8,16,32):
        a=[Q(i) for i in range(d+5)];u=seed(a,d);A=rows(a,d);I=[i for i,r in enumerate(A) if dot(r,u)==1]
        for p in (I[0],I[len(I)//2],I[-1]):
            c=make(a,d,u,p);res=verify(c);saved.append(c);large.append(res)
    # Malformed records: no geometric claim is inferred from rejections alone.
    rejected=[];base=next(c for c in saved if c['dimension']==3)
    mutations=[('zero step',lambda c:c.update(t=Q(0))),('wrong leaving',lambda c:c.update(p=c['q'])),
      ('old row enters',lambda c:c.update(q=c['p'])),('wrong direction',lambda c:c.update(w=[Q(0)]*3)),
      ('bad inverse',lambda c:c['inverse'].__setitem__(0,[Q(0)]*3)),('overshoot',lambda c:c.update(t=2*c['t'])),
      ('wrong endpoint',lambda c:c.update(v=c['u'])),('omitted active',lambda c:c['I'].pop()),
      ('repeated nodes',lambda c:c['a'].__setitem__(0,c['a'][1]))]
    for name,mut in mutations:
        c=deepcopy(base);c['inverse']=[list(r) for r in c['inverse']];c['a']=list(c['a']);mut(c)
        try:verify(c)
        except (ValueError,IndexError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError(name)
    oldmake,oldinv=globals()['make'],globals()['inverse']
    def fail(*a,**k):raise AssertionError('producer in replay')
    try:
        globals()['make']=globals()['inverse']=fail
        for c in saved:verify(c)
    finally:globals()['make'],globals()['inverse']=oldmake,oldinv
    dump(out/'fixtures.json',saved)
    return dict(status='PASS',counts=totals,models=models,large_pivots=large,rejected=rejected,
       saved_records=len(saved),discovery_disabled_replay=True,
       scope='Exact supporting rational tests; no local Lean claim or uniform diameter bound.')


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r=run(a.out);r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    dump(a.out/'exact-tests.json',r);print(json.dumps(r['counts'],sort_keys=True))
if __name__=='__main__':main()
