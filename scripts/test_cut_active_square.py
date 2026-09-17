#!/usr/bin/env python3
"""Exact supporting checks for selected active equations. Not Lean extraction."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import random, json, hashlib, argparse


def rank(rows, n):
    a=[list(map(F,row)) for row in rows]; k=0
    for j in range(n):
        z=next((i for i in range(k,len(a)) if a[i][j]),None)
        if z is None:continue
        a[k],a[z]=a[z],a[k];p=a[k][j];a[k]=[v/p for v in a[k]]
        for i in range(len(a)):
            if i!=k:
                q=a[i][j];a[i]=[u-q*v for u,v in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def inverse(a):
    n=len(a);t=[list(map(F,r))+[F(i==j) for j in range(n)] for i,r in enumerate(a)]
    for j in range(n):
        p=next((i for i in range(j,n) if t[i][j]),None)
        if p is None:raise ValueError('singular square')
        t[j],t[p]=t[p],t[j];z=t[j][j];t[j]=[v/z for v in t[j]]
        for i in range(n):
            if i!=j:
                z=t[i][j];t[i]=[u-z*v for u,v in zip(t[i],t[j])]
    return [r[n:] for r in t]


def select(rows,n):
    if n<1 or rank([[F(1)]*n]+rows,n)!=n:raise ValueError('no independent augmented support')
    a=[[F(1)]*n];ids=[]
    for i,r in enumerate(rows):
        if rank(a+[r],n)>len(a):a.append(r);ids.append(i)
    assert len(ids)+1==n
    return ids,inverse(a)


def verify(rows,n,ids,inv):
    assert len(ids)+1==n and len(set(ids))==len(ids) and all(0<=i<len(rows) for i in ids)
    a=[[F(1)]*n]+[rows[i] for i in ids]
    assert len(inv)==n and all(len(r)==n for r in inv)
    for i in range(n):
        for j in range(n):
            assert sum((a[i][k]*inv[k][j] for k in range(n)),F(0))==int(i==j)
    return a


def run():
    rng=random.Random(294);records=[];stats=dict(abstract_cases=0,square_identities=0,signed_recoveries=0,
      original_cut_vertices=0,original_active_rows=0,proper_row_subsets_enumerated=0,negative_controls=0)
    for n in range(1,9):
        for trial in range(12):
            rows=[]
            # Coordinate rows on simplex supports give known full augmented rank.
            for j in range(1,n):rows.append([F(i==j) for i in range(n)])
            for _ in range(n+2):
                rows.append([F(rng.randint(-6,6),rng.randint(1,5)) for i in range(n)])
            rng.shuffle(rows);ids,inv=select(rows,n);a=verify(rows,n,ids,inv)
            stats['abstract_cases']+=1;stats['square_identities']+=n*n
            for _ in range(3):
                target=[F(rng.randint(-15,15),rng.randint(1,8)) for i in range(n)]
                u=[sum((r[j]*target[j] for j in range(n)),F(0)) for r in inv]
                assert [sum((x*y for x,y in zip(r,u)),F(0)) for r in a]==target
                stats['signed_recoveries']+=1
            if n<=4:
                good=[J for J in combinations(range(len(rows)),n-1) if rank([[F(1)]*n]+[rows[i] for i in J],n)==n]
                assert tuple(ids) in good
                stats['proper_row_subsets_enumerated']+=len(list(combinations(range(len(rows)),n-1)))
            if trial==0:records.append(dict(n=n,selected=ids,active_rows=len(rows)))
    # Actual extreme points in simplex intersected with original coordinate caps.
    # Positive support vertices may violate the new cuts; Q is not a singleton.
    geometric=[]
    for d in [0,1,2,3,4,8,16]:
        n=d+1;V=[[F(i==j+1) for j in range(d)] for i in range(n)]
        x=[F(1,2*n)]*d;w=[1-sum(x,F(0))]+x
        C=[[F(j==i) for j in range(d)] for i in range(d)]
        C += [[F(2)*(F(j==i)) for j in range(d)] for i in range(d)]
        if d:C += [[F(1)]*d]
        b=[sum((a*z for a,z in zip(r,x)),F(0)) for r in C]
        rows=[[sum((a*z for a,z in zip(r,p)),F(0)) for p in V] for r in C]
        ids,inv=select(rows,n);a=verify(rows,n,ids,inv)
        recovered=[sum((r[j]*([F(1)]+[b[i] for i in ids])[j] for j in range(n)),F(0)) for r in inv]
        assert recovered==w and all(t>0 for t in w)
        assert [sum((w[i]*V[i][j] for i in range(n)),F(0)) for j in range(d)]==x
        # Active original normals contain an identity, so this feasible point is extreme.
        assert rank(C,d)==d if d else C==[]
        assert sum(x,F(0))<=1 and all(t>=0 for t in x)
        stats['original_cut_vertices']+=1;stats['original_active_rows']+=len(C)
        geometric.append(dict(dimension=d,support=n,active_rows=len(C),selected=ids,
             basis_points_outside_cut=sum(any(sum((a*z for a,z in zip(r,p)),F(0))>rhs for r,rhs in zip(C,b)) for p in V)))
    # False column-independence, loss of mass, missing selected row, false inverse.
    try:select([[F(1),F(1),F(1)]],3)
    except ValueError:stats['negative_controls']+=1
    else:raise AssertionError('rank deficiency accepted')
    assert rank([[F(0),F(1)]],2)<2;stats['negative_controls']+=1
    rows=[[F(0),F(1),F(0)],[F(0),F(0),F(1)]];ids,inv=select(rows,3)
    for badids,badinv in [(ids[:-1],inv),(ids,[[F(0)]*3]*3),([ids[0],ids[0]],inv)]:
        try:verify(rows,3,badids,badinv)
        except AssertionError:stats['negative_controls']+=1
        else:raise AssertionError('forgery accepted')
    # Recheck stored inverses without invoking selection/elimination.
    saved=[]
    for n in [1,2,5,17]:
        rows=[[F(i==j) for i in range(n)] for j in range(1,n)]
        ids,inv=select(rows,n);saved.append((rows,n,ids,inv))
    oldrank=globals()['rank'];oldselect=globals()['select'];oldinv=globals()['inverse']
    def forbidden(*a,**k):raise AssertionError('producer called during audit')
    try:
        globals()['rank']=globals()['select']=globals()['inverse']=forbidden
        for args in saved:verify(*args)
    finally:globals()['rank'],globals()['select'],globals()['inverse']=oldrank,oldselect,oldinv
    return dict(status='PASS',seed=294,counts=stats,examples=records,geometric_cases=geometric,
      producer_disabled_saved_audits=len(saved),
      scope='Exact supporting arithmetic and explicit simplex-cut models; not Lean verification or a polynomial total catalogue bound.')


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps(r['counts'],sort_keys=True))
if __name__=='__main__':main()
