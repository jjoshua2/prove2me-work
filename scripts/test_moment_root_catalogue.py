#!/usr/bin/env python3
"""Exact supporting tests for the separate all-real moment-root Lean theorem.

Construct candidates by polynomial arithmetic; compare every small candidate
with an independent exact original-row square solve. No solver in the producer.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, math, random


def polynomial(roots):
    p=[Q(1)]
    for a in roots:
        out=[Q(0)]*(len(p)+1)
        for j,c in enumerate(p):
            out[j]-=a*c;out[j+1]+=c
        p=out
    return p


def evaluate(p,x):
    value=Q(0)
    for c in reversed(p):value=value*x+c
    return value


def row_matrix(a,d):
    means=[sum(t**j for t in a)/len(a) for j in range(1,d+1)]
    return [tuple(t**j-means[j-1] for j in range(1,d+1)) for t in a]


def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))


def square_solve(A,b):
    # Independent rational Gaussian elimination, not polynomial interpolation.
    n=len(b)
    M=[list(row)+[rhs] for row,rhs in zip(A,b)]
    pivot=0
    for j in range(n):
        i=next((i for i in range(pivot,n) if M[i][j]),None)
        if i is None:continue
        M[pivot],M[i]=M[i],M[pivot]
        z=M[pivot][j];M[pivot]=[x/z for x in M[pivot]]
        for i in range(n):
            if i!=pivot:
                z=M[i][j];M[i]=[x-z*y for x,y in zip(M[i],M[pivot])]
        pivot+=1
    inconsistent=any(all(x==0 for x in row[:-1]) and row[-1]!=0 for row in M)
    if pivot<n:return None,pivot,inconsistent
    return tuple(row[-1] for row in M),pivot,False


def candidate(a,d,S):
    p=polynomial(a[i] for i in S)
    values=tuple(evaluate(p,t) for t in a)
    mean=sum(values)/len(a)
    if mean==0:return dict(S=list(S),mean='0',status='ZERO_MEAN')
    x=tuple(-p[j]/mean for j in range(1,d+1))
    good=all(z/mean>=0 for z in values)
    return dict(S=list(S),mean=str(mean),status='VERTEX' if good else 'INFEASIBLE',
                point=list(map(str,x)),polynomial=list(map(str,p)),values=list(map(str,values)))


def verify_record(a,d,record):
    S=record['S'];x=tuple(map(Q,record['point']));mean=Q(record['mean'])
    p=tuple(map(Q,record['polynomial']));values=tuple(map(Q,record['values']))
    assert len(set(S))==len(S)==d and len(p)==d+1 and p[-1]==1
    assert len(x)==d and len(values)==len(a) and mean!=0
    # A monic degree-d polynomial with these distinct d roots is the product.
    assert all(evaluate(p,a[i])==0 for i in S)
    assert all(evaluate(p,t)==v for t,v in zip(a,values))
    assert sum(values)/len(a)==mean
    assert all(x[j]==-p[j+1]/mean for j in range(d))
    rows=row_matrix(a,d)
    actual=[dot(r,x) for r in rows]
    assert all(y==1-v/mean for y,v in zip(actual,values))
    assert {i for i,v in enumerate(actual) if v==1}==set(S)
    assert record['status']==('VERTEX' if all(v<=1 for v in actual) else 'INFEASIBLE')
    return len(actual)


def run():
    rng=random.Random(298)
    models=[(0,[Q(0)]),(0,list(map(Q,range(4)))),(1,list(map(Q,range(3)))),
            (1,list(map(Q,range(4)))),(2,list(map(Q,range(5)))),
            (3,list(map(Q,range(6)))),(4,list(map(Q,range(7)))),
            (5,list(map(Q,range(8)))),(6,list(map(Q,range(9))))]
    for d,m in [(1,5),(2,6),(3,7),(4,8),(5,9),(6,10)]:
        a=[Q(x,7) for x in rng.sample(range(-100,101),m)];rng.shuffle(a)
        models.append((d,a))
    # Nonuniform tiny gaps and deliberately scrambled original row labels.
    models.append((3,[Q(0),Q(1,2**80),Q(1),Q(3),Q(2),Q(-1)]))
    total=Counter();reports=[];saved=[]
    for d,a in models:
        assert len(set(a))==len(a) and d<len(a)
        A=row_matrix(a,d);seen=set();reference=set();counts=Counter()
        for S in combinations(range(len(a)),d):
            record=candidate(a,d,S);counts['square_systems']+=1
            x,rank,inconsistent=square_solve([A[i] for i in S],[Q(1)]*d)
            if record['status']=='ZERO_MEAN':
                assert x is None and inconsistent
                counts['zero_mean_inconsistent']+=1
                continue
            counts['original_row_identities']+=verify_record(a,d,record)
            assert rank==d and tuple(map(Q,record['point']))==x
            counts['coefficient_recoveries']+=1
            if all(dot(r,x)<=1 for r in A):reference.add(x)
            if record['status']=='VERTEX':
                assert x not in seen;seen.add(x);counts['vertices']+=1
                counts['negative_mean_vertices' if Q(record['mean'])<0 else 'positive_mean_vertices']+=1
            else:counts['infeasible_candidates']+=1
            if len(saved)<5 or record['status']=='VERTEX' and Q(record['mean'])<0 and len(saved)<10:
                saved.append(dict(dimension=d,a=list(map(str,a)),record=record))
        assert seen==reference and len(seen)<=math.comb(len(a),d)
        total.update(counts);reports.append(dict(dimension=d,labels=len(a),**counts))
    large=[]
    for d in [8,16,32,64]:
        m=2*d+1;a=list(map(Q,range(m)))
        # Consecutive even block and wrap-around roots. The latter has negative mean.
        for S in [tuple(range(d)),tuple([0,*range(2,d),m-1])]:
            rec=candidate(a,d,S);assert rec['status']=='VERTEX'
            checks=verify_record(a,d,rec)
            large.append(dict(dimension=d,labels=m,mean_sign=1 if Q(rec['mean'])>0 else -1,
                              checked_original_rows=checks,vertices_enumerated=False))
            saved.append(dict(dimension=d,a=list(map(str,a)),record=rec))
    # Explicit hypothesis/filter countercontrols, not failed theorem instances.
    zero=candidate(list(map(Q,range(3))),1,(1,));assert zero['status']=='ZERO_MEAN'
    bad=candidate(list(map(Q,range(5))),2,(1,3));assert bad['status']=='INFEASIBLE'
    neg=candidate(list(map(Q,range(5))),2,(0,4));assert Q(neg['mean'])<0 and neg['status']=='VERTEX'
    # Verification must not call product generation or square-system inversion.
    oldp,olds=globals()['polynomial'],globals()['square_solve']
    def forbidden(*args,**kwargs):raise AssertionError('producer invoked by record verification')
    try:
        globals()['polynomial']=globals()['square_solve']=forbidden
        checked=sum(verify_record(list(map(Q,s['a'])),s['dimension'],s['record']) for s in saved)
    finally:globals()['polynomial'],globals()['square_solve']=oldp,olds
    failures=[]
    from copy import deepcopy
    fixture=next(s for s in saved if s['dimension']>=2)
    for name,edit in [('zero denominator',lambda r:r.update(mean='0')),
                      ('bad mean',lambda r:r.update(mean='12345')),
                      ('bad coordinate',lambda r:r['point'].__setitem__(0,'999')),
                      ('bad leading coefficient',lambda r:r['polynomial'].__setitem__(-1,'2')),
                      ('missing root',lambda r:r['S'].pop()),
                      ('wrong nodal value',lambda r:r['values'].__setitem__(0,'999'))]:
        r=deepcopy(fixture['record']);edit(r)
        try:verify_record(list(map(Q,fixture['a'])),fixture['dimension'],r)
        except (AssertionError,ZeroDivisionError):failures.append(name)
        else:raise AssertionError('forgery accepted '+name)
    report=dict(status='PASS',small_models=reports,totals=dict(total),large_selected=large,
                countercontrols={'zero_mean':zero,'mixed_sign':bad,'negative_mean_valid':neg},
                replay=dict(records=len(saved),original_rows=checked,product_and_solver_disabled=True),
                rejected=failures,
                scope='Exact finite checks; not Lean verification, polynomial enumeration, all-pairs routes or all-real proof by sampling.')
    return report,saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args()
    report,saved=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    for path,data in [(a.out,report),(a.fixtures,saved)]:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['totals'],sort_keys=True))
if __name__=='__main__':main()
