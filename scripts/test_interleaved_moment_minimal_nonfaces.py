#!/usr/bin/env python3
"""Exact finite tests; not a replacement for Lean's universal proof."""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import argparse, hashlib, json, random


def multiply(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out


def evaluate(p,x):
    y=F(0)
    for c in reversed(p):y=y*x+c
    return y


def witness(a,k,S):
    p=[F(1)]
    for i in sorted(S):p=multiply(p,[a[i]**2,-2*a[i],F(1)])
    p += [F(0)]*(2*k+1-len(p))
    h=sum((evaluate(p,t) for t in a),F(0))/len(a)
    assert h>0
    return h,[-p[j]/h for j in range(1,2*k+1)]


def rows(a,k):
    means=[sum((t**j for t in a),F(0))/len(a) for j in range(1,2*k+1)]
    return [[t**j-means[j-1] for j in range(1,2*k+1)] for t in a]


def check(a,k,l,r,all_subsets=True):
    assert len(l)==len(r)==k+1 and len(set(a))==len(a)
    assert all(a[l[i]]<a[r[i]] for i in range(k+1))
    assert all(a[r[i]]<a[l[j]] for i in range(k+1) for j in range(i+1,k+1))
    selected=[t for pair in zip(l,r) for t in pair]
    weights=[1/prod((a[i]-a[j] for j in selected if j!=i),start=F(1)) for i in selected]
    assert all(w<0 if pos%2==0 else w>0 for pos,w in enumerate(weights))
    moment_checks=0
    for degree in range(2*k+1):
        assert sum((w*a[i]**degree for i,w in zip(selected,weights)),F(0))==0
        moment_checks+=1
    A=rows(a,k);subsets=set()
    for side in [l,r]:
        if all_subsets:
            for size in range(k+1):subsets.update(tuple(c) for c in combinations(sorted(side),size))
        else:
            subsets.add(())
            subsets.add(tuple(sorted(side[:-1])))
            subsets.add((side[0],))
    rows_checked=0;sign_slack_checks=0
    for S in sorted(subsets):
        h,x=witness(a,k,S)
        vals=[sum((u*v for u,v in zip(row,x)),F(0)) for row in A]
        for i,val in enumerate(vals):
            exact=1-prod(((a[i]-a[s])**2 for s in S),start=F(1))/h
            assert val==exact and val<=1 and (val==1)==(i in S)
            rows_checked+=1
        assert any(vals[i]<1 for i in l) and any(vals[i]<1 for i in r)
        # Verify the actual original-row zero-sum transport, independently of
        # the recurrence which produced the witness polynomial.
        assert sum((w*(1-vals[i]) for i,w in zip(selected,weights)),F(0))==0
        sign_slack_checks+=2
    return dict(moment_checks=moment_checks,proper_subsets=len(subsets),
                original_row_checks=rows_checked,sign_slack_checks=sign_slack_checks,
                weights=len(weights))


def run():
    rng=random.Random(287);totals={k:0 for k in ['cases','moment_checks','proper_subsets','original_row_checks','sign_slack_checks','weights']}
    records=[]
    for k in range(4):
        m=2*k+4
        for it in range(18):
            vals=sorted({F(t,7) for t in rng.sample(range(-200,201),m)})
            # Global label order deliberately differs from the parameter order.
            a=list(vals);rng.shuffle(a)
            choose=sorted(rng.sample(range(m),2*k+2))
            selected=[a.index(vals[j]) for j in choose]
            stat=check(a,k,selected[::2],selected[1::2])
            totals['cases']+=1
            for key,value in stat.items():totals[key]+=value
    # The original odd-label family on the integer moments: every (k+1)-set
    # has explicit distinct even separators; the count here is computational,
    # not a formal catalogue theorem.
    odd_counts=[]
    for k in range(1,5):
        a=list(map(F,range(4*k+1)));count=0
        for S in combinations(range(1,4*k,2),k+1):
            l=[s-1 for s in S];r=list(S)
            stat=check(a,k,l,r)
            count+=1;totals['cases']+=1
            for key,value in stat.items():totals[key]+=value
        odd_counts.append(dict(k=k,odd_minimal_sets_tested=count))
    for k in [8,16]:
        a=list(map(F,range(4*k+1)));r=list(range(1,2*k+2,2));l=[i-1 for i in r]
        stat=check(a,k,l,r,False);totals['cases']+=1
        for key,value in stat.items():totals[key]+=value
        records.append(dict(dimension=2*k,labels=len(a),**stat))
    # Removing interleaving is false: adjacent moment labels 0,1 can both be
    # tight in dimension two, with a nonnegative polynomial t(t-1).
    a=list(map(F,range(4)));p=[F(0),F(-1),F(1)]
    h=sum((evaluate(p,t) for t in a),F(0))/4;x=[-p[1]/h,-p[2]/h]
    vals=[sum((u*v for u,v in zip(row,x)),F(0)) for row in rows(a,1)]
    assert vals[:2]==[1,1] and all(v<=1 for v in vals)
    invalid=0
    for bad in [([F(0),F(1),F(2),F(3)],1,[0,1],[2,3]),
                ([F(0),F(1),F(1),F(3)],1,[0,2],[1,3]),
                ([F(0),F(1),F(2),F(3)],1,[1,2],[0,3])]:
        try:check(*bad)
        except AssertionError:invalid+=1
        else:raise AssertionError('invalid hypotheses accepted')
    return dict(status='PASS',seed=287,counts=totals,odd_family_checks=odd_counts,large_cases=records,
                rejected_hypothesis_controls=invalid,
                no_interleaving_counterexample=dict(a=list(map(str,a)),tight_labels=[0,1],point=list(map(str,x))),
                scope='Exact supporting finite checks; not Lean compilation, all-real proof by samples, full minimal-nonface catalogue or a diameter bound.')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    result=run();result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result['counts'],sort_keys=True))
if __name__=='__main__':main()
