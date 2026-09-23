#!/usr/bin/env python3
"""Exact closed-form upper rank for a strict convex finite real/rational chain.

The Python certificate is separate from Lean. Fractions and explicit checks are
used; no arrangement search, LP, or graph is an input to the producer.
"""
from fractions import Fraction as Q
from itertools import combinations


def need(condition, message):
    if not condition:
        raise ValueError(message)


def encode(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [encode(v) for v in x]
    return x


def prepare(w, a):
    w, a = tuple(map(Q, w)), tuple(map(Q, a))
    need(len(w) == len(a) and len(w) > 0, 'nonempty paired chain required')
    need(all(x < y for x, y in zip(w, w[1:])), 'abscissas must be strictly ordered')
    slopes = [(b-a0)/(y-x) for x,y,a0,b in zip(w,w[1:],a,a[1:])]
    need(all(x < y for x,y in zip(slopes,slopes[1:])), 'strict convexity is required')
    return w, a, slopes


def produce(w, a):
    w, a, slopes = prepare(w,a)
    # Every secant is a positive weighted average of adjacent secants.
    M = 1 + max([abs(s) for s in slopes] or [Q(0)])
    choices = []
    for t in (-M, M):
        values = [b+t*x for x,b in zip(w,a)]
        c = 1-min(values)
        choices.append(dict(tilt=t,shift=c,heights=[z+c for z in values]))
    return dict(abscissas=w,ordinates=a,adjacent_slopes=slopes,bound=M,
                choices=choices,ranks=[min(k,len(w)-1-k) for k in range(len(w))])


def audit(w, a, cert, exhaustive_triples=False):
    w,a,slopes = prepare(w,a); N=len(w)
    need(tuple(map(Q,cert['abscissas']))==w and tuple(map(Q,cert['ordinates']))==a,'changed input chain')
    need(list(map(Q,cert['adjacent_slopes']))==slopes,'false adjacent secants')
    M=Q(cert['bound']);need(M>0,'nonpositive tilt bound')
    pair_checks=0
    for i,j in combinations(range(N),2):
        need(abs(a[j]-a[i]) < M*(w[j]-w[i]),'tilt does not dominate a secant')
        # Independently reconstitute the exact weighted average, so an
        # adjacent-slopes audit never treats an omitted secant as a sample.
        numerator=sum((slopes[k]*(w[k+1]-w[k]) for k in range(i,j)),Q(0))
        need(numerator==a[j]-a[i],'telescoping secant identity')
        pair_checks+=1
    triples=0
    if exhaustive_triples:
        for i,j,k in combinations(range(N),3):
            need((a[j]-a[i])*(w[k]-w[j]) < (a[k]-a[j])*(w[j]-w[i]),'strict triple inequality')
            triples+=1
    need(len(cert['choices'])==2,'two extreme tilts required')
    raw_counts=[]; reciprocal=[]
    for sign,entry in zip((-1,1),cert['choices']):
        t,c=Q(entry['tilt']),Q(entry['shift']);need(t==sign*M,'wrong tilt')
        f=[b+t*x+c for x,b in zip(w,a)]
        need(list(map(Q,entry['heights']))==f and all(v>0 for v in f),'false positive height witness')
        need(all(sign*(y-x)>0 for x,y in zip(f,f[1:])),'tilt not strictly monotone')
        counts=[len({v for v in f if v>f[k]}) for k in range(N)]
        need(counts==([*range(N)] if sign==-1 else list(reversed(range(N)))),'wrong extreme ranks')
        inverse=[1/v for v in f]
        below=[len({Q(0)}|{r for r in inverse if r<inverse[k]}) for k in range(N)]
        need(below==[z+1 for z in counts],'target zero / reciprocal count mismatch')
        raw_counts.append(counts);reciprocal.append(below)
    minimum=[min(x,y) for x,y in zip(*raw_counts)]
    need(minimum==cert['ranks']==[min(k,N-1-k) for k in range(N)],'false closed-form minimum')
    need(all(2*(r+1)<=N+1 for r in minimum),'half-size bound failed')
    return dict(points=N,pair_checks=pair_checks,triples=triples,
                maximum_rank=max(minimum),minimum=minimum)
