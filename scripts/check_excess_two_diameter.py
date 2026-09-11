#!/usr/bin/env python3
"""Exact rational regression certificates for the normalized two-moment slice.

These finite checks supplement, and never substitute for, the Lean proof.
Vertex and edge carriers are certified by their exact support/equality ranks.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
import json


def check(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def support(x):
    return {i for i, v in enumerate(x) if v != 0}


def feasible(t, mu, x):
    return all(v >= 0 for v in x) and sum(x) == 1 and sum(a*b for a,b in zip(t,x)) == mu


def rank(t, S):
    return 0 if not S else (1 if len({t[i] for i in S}) == 1 else 2)


def unit(n, i):
    return tuple(Q(k == i) for k in range(n))


def pair(t, mu, i, j):
    check(t[i] < mu < t[j], 'pair does not straddle moment')
    x=[Q(0)]*len(t)
    x[i]=(t[j]-mu)/(t[j]-t[i])
    x[j]=(mu-t[i])/(t[j]-t[i])
    return tuple(x)


def vertex(t, mu, x):
    return feasible(t, mu, x) and len(support(x)) == rank(t, support(x))


def edge_or_stay(t, x, y):
    S=support(x)|support(y)
    return x==y or len(S)-rank(t,S)==1


def selector(t, mu, s):
    S=sorted(support(s))
    check(bool(S), 'empty support')
    i=min(S,key=lambda k:t[k]);j=max(S,key=lambda k:t[k])
    if t[i]==mu:return unit(len(t),i)
    if t[j]==mu:return unit(len(t),j)
    return pair(t,mu,i,j)


def portal(t, mu, x, y):
    if len(support(x))==1 or len(support(y))==1:return x
    i=next(i for i in support(x) if t[i]<mu)
    j=next(i for i in support(y) if mu<t[i])
    return pair(t,mu,i,j)


def main():
    counts=dict(slice_cases=0, feasible_cases=0, vertex_certificates=0,
                ordered_vertex_routes=0, checkpoint_selectors=0,
                common_zero_checks=0, exact_diameter_two_cases=0)
    mus=[Q(-2),Q(-1),Q(-1,2),Q(0),Q(1,2),Q(1),Q(2)]
    for n in range(6):
        for tt in product((-1,0,1),repeat=n):
            t=tuple(map(Q,tt))
            for mu in mus:
                counts['slice_cases']+=1
                vertices=[unit(n,i) for i in range(n) if t[i]==mu]
                vertices += [pair(t,mu,i,j) for i in range(n) for j in range(n) if t[i]<mu<t[j]]
                if not vertices:continue
                counts['feasible_cases']+=1
                for x in vertices:
                    check(vertex(t,mu,x),'invalid vertex certificate')
                    counts['vertex_certificates']+=1
                sharp=False
                for x,y in product(vertices,repeat=2):
                    w=portal(t,mu,x,y)
                    check(vertex(t,mu,w),'invalid portal vertex')
                    check(edge_or_stay(t,x,w) and edge_or_stay(t,w,y),'invalid edge carrier')
                    for i in range(n):
                        if x[i]==y[i]==0:
                            check(w[i]==0,'common zero lost')
                            counts['common_zero_checks']+=1
                    sharp |= not edge_or_stay(t,x,y)
                    counts['ordered_vertex_routes']+=1
                    s=tuple((a+2*b)/3 for a,b in zip(x,y))
                    p=selector(t,mu,s)
                    check(feasible(t,mu,s) and vertex(t,mu,p),'bad checkpoint/selector')
                    check(support(p)<=support(s),'selector added positive coordinate')
                    counts['checkpoint_selectors']+=1
                counts['exact_diameter_two_cases']+=int(sharp)
    check(counts['exact_diameter_two_cases']>0,'sharpness case missing')
    print(json.dumps({'status':'PASS','arithmetic':'fractions.Fraction',
                     'evidence_level':'finite exact certificates, not a Lean/platform verdict',
                     'families':'all t in {-1,0,1}^n for 0 <= n <= 5; seven interior/boundary/exterior moments',
                     **counts},indent=2))


if __name__=='__main__':
    main()
