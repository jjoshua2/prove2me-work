#!/usr/bin/env python3
"""Exact finite tests for the selected-set bridge, not Lean verification.

The dependency's accepted packing implementation is reused unchanged. This
consumer checks the literal selected-set gap predicate, not its parity shortcut.
"""
from __future__ import annotations
from collections import Counter
from copy import deepcopy
from itertools import combinations
from pathlib import Path
import argparse
import hashlib
import json
import test_alternating_complement_routes as accepted


def selected(m: int, S) -> tuple[int, ...]:
    if type(m) is not int or m < 0:
        raise ValueError('invalid universe')
    data=tuple(S)
    if any(type(x) is not int or not 0 <= x < m for x in data) or len(set(data)) != len(data):
        raise ValueError('invalid selected labels')
    return tuple(sorted(data))


def gaps(m: int, S: tuple[int, ...]) -> bool:
    H=[i for i in range(m) if i not in S]
    return all(sum(i < s < j for s in S) % 2 == 0 for i,j in combinations(H,2))


def build(m: int, S, T) -> list[tuple[int, ...]]:
    S,T=selected(m,S),selected(m,T)
    if len(S)!=len(T) or not gaps(m,S) or not gaps(m,T):
        raise ValueError('endpoint violates cardinality or even-gap condition')
    U=set(range(m));h=tuple(sorted(U-set(S)));k=tuple(sorted(U-set(T)))
    return [tuple(sorted(U-set(H))) for H in accepted.construct(m,h,k)]


def audit(m: int, S, T, path) -> int:
    S,T=selected(m,S),selected(m,T);d=len(S)
    if len(T)!=d or not path or tuple(path[0])!=S or tuple(path[-1])!=T:
        raise ValueError('endpoints')
    if len(path)-1 > 2*(m-d)+1:
        raise ValueError('bound')
    P=[selected(m,p) for p in path]
    if any(len(p)!=d or not gaps(m,p) for p in P):
        raise ValueError('invalid intermediate set')
    if any(p==q or len(set(p)&set(q))+1!=d for p,q in zip(P,P[1:])):
        raise ValueError('not a nontrivial one-label exchange')
    return len(P)-1


def run():
    counts=Counter(); saved=[];models=[]
    for m in range(11):
        for d in range(m+1):
            V=[]
            for S in combinations(range(m),d):
                H=tuple(i for i in range(m) if i not in S)
                good=gaps(m,S);phase=accepted.legal(m,H)
                assert good==phase
                counts['all_subsets']+=1
                counts['legal_subsets' if good else 'illegal_subsets']+=1
                for rank,h in enumerate(H):
                    assert sum(s<h for s in S)+rank==h
                    counts['rank_balance_identities']+=1
                for i,j in combinations(range(len(H)),2):
                    below_i=sum(s<H[i] for s in S);below_j=sum(s<H[j] for s in S)
                    between=sum(H[i]<s<H[j] for s in S)
                    assert below_j==below_i+between
                    counts['gap_partition_identities']+=1
                if good:V.append(S)
            model=Counter(m=m,d=d,configurations=len(V))
            for S in V:
                for T in V:
                    path=build(m,S,T);L=audit(m,S,T,path)
                    counts['endpoint_pairs']+=1;counts['exchanges']+=L
                    counts['visited_even_gap_sets']+=len(path)
                    model['pairs']+=1
                    h=[i for i in range(m) if i not in S];k=[i for i in range(m) if i not in T]
                    counts['opposite_phase_pairs']+=bool(h and k and h[0]%2!=k[0]%2)
                    counts['repeated_vertex_routes']+=len(set(path))<len(path)
                    counts['target_label_loss_routes']+=any(not(set(p)&set(T))<=set(q) for p,q in zip(path,path[1:]))
                    if not any(c['m']==m and len(c['S'])==d for c in saved):
                        saved.append(dict(m=m,S=S,T=T,path=path))
            models.append(dict(model))
    large=[]
    for m,r in [(65,32),(127,32),(257,64)]:
        U=set(range(m));h=tuple(3*i for i in range(r));k=tuple(3*i+1 for i in range(r))
        if k[-1]>=m:h=tuple(range(r));k=tuple(range(m-r,m))
        S=tuple(sorted(U-set(h)));T=tuple(sorted(U-set(k)))
        p=build(m,S,T);L=audit(m,S,T,p)
        large.append(dict(m=m,d=m-r,length=L,bound=2*r+1,full_graph_enumerated=False))
        saved.append(dict(m=m,S=S,T=T,path=p))
    old=accepted.construct
    def forbidden(*a,**kw):raise AssertionError('packing producer invoked by consumer')
    accepted.construct=forbidden
    try:
        replay=sum(audit(c['m'],c['S'],c['T'],c['path']) for c in saved)
    finally:accepted.construct=old
    invalid=[('out of range',5,[0,5],[1,2]),('duplicate label',5,[0,0],[1,2]),
             ('unequal size',5,[0],[1,2]),('odd selected gap',5,[1,3],[0,1])]
    rejected=[]
    for name,m,S,T in invalid:
        try:build(m,S,T)
        except ValueError:rejected.append(name)
        else:raise AssertionError('invalid endpoint accepted '+name)
    c=next(c for c in saved if len(c['path'])>2 and c['m']>4)
    for name,mutate in [('stationary edge',lambda p:p.insert(1,p[0])),
                        ('wrong endpoint',lambda p:p.__setitem__(-1,())),
                        ('malformed intermediate',lambda p:p.__setitem__(1,(c['m'],)))]:
        p=deepcopy(c['path']);mutate(p)
        try:audit(c['m'],c['S'],c['T'],p)
        except ValueError:rejected.append(name)
        else:raise AssertionError('forged path accepted '+name)
    return dict(status='PASS',counts=dict(counts),models=models,large=large,
                saved_records=len(saved),saved_exchanges=replay,rejected=rejected,
                producer_disabled_replay=True,
                scope='Exact finite checks of selected-set enumeration/parity/route transport; not Lean verification or a geometric diameter theorem.'),saved


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    report,records=run()
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['unchanged_dependency_sha256']=hashlib.sha256(Path(accepted.__file__).read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    for name,data in [('exact-tests.json',report),('fixtures.json',records)]:
        (args.out/name).write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))

if __name__=='__main__':main()
