#!/usr/bin/env python3
"""Exact planar source-rank search via inverse-height breakpoints.

No LP, order-partition enumerator or old source-rank solver is used. For fixed
strict target numerator h, D=t*(-h_y,h_x)+c*h spans every real planar slope.
The c direction translates inverse heights and is irrelevant to their order.
All pair crossings, their singleton cells, and their open intervals are checked.
The executable is separate from Lean; its correctness needs its own audit.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from bisect import bisect_right
from typing import Any, Sequence


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Q(0))


def encoded(value: Any) -> Any:
    if isinstance(value,Q): return str(value)
    if isinstance(value,dict): return {str(k):encoded(v) for k,v in value.items()}
    if isinstance(value,(tuple,list)): return [encoded(v) for v in value]
    return value


def data(points: Sequence[Sequence], target: int, face: Sequence[int], h: Sequence):
    P=tuple(tuple(map(Q,p)) for p in points); H=tuple(map(Q,h)); F=tuple(face)
    require(bool(P) and all(len(p)==2 for p in P) and len(H)==2,'planar data required')
    require(len(P)==len(set(P)), 'duplicate points; supply a finite set')
    require(isinstance(target,int) and 0<=target<len(P),'invalid target')
    require(F==tuple(sorted(set(F))) and target in F and all(0<=i<len(P) for i in F),'invalid face')
    n=tuple(dot(H,tuple(a-b for a,b in zip(z,P[target]))) for z in P)
    require(n[target]==0 and all(s>0 for i,s in enumerate(n) if i!=target),'numerator not strict on global set')
    require(H!=(0,0),'nonzero numerator required')
    e=(-H[1],H[0]); lines=[]
    for i in F:
        if i==target: continue
        beta=dot(e,tuple(a-b for a,b in zip(P[i],P[target])))/n[i]
        lines.append((i,1/n[i],beta))
    return P,H,F,n,e,lines


def sweep(points: Sequence[Sequence], target: int, face: Sequence[int], h: Sequence) -> dict:
    P,H,F,n,e,lines=data(points,target,face,h)
    roots=set()
    for (_,a,b),(_,c,d) in combinations(lines,2):
        if b!=d: roots.add((c-a)/(b-d))
    breaks=sorted(roots)
    intervals=([breaks[0]-1]+[(a+b)/2 for a,b in zip(breaks,breaks[1:])]+[breaks[-1]+1]
               if breaks else [Q(0)])
    samples=sorted(set(breaks+intervals)); table=[]
    best={i:None for i in F if i!=target}
    for t in samples:
        values=[a+t*b for _,a,b in lines]; levels=sorted(set(values),reverse=True)
        ranks={a:k+1 for k,a in enumerate(levels)}
        row=[ranks[a] for a in values]; table.append(row)
        for (i,_,_),r in zip(lines,row):
            key=(r,abs(t),t)
            if best[i] is None or key<best[i][0]: best[i]=(key,t)
    chosen=[]
    for i in F:
        if i==target:
            chosen.append(dict(source=i,rank=0,parameter=Q(0),shift=Q(0),slope=(Q(0),Q(0))))
            continue
        key,t=best[i]
        global_heights=[(1+t*dot(e,tuple(a-b for a,b in zip(z,P[target]))))/n[j]
                        for j,z in enumerate(P) if j!=target]
        c=1-min(global_heights); D=tuple(t*a+c*b for a,b in zip(e,H))
        chosen.append(dict(source=i,rank=key[0],parameter=t,shift=c,slope=D))
    return dict(kind='exact_inverse_height_sweep_not_Lean',target=target,face=list(F),numerator=H,
                lines=[dict(point=i,intercept=a,slope=b) for i,a,b in lines],
                breakpoints=breaks,interval_samples=intervals,samples=samples,
                candidate_ranks=table,chosen=chosen)


def audit(points: Sequence[Sequence], target: int, face: Sequence[int], h: Sequence, cert: dict) -> dict:
    """Reconstruct crossing coverage, all candidate ranks, and positive witnesses.

    This never calls sweep. Every affine crossing is accounted for; the exact
    interval representatives plus all boundaries therefore cover every real t.
    """
    P,H,F,n,e,lines=data(points,target,face,h)
    require(cert['target']==target and cert['face']==list(F) and tuple(map(Q,cert['numerator']))==H,'wrong input binding')
    supplied=[(r['point'],Q(r['intercept']),Q(r['slope'])) for r in cert['lines']]
    require(supplied==lines,'incomplete or changed inverse-height lines')
    breaks=list(map(Q,cert['breakpoints'])); expected=set()
    pair_checks=0
    for i in range(len(lines)):
        for j in range(i):
            _,a,b=lines[i];_,c,d=lines[j]; pair_checks+=1
            if b!=d:
                root=(c-a)/(b-d); require(a+root*b==c+root*d,'crossing identity')
                expected.add(root)
    require(breaks==sorted(expected),'missing, duplicate, or false crossing')
    interior=list(map(Q,cert['interval_samples']))
    if breaks:
        require(len(interior)==len(breaks)+1,'missing open cell')
        require(interior[0]<breaks[0] and breaks[-1]<interior[-1],'missing exterior cell')
        for a,t,b in zip(breaks,interior[1:-1],breaks[1:]):
            require(a<t<b,'sample not strictly inside open cell')
    else: require(len(interior)==1,'empty arrangement needs one cell')
    samples=list(map(Q,cert['samples']))
    require(samples==sorted(set(breaks+interior)),'sample coverage mismatch')
    table=[]; minima={i:None for i in F if i!=target}
    for t in samples:
        values={i:a+b*t for i,a,b in lines}
        row=[]
        ordered=sorted(set(values.values()))
        for i,a,b in lines:
            # Ascending bisection, independent of the producer's descending-rank map.
            rank=1+len(ordered)-bisect_right(ordered,values[i])
            row.append(rank); minima[i]=rank if minima[i] is None else min(minima[i],rank)
        table.append(row)
    require(table==cert['candidate_ranks'],'incorrect candidate rank table')
    require([r['source'] for r in cert['chosen']]==list(F),'missing/duplicate source witness')
    states=[]; nonpositive_before=0
    for witness in cert['chosen']:
        i=witness['source']; D=tuple(map(Q,witness['slope']));t=Q(witness['parameter']);c=Q(witness['shift'])
        require(len(D)==2,'bad denominator slope')
        if i==target:
            require(witness['rank']==0 and D==(0,0),'target case')
            states.append(dict(source=i,rank=0,slope=D));continue
        require(t in samples and D==tuple(t*a+c*b for a,b in zip(e,H)),'witness is not the stated shifted slope')
        q=[1+dot(D,tuple(a-b for a,b in zip(z,P[target]))) for z in P]
        require(all(a>0 for a in q),'denominator not globally positive')
        ratio=[n[j]/q[j] for j in F]
        rx=n[i]/q[i];lower={a for a in ratio if a<rx}
        values={j:a+b*t for j,a,b in lines};upper={a for a in values.values() if values[i]<a}
        require(len(lower)==len(upper)+1==witness['rank']==minima[i],'false optimum or inverse-count identity')
        require(Q(0) in lower,'target zero omitted')
        for j,alpha,beta in lines:
            require(q[j]/n[j]==alpha+beta*t+c,'inverse translation identity')
            require(n[j]/q[j]==1/(alpha+beta*t+c),'reciprocal identity')
        nonpositive_before+=any(1+t*dot(e,tuple(a-b for a,b in zip(z,P[target])))<=0 for z in P)
        states.append(dict(source=i,rank=minima[i],slope=D))
    return dict(states=states,pair_checks=pair_checks,breakpoints=len(breaks),cells=len(samples),
                nonpositive_unshifted_witnesses=nonpositive_before)
