#!/usr/bin/env python3
"""Exact supporting checks for the triangular completion lower-bound packet.
No tests in this file constitute Lean compilation or an all-real proof.
"""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product, combinations
from collections import Counter
from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json, random
import test_completion_direction_obstruction as old


def minimal_rows(d: int, e: F):
    if d < 1 or not 0 < e < F(1, 2):
        raise ValueError('dimension/epsilon')
    out=[]
    for i in range(d):
        a=[F(0)]*d; b=[F(0)]*d
        a[i]=-1; b[i]=1
        if i+1<d: a[i+1]=b[i+1]=e
        out.extend([(tuple(a),F(0)),(tuple(b),F(1))])
    return out


def corner(bits, e):
    x=[F(0)]*len(bits)
    for i in reversed(range(len(bits))):
        s=e*x[i+1] if i+1<len(bits) else F(0)
        x[i]=1-s if bits[i] else s
    return tuple(x)


def line(bits, e, t):
    x=[F(0)]*(len(bits)+1); x[-1]=t
    for i in reversed(range(len(bits))):
        s=e*x[i+1]; x[i]=1-s if bits[i] else s
    return tuple(x)


def hull_weights(x, e):
    if not x:return {(): F(1)}
    c=e*x[1] if len(x)>1 else F(0)
    t=(x[0]-c)/(1-2*c)
    assert 0<=t<=1
    tail=hull_weights(x[1:],e)
    return {(b,)+bits: weight*(t if b else 1-t)
            for bits,weight in tail.items() for b in [0,1]}


def make_edge(bits,e):
    p=line(bits,e,F(0)); q=line(bits,e,F(1)); R=minimal_rows(len(p),e)
    active=[2*i+b for i,b in enumerate(bits)]
    score=tuple(sum((R[k][0][j] for k in active),F(0)) for j in range(len(p)))
    return dict(epsilon=e,bits=bits,p=p,q=q,delta=old.sub(q,p),score=score,
                support_value=sum((R[k][1] for k in active),F(0)))


def audit_edge(c):
    e=F(c['epsilon']);bits=c['bits'];p=tuple(map(F,c['p']));q=tuple(map(F,c['q']))
    D=tuple(map(F,c['delta']));score=tuple(map(F,c['score']));M=F(c['support_value'])
    if any(b not in (0,1) for b in bits) or len(p)!=len(bits)+1 or len(q)!=len(p):raise ValueError('labels')
    R=minimal_rows(len(p),e)
    if not(p[-1]==0 and q[-1]==1) or old.sub(q,p)!=D or D[-1]!=1:raise ValueError('normalized endpoints')
    if any(old.dot(a,x)>b for a,b in R for x in [p,q]):raise ValueError('original feasibility')
    Ip={i for i,(a,b) in enumerate(R) if old.dot(a,p)==b}
    Iq={i for i,(a,b) in enumerate(R) if old.dot(a,q)==b}
    common={2*i+b for i,b in enumerate(bits)}
    if Ip& Iq !=common or old.rank([R[i][0] for i in common])!=len(bits):raise ValueError('common slice')
    if old.rank([R[i][0] for i in Ip])!=len(p) or old.rank([R[i][0] for i in Iq])!=len(p):raise ValueError('extremality')
    expected=tuple(sum((R[k][0][j] for k in common),F(0)) for j in range(len(p)))
    if score!=expected or M!=sum((R[k][1] for k in common),F(0)):raise ValueError('objective')
    if any(D[i] != e*(1-2*b)*D[i+1] for i,b in enumerate(bits)):raise ValueError('direction recurrence')
    if old.dot(score,p)!=M or old.dot(score,q)!=M:raise ValueError('support value')
    # Common rows have rank d-1; their complete feasible slice is a line.
    # The two last-coordinate inequalities truncate that line exactly at p,q.
    return dict(original_inequalities=2*len(p),checked_endpoints=2,
                support_dimension=1,common_rank=len(bits))


def audit_hull(c):
    e=F(c['epsilon']);x=tuple(map(F,c['point']));terms=c['terms'];d=len(x)
    R=minimal_rows(d,e)
    if any(old.dot(a,x)>b for a,b in R):raise ValueError('hull input')
    total=F(0);avg=[F(0)]*d
    for t in terms:
        bits=t['bits'];v=tuple(map(F,t['vertex']));weight=F(t['weight'])
        if weight<0 or len(bits)!=d or len(v)!=d:raise ValueError('hull term')
        if any(old.dot(a,v)>b for a,b in R):raise ValueError('corner feasibility')
        if any(old.dot(R[2*i+b][0],v)!=R[2*i+b][1] for i,b in enumerate(bits)):raise ValueError('corner rows')
        total+=weight
        avg=[a+weight*b for a,b in zip(avg,v)]
    if total!=1 or tuple(avg)!=x:raise ValueError('convex combination')


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x


def run():
    rng=random.Random(320);totals=Counter();models=[];edges=[];hulls=[];large=[]
    for e in [F(1,4),F(1,3),F(2,5)]:
        for d in range(1,7):
            R=minimal_rows(d,e);V={bits:corner(bits,e) for bits in product((0,1),repeat=d)}
            reference=set()
            for I in combinations(range(2*d),d):
                x=old.solve([R[i][0] for i in I],[R[i][1] for i in I]);totals['square_systems']+=1
                if x is not None and all(old.dot(a,x)<=b for a,b in R):reference.add(x)
            assert reference==set(V.values())
            Ds=set();checks=0
            for bits in product((0,1),repeat=d-1):
                c=make_edge(bits,e);audit_edge(c);Ds.add(c['delta'])
                face={x for x in reference if old.dot(c['score'],x)==c['support_value']}
                assert face=={c['p'],c['q']};checks+=len(reference)
                if d<=3 or bits==tuple([0]*(d-1)):edges.append(c)
            assert len(Ds)==2**(d-1) and all(v[-1]==1 for v in Ds)
            for _ in range(3):
                x=[F(0)]*d
                for i in reversed(range(d)):
                    a=e*x[i+1] if i+1<d else F(0)
                    x[i]=a+(1-2*a)*F(rng.randrange(11),10)
                weights=hull_weights(tuple(x),e)
                c=dict(epsilon=e,point=tuple(x),terms=[dict(bits=b,vertex=V[b],weight=w) for b,w in weights.items()])
                audit_hull(c);hulls.append(c);totals['convex_combination_terms']+=len(weights)
            # Strict-other-row witnesses support the written facet interpretation;
            # the Lean public statement uses only the explicit 2d inequalities.
            for i in range(d):
                for side in [0,1]:
                    x=[F(1,2)]*d;a=e*x[i+1] if i+1<d else F(0);x[i]=1-a if side else a
                    assert all(old.dot(A,x)==b if j==2*i+side else old.dot(A,x)<b for j,(A,b) in enumerate(R))
                    totals['unique_row_witness_checks']+=len(R)
            models.append(dict(dimension=d,epsilon=e,original_inequalities=2*d,vertices=len(reference),selected_directions=len(Ds),full_support_checks=checks))
            totals['vertices']+=len(reference);totals['selected_edges']+=len(Ds);totals['full_support_checks']+=checks
    for d in [8,16,32,64]:
        data=[]
        for _ in range(8):
            bits=tuple(rng.randrange(2) for i in range(d-1));c=make_edge(bits,F(1,4));audit_edge(c);edges.append(c);data.append(c)
        large.append(dict(dimension=d,selected_edges=8,whole_graph_enumerated=False))
    fixtures=json.loads(json.dumps(encode(dict(edges=edges,hulls=hulls))))
    original={n:globals()[n] for n in ['line','corner','make_edge','hull_weights']}
    def forbidden(*a,**k):raise AssertionError('construction during audit')
    try:
        for n in original:globals()[n]=forbidden
        for c in fixtures['edges']:audit_edge(c)
        for c in fixtures['hulls']:audit_hull(c)
    finally:globals().update(original)
    c0=next(c for c in fixtures['edges'] if len(c['bits'])==2);bad=[]
    mutations=[('zero epsilon',lambda c:c.update(epsilon='0')),('collapsed interval',lambda c:c.update(epsilon='1/2')),
               ('infeasible endpoint',lambda c:c['p'].__setitem__(0,'99')),
               ('wrong direction',lambda c:c['delta'].__setitem__(0,'99')),
               ('wrong objective',lambda c:c['score'].__setitem__(0,'99'))]
    for name,edit in mutations:
        c=deepcopy(c0);edit(c)
        try:audit_edge(c)
        except (ValueError,AssertionError):bad.append(name)
        else:raise AssertionError('forgery accepted')
    c=deepcopy(fixtures['hulls'][-1]);c['terms'][0]['weight']='-1'
    try:audit_hull(c)
    except ValueError:bad.append('negative convex weight')
    else:raise AssertionError('bad hull certificate accepted')
    return dict(status='PASS',Lean_verification=False,models=models,totals=dict(totals),large=large,
                saved_edges=len(edges),saved_hull_records=len(hulls),serialized_producer_disabled=True,rejected=bad),fixtures


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    report,fixtures=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['reference_sha256']=hashlib.sha256(Path(old.__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',fixtures)]:
        (a.out/name).write_text(json.dumps(encode(obj),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['totals'],sort_keys=True))
if __name__=='__main__':main()
