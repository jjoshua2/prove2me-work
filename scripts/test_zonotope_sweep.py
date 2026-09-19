#!/usr/bin/env python3
"""Exact rational sweep regression. Separate from Lean verification."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from pathlib import Path
import argparse, hashlib, json, random


def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def zero(v): return all(x==0 for x in v)
def scale(a,v): return tuple(a*x for x in v)
def sub(u,v): return tuple(x-y for x,y in zip(u,v))
def corner(w,f,d): return tuple(sum((v[j] for v in w if dot(f,v)>0),Q(0)) for j in range(d))
def sign(x): return (x>0)-(x<0)

def transverse(vectors,d):
    nonzero=set(v for v in vectors if not zero(v))
    for n in range(len(nonzero)*max(d-1,0)+2):
        h=tuple(Q(n)**j for j in range(d))
        if all(dot(h,v)!=0 for v in nonzero): return h
    raise AssertionError('polynomial root bound violated')

def prepare(w,f,g,d):
    contrasts=[sub(scale(dot(f,u),v),scale(dot(f,v),u)) for u in w for v in w]
    S=set(w+contrasts); h=transverse(S,d)
    epsilon=min([Q(1)]+[abs(dot(g,v))/(2*(1+abs(dot(h,v)))) for v in S if dot(g,v)!=0])
    k=tuple(a+epsilon*b for a,b in zip(g,h))
    roots=sorted(set(dot(f,v)/(dot(f,v)-dot(k,v)) for v in w
        if not zero(v) and dot(f,v)!=dot(k,v) and 0<dot(f,v)/(dot(f,v)-dot(k,v))<1))
    return dict(d=d,w=w,f=f,g=g,k=k,crossings=roots)

def audit(c,enumerate_corners=True):
    d=c['d']; w=[tuple(map(Q,v)) for v in c['w']];f,g,k=[tuple(map(Q,c[n])) for n in ('f','g','k')]
    roots=list(map(Q,c['crossings']));m=len(w)
    assert len(f)==len(g)==len(k)==d and all(len(v)==d for v in w)
    assert all(zero(v) or dot(f,v)!=0 and dot(g,v)!=0 and dot(k,v)!=0 for v in w)
    assert all(sign(dot(g,v))==sign(dot(k,v)) for v in w)
    expected=sorted(set(dot(f,v)/(dot(f,v)-dot(k,v)) for v in w
        if not zero(v) and dot(f,v)!=dot(k,v) and 0<dot(f,v)/(dot(f,v)-dot(k,v))<1))
    assert roots==expected and len(roots)<=m
    assert corner(w,g,d)==corner(w,k,d)
    ctr=Counter(models=1,generators=m,crossings=len(roots),zero_generators=sum(map(zero,w)))
    vertices=None
    if enumerate_corners:
        vertices={tuple(sum((bits[i]*w[i][j] for i in range(m)),Q(0)) for j in range(d)) for bits in product((0,1),repeat=m)}
        ctr['boolean_representations']=2**m
    times=[Q(0)]+[(a+b)/2 for a,b in zip([Q(0)]+roots,roots+[Q(1)])]+[Q(1)]
    samples=[]
    for t in times:
        objective=tuple((1-t)*a+t*b for a,b in zip(f,k));p=corner(w,objective,d);samples.append(p)
        assert all(zero(v) or dot(objective,v)!=0 for v in w)
        if vertices is not None:
            mx=max(dot(objective,x) for x in vertices)
            assert {x for x in vertices if dot(objective,x)==mx}=={p}
            ctr['singleton_support_checks']+=len(vertices)
    for n,t in enumerate(roots):
        obj=tuple((1-t)*a+t*b for a,b in zip(f,k));ties=[v for v in w if dot(obj,v)==0 and not zero(v)]
        assert ties;u=ties[0];j=next(j for j,x in enumerate(u) if x)
        coeff=[v[j]/u[j] for v in ties]
        assert all(v==scale(a,u) for v,a in zip(ties,coeff))
        ctr['parallel_tie_events']+=len(ties)>1
        p,q=samples[n+1],samples[n+2];assert p!=q
        if vertices is not None:
            face={x for x in vertices if dot(obj,x)==sum(max(Q(0),dot(obj,v)) for v in w)}
            direction=sub(q,p);jj=next(j for j,x in enumerate(direction) if x)
            assert p in face and q in face
            for x in face:
                parameter=(x[jj]-p[jj])/direction[jj]
                assert 0<=parameter<=1 and sub(x,p)==scale(parameter,direction)
            ctr['whole_face_checks']+=len(face)
    ctr['constructed_test_route_edges']=len(roots)
    ctr['changed_target_objectives']=k!=g
    return ctr

def encode(o):
    if isinstance(o,Q): return str(o)
    if isinstance(o,dict): return {k:encode(v) for k,v in o.items()}
    if isinstance(o,(list,tuple)): return [encode(v) for v in o]
    return o

def run():
    rng=random.Random(313);total=Counter();saved=[];large=[]
    systems=[(0,[]),(0,[()]),(2,[(1,0),(0,1)]),(2,[(1,0),(2,0),(-3,0),(0,1),(0,0)]),(2,[(1,0),(0,1),(1,1)])]
    for _ in range(50):
        d=rng.randrange(1,5);m=rng.randrange(0,9)
        w=[tuple(rng.randrange(-2,3) for j in range(d)) for i in range(m)]
        if m>2:w[-1]=tuple(-x for x in w[0])
        systems.append((d,w))
    for number,(d,ww) in enumerate(systems):
        w=[tuple(map(Q,v)) for v in ww];f=transverse(w,d)
        for g in [f,scale(-1,f),transverse(w+[tuple(Q(i+1) for i in range(d))],d)]:
            rec=prepare(w,f,g,d);total.update(audit(rec));
            if number%6==0:saved.append(rec)
    for d in [8,16,32,64]:
        w=[tuple(Q(int(j==i)) for j in range(d)) for i in range(min(d,10))]
        w += [scale(2,w[0]),scale(-3,w[0]),tuple(Q(0) for _ in range(d))]
        f=tuple(Q(1) for _ in range(d));rec=prepare(w,f,scale(-1,f),d)
        count=audit(rec,False);large.append(dict(d=d,**count));saved.append(rec)
    # Replay rejects forged input without any generic-objective construction.
    functions={n:globals()[n] for n in ('transverse','prepare')}
    def forbidden(*args,**kwargs): raise AssertionError('construction during saved replay')
    try:
        for n in functions: globals()[n]=forbidden
        for c in saved: audit(c,len(c['w'])<=8)
    finally:
        globals().update(functions)
    from copy import deepcopy
    base=next(c for c in saved if c['crossings'] and c['d']>=2)
    mutations=[('missing crossing',lambda c:c['crossings'].pop()),
      ('duplicate crossing',lambda c:c['crossings'].append(c['crossings'][0])),
      ('wrong target chamber',lambda c:c.update(k=scale(-1,c['g']))),
      ('nonregular target',lambda c:c.update(k=tuple(Q(0) for _ in c['k'])))]
    rejected=[]
    for name,change in mutations:
        c=deepcopy(base);change(c)
        try: audit(c)
        except (AssertionError,ZeroDivisionError): rejected.append(name)
        else: raise AssertionError('forgery accepted: '+name)
    # Direct unperturbed interpolation from (1,1) to (-1,-1) hits a 2D face.
    assert dot((Q(0),Q(0)),(Q(1),Q(0)))==dot((Q(0),Q(0)),(Q(0),Q(1)))==0
    return dict(status='PASS',totals=dict(total),large=large,saved_records=len(saved),
      construction_disabled=True,rejected=rejected,
      naive_simultaneous_independent_tie_control=True,
      scope='Exact finite supporting checks. The test constructs sample routes; the Lean target certifies sweeps and faces, not a completed all-pairs walk theorem.'),saved

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',type=Path,required=True);args=parser.parse_args()
    report,fixtures=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    for name,o in [('exact-tests.json',report),('fixtures.json',fixtures)]:
        (args.out/name).write_text(json.dumps(encode(o),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['totals'],sort_keys=True))
if __name__=='__main__':main()
