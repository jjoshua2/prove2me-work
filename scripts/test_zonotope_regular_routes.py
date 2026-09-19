#!/usr/bin/env python3
"""Exact finite walk checks; neither Lean extraction nor an arbitrary-input parser proof."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random
import test_zonotope_sweep as sweep


def construct(w,f,g,d):
    rec=sweep.prepare(w,f,g,d)
    mesh=[Q(0)]+rec['crossings']+[Q(1)]
    samples=[(a+b)/2 for a,b in zip(mesh,mesh[1:])]
    objectives=[tuple((1-t)*x+t*y for x,y in zip(f,rec['k'])) for t in samples]
    coefficients=[[Q(sweep.dot(h,v)>0) for v in w] for h in objectives]
    vertices=[tuple(sum((c[i]*w[i][j] for i in range(len(w))),Q(0)) for j in range(d)) for c in coefficients]
    rec.update(mesh=mesh,samples=samples,coefficients=coefficients,vertices=vertices)
    return rec


def audit(rec,exhaustive=True):
    d=rec['d'];w=[tuple(map(Q,v)) for v in rec['w']];m=len(w)
    f,g,k=[tuple(map(Q,rec[key])) for key in ('f','g','k')]
    mesh=list(map(Q,rec['mesh']));samples=list(map(Q,rec['samples']))
    roots=list(map(Q,rec['crossings']));V=[tuple(map(Q,v)) for v in rec['vertices']]
    C=[list(map(Q,c)) for c in rec['coefficients']]
    if not all(len(v)==d for v in w+[f,g,k]+V):raise ValueError('dimension')
    if not all(sweep.zero(v) or sweep.dot(f,v)*sweep.dot(f,v)>0 and sweep.dot(g,v)*sweep.dot(k,v)>0 for v in w):raise ValueError('regular endpoint signs')
    expected=sorted(set(sweep.dot(f,v)/(sweep.dot(f,v)-sweep.dot(k,v)) for v in w
      if not sweep.zero(v) and sweep.dot(f,v)!=sweep.dot(k,v)
      and 0<sweep.dot(f,v)/(sweep.dot(f,v)-sweep.dot(k,v))<1))
    if roots!=expected or mesh!=[Q(0)]+expected+[Q(1)] or len(roots)>m:raise ValueError('exact ordered mesh')
    if not len(V)==len(samples)==len(C)==len(roots)+1:raise ValueError('walk length')
    points=None;checks=Counter(routes=1,edges=len(roots),generators=m,zero_generators=sum(map(sweep.zero,w)))
    if exhaustive:
        points={tuple(sum((bits[i]*w[i][j] for i in range(m)),Q(0)) for j in range(d)) for bits in product((0,1),repeat=m)}
        checks['boolean_representations']=2**m
    for j,(t,x,c) in enumerate(zip(samples,V,C)):
        if not mesh[j]<t<mesh[j+1] or len(c)!=m:raise ValueError('interior chamber sample')
        obj=tuple((1-t)*a+t*b for a,b in zip(f,k))
        if any(c[i] != int(sweep.dot(obj,w[i])>0) or not sweep.zero(w[i]) and sweep.dot(obj,w[i])==0 for i in range(m)):raise ValueError('chamber saturation')
        if x!=tuple(sum((c[i]*w[i][z] for i in range(m)),Q(0)) for z in range(d)):raise ValueError('original point')
        if points is not None:
            cap=sum(max(Q(0),sweep.dot(obj,v)) for v in w)
            if {p for p in points if sweep.dot(obj,p)==cap}!={x}:raise ValueError('not singleton whole face')
            checks['singleton_support_comparisons']+=len(points)
    for objective,point in [(f,V[0]),(g,V[-1])]:
        if point!=tuple(sum((v[j] for v in w if sweep.dot(objective,v)>0),Q(0)) for j in range(d)):raise ValueError('wrong endpoint')
    for j,t in enumerate(roots):
        obj=tuple((1-t)*a+t*b for a,b in zip(f,k));x,y=V[j:j+2]
        if x==y:raise ValueError('stationary transition')
        D=sweep.sub(y,x);axis=next(i for i,z in enumerate(D) if z)
        ties=[v for v in w if sweep.dot(obj,v)==0 and not sweep.zero(v)]
        if not ties or any(v!=sweep.scale(v[axis]/D[axis],D) for v in ties):raise ValueError('not one-dimensional event')
        # Direct free-coefficient endpoints of the WHOLE tie face.
        fixed=tuple(sum((v[z] for v in w if sweep.dot(obj,v)>0),Q(0)) for z in range(d))
        low=sum((min(Q(0),v[axis]/D[axis]) for v in ties),Q(0))
        high=sum((max(Q(0),v[axis]/D[axis]) for v in ties),Q(0))
        end0=tuple(a+low*b for a,b in zip(fixed,D));end1=tuple(a+high*b for a,b in zip(fixed,D))
        if {x,y}!={end0,end1}:raise ValueError('event endpoints not chamber vertices')
        checks['parallel_tie_events']+=len(ties)>1
        if points is not None:
            cap=sum(max(Q(0),sweep.dot(obj,v)) for v in w)
            face=[p for p in points if sweep.dot(obj,p)==cap]
            for p in face:
                ratio=(p[axis]-x[axis])/D[axis]
                if not 0<=ratio<=1 or sweep.sub(p,x)!=sweep.scale(ratio,D):raise ValueError('larger event face')
            checks['whole_event_face_points']+=len(face)
    checks['vertices_visited']=len(V)
    return checks


def run():
    rng=random.Random(315);systems=[(0,[]),(0,[()]),(3,[]),(2,[(0,0)]),
      (2,[(1,0),(2,0),(-3,0),(0,1),(0,0)]),(2,[(1,0),(0,1),(1,1)])]
    for _ in range(36):
        d=rng.randrange(1,5);m=rng.randrange(1,9)
        w=[tuple(rng.randrange(-3,4) for _ in range(d)) for _ in range(m)]
        if m>2:w[-1]=tuple(-x for x in w[0])
        systems.append((d,w))
    total=Counter();saved=[]
    for no,(d,ww) in enumerate(systems):
        w=[tuple(map(Q,v)) for v in ww];f=sweep.transverse(w,d)
        for g in (f,sweep.scale(-1,f)):
            rec=construct(w,f,g,d);total.update(audit(rec))
            if no%5==0:saved.append(rec)
    large=[]
    for d in (8,16,32,64):
        w=[tuple(Q(i==j) for j in range(d)) for i in range(min(d,12))]
        w += [sweep.scale(2,w[0]),sweep.scale(-3,w[0]),tuple(Q(0) for _ in range(d))]
        f=tuple(Q(1) for _ in range(d));rec=construct(w,f,sweep.scale(-1,f),d)
        large.append(dict(dimension=d,full_graph_enumerated=False,**audit(rec,False)));saved.append(rec)
    original=construct;functions={name:getattr(sweep,name) for name in ('prepare','transverse','corner')}
    def forbidden(*a,**k):raise AssertionError('construction during saved verification')
    try:
        globals()['construct']=forbidden
        for name in functions:setattr(sweep,name,forbidden)
        for rec in saved:audit(rec,len(rec['w'])<=8)
    finally:
        globals()['construct']=original
        for name,fun in functions.items():setattr(sweep,name,fun)
    base=next(c for c in saved if len(c['crossings'])>=2 and c['d']>=2);rejected=[]
    mutations=[('missing crossing',lambda c:c['crossings'].pop()),('unsorted mesh',lambda c:c['mesh'].reverse()),
      ('sample at event',lambda c:c['samples'].__setitem__(0,c['mesh'][1])),
      ('stationary edge',lambda c:c['vertices'].__setitem__(1,c['vertices'][0])),
      ('wrong point',lambda c:c['vertices'].__setitem__(0,tuple(Q(999) for _ in range(c['d'])))),
      ('non-saturated coefficient',lambda c:c['coefficients'][0].__setitem__(0,Q(1,2)))]
    for name,change in mutations:
        c=deepcopy(base);change(c)
        try:audit(c)
        except (ValueError,AssertionError,StopIteration,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('forgery accepted '+name)
    return dict(status='PASS',counts=dict(total),large=large,saved_records=len(saved),
      constructors_disabled=True,rejected=rejected,
      scope='Finite original-face walk checks, separate from Lean. Regular endpoint objectives are inputs; original-facet complexity and arbitrary-vertex objective construction are not certified.'),saved


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',required=True,type=Path);args=parser.parse_args()
    report,saved=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['dependency_sha256']=hashlib.sha256(Path(sweep.__file__).read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    for name,o in [('exact-tests.json',report),('fixtures.json',saved)]:
        (args.out/name).write_text(json.dumps(sweep.encode(o),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
