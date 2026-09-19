#!/usr/bin/env python3
"""Exact finite checks for the completion construction; not Lean or extracted code."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, random


def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(a,x): return tuple(a*b for b in x)
def dot(x,y): return sum((a*b for a,b in zip(x,y)),F(0))
def cross(x,y): return x[0]*y[1]-x[1]*y[0]
def hull(points):
    pts=sorted(set(points))
    if len(pts)<2:return pts
    lo=[];hi=[]
    for p in pts:
        while len(lo)>1 and cross(sub(lo[-1],lo[-2]),sub(p,lo[-1]))<=0:lo.pop()
        lo.append(p)
    for p in reversed(pts):
        while len(hi)>1 and cross(sub(hi[-1],hi[-2]),sub(p,hi[-1]))<=0:hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]


def rows(poly):
    if len(poly)==1:
        p=poly[0]
        return [((F(1),F(0)),p[0]),((F(-1),F(0)),-p[0]),
                ((F(0),F(1)),p[1]),((F(0),F(-1)),-p[1])]
    if len(poly)==2:
        x,y=poly;d=sub(y,x);a=(d[1],-d[0])
        return [(a,dot(a,x)),(scale(-1,a),-dot(a,x)),(d,dot(d,y)),(scale(-1,d),-dot(d,x))]
    return [((sub(y,x)[1],-sub(y,x)[0]),dot((sub(y,x)[1],-sub(y,x)[0]),x))
            for x,y in zip(poly,poly[1:]+poly[:1])]


def from_rows(H):
    pts=[]
    for (a,b),(c,d) in combinations(H,2):
        det=cross(a,c)
        if not det:continue
        x=((b*c[1]-a[1]*d)/det,(a[0]*d-b*c[0])/det)
        if all(dot(h,x)<=k for h,k in H):pts.append(x)
    return hull(pts)


def point(v,t):
    z=tuple(F(0) for _ in v[0])
    for (i,j),a in t.items():z=add(z,add(scale(a,v[i]),scale(1-a,v[j])))
    return z


def witness(v,f):
    k=max(range(len(v)),key=lambda i:dot(f,v[i]))
    t={(i,j):F(1 if i==k or dot(f,v[i])>=dot(f,v[j]) else 0)
       for i in range(len(v)) for j in range(len(v))}
    z=point(v,t);q=sub(z,v[k])
    return dict(v=v,f=f,k=k,t=[[i,j,str(a)] for (i,j),a in t.items()],q=q,z=z)


def audit(record):
    v=[tuple(map(F,x)) for x in record['v']];f=tuple(map(F,record['f']))
    k=record['k'];q=tuple(map(F,record['q']));z=tuple(map(F,record['z']))
    t={(i,j):F(a) for i,j,a in record['t']}
    n=len(v)
    if not n or not 0<=k<n:raise ValueError('nonempty/index')
    if set(t)!=set(product(range(n),repeat=2)):raise ValueError('all represented pairs required')
    if any(a<0 or a>1 for a in t.values()):raise ValueError('outside segment')
    if point(v,t)!=z or add(v[k],q)!=z:raise ValueError('source identity')
    if any(dot(f,x)>dot(f,v[k]) for x in v):raise ValueError('maximal generator')
    if dot(f,z)!=sum(max(dot(f,v[i]),dot(f,v[j])) for i,j in t):raise ValueError('sum support')
    for i in range(n):
        if t[k,i]!=1:raise ValueError('incident choice must be one')
        updated=dict(t);updated[k,i]=F(0)
        if point(v,updated)!=add(q,v[i]):raise ValueError('replacement identity')
    return n,n*n


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x


def run():
    rng=random.Random(311);counts=Counter();models=[];saved=[]
    cases=[[(0,0)],[(2,-3),(2,-3)],[(0,0),(1,0)],[(0,0),(1,0),(0,1)],
           [(0,0),(2,0),(2,2),(0,2),(1,1)],[(0,0),(1,1),(2,2),(1,1)]]
    for n in range(1,9):
        for _ in range(5):cases.append([(F(rng.randrange(-8,9),3),F(rng.randrange(-8,9),5)) for _ in range(n)])
    for num,raw in enumerate(cases):
        v=[tuple(map(F,p)) for p in raw];n=len(v);P=hull(v)
        Z=[(F(0),F(0))]
        for i,j in product(range(n),repeat=2):Z=hull([add(x,y) for x in Z for y in [v[i],v[j]]])
        H=rows(Z);HQ=[(a,b-max(dot(a,p) for p in v)) for a,b in H];Q=from_rows(HQ)
        if not Q:raise AssertionError('empty erosion')
        if hull([add(p,q) for p in P for q in Q])!=Z:raise AssertionError('whole-set completion failed')
        fs=[a for a,b in H]+[(F(0),F(0))]+[tuple(F(rng.randrange(-7,8)) for _ in range(2)) for _ in range(8)]
        stat=Counter()
        for f in fs:
            r=witness(v,f);m,g=audit(r)
            assert all(dot(a,r['q'])<=b for a,b in HQ)
            assert dot(f,r['z'])==max(dot(f,z) for z in Z)
            assert dot(f,r['q'])+max(dot(f,p) for p in P)==max(dot(f,z) for z in Z)
            stat['support_witnesses']+=1;stat['replacement_identities']+=m;stat['segment_checks']+=g
        counts.update(stat);counts['models']+=1;counts['Z_vertices']+=len(Z);counts['Q_vertices']+=len(Q)
        models.append(dict(generators=n,dimension=2,P_vertices=len(P),Z_vertices=len(Z),Q_vertices=len(Q),**stat))
        if num in (0,1,2,3,4,5,10,20,30,40):saved.append(encode(witness(v,fs[-1])))
    high=[]
    for d,n in [(0,1),(0,5),(1,4),(3,4),(4,6),(8,5),(16,6),(32,4),(64,3)]:
        v=[tuple(F(rng.randrange(-8,9),7) for _ in range(d)) for _ in range(n)]
        f=tuple(F(rng.randrange(-8,9)) for _ in range(d));rec=witness(v,f);audit(rec)
        for _ in range(8):
            t={e:F(rng.randrange(9),8) for e in product(range(n),repeat=2)}
            assert dot(f,point(v,t))<=dot(f,rec['z'])
        high.append(dict(dimension=d,generators=n,represented_segments=n*n,replacement_identities=n,full_bodies_enumerated=False))
        saved.append(encode(rec))
    # Audit saved records without invoking the construction or hull/intersection solvers.
    return counts,models,high,saved


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    counts,models,high,saved=run()
    original=(witness,hull,from_rows)
    def forbidden(*args,**kwargs):raise AssertionError('construction disabled')
    globals().update(witness=forbidden,hull=forbidden,from_rows=forbidden)
    try:
        for s in saved:audit(s)
    finally:globals().update(zip(('witness','hull','from_rows'),original))
    from copy import deepcopy
    base=next(x for x in saved if len(x['v'])>2 and len(x['f'])==2);bad=[]
    for name,edit in [('missing pair',lambda c:c['t'].pop()),('wrong translate',lambda c:c.update(q=['999','999'])),
                      ('outside coefficient',lambda c:c['t'][0].__setitem__(2,'2')),('wrong sum point',lambda c:c.update(z=['999','999']))]:
        c=deepcopy(base);edit(c)
        try:audit(c)
        except (ValueError,AssertionError):bad.append(name)
        else:raise AssertionError('forgery accepted')
    report=dict(status='PASS',counts=dict(counts),models=models,selected_high_dimensional=high,saved_replays=len(saved),
      constructors_disabled=True,rejected=bad,source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      scope='Exact rational whole-set polygon checks and selected general-dimensional support witnesses, not Lean verification or edge-route certification.')
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',saved)]:
        (a.out/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
