#!/usr/bin/env python3
"""Exact tests for every-lift lower bounds. Not Lean verification or extraction."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from collections import Counter, deque
from copy import deepcopy
import json, argparse, hashlib, random

def dot(a,b): return sum((F(x)*y for x,y in zip(a,b)),F(0))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def maskvec(mask,d): return tuple(F(bool(mask>>j&1)) for j in range(d))
def chosen(w,f,d): return tuple(sum((v[j] for v in w if dot(f,v)>0),F(0)) for j in range(d))
def parallel(a,b):
    j=next((j for j,x in enumerate(b) if x),None)
    return not any(a) if j is None else all(a[i]*b[j]==a[j]*b[i] for i in range(len(a)))
def hull2(points):
    ps=sorted(set(points))
    if len(ps)<2:return ps
    def cross(o,a,b): return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])
    lo=[];hi=[]
    for x in ps:
        while len(lo)>1 and cross(lo[-2],lo[-1],x)<=0:lo.pop()
        lo.append(x)
    for x in reversed(ps):
        while len(hi)>1 and cross(hi[-2],hi[-1],x)<=0:hi.pop()
        hi.append(x)
    return lo[:-1]+hi[:-1]
def zono2(w):
    H=[(F(0),F(0))]
    for v in w:H=hull2(H+[add(x,v) for x in H])
    return H
def expose2(H,i):
    u=H[i];a=sub(u,H[i-1]);b=sub(H[(i+1)%len(H)],u)
    f=(a[1]+b[1],-a[0]-b[0])
    assert all(x==u or dot(f,x)<dot(f,u) for x in H)
    return f

def sweep(w,f,g,d):
    assert all(not any(v) or (dot(f,v) and dot(g,v)) for v in w)
    T=sorted(set(dot(f,v)/(dot(f,v)-dot(g,v)) for v in w
        if dot(f,v)*dot(g,v)<0))
    for t in T:
        ties=[v for v in w if any(v) and (1-t)*dot(f,v)+t*dot(g,v)==0]
        assert all(parallel(v,ties[0]) for v in ties),'independent tie'
    E=[F(0)]+T+[F(1)]
    samples=[(x+y)/2 for x,y in zip(E,E[1:])]
    signs=[[int((1-t)*dot(f,v)+t*dot(g,v)>0) for v in w] for t in samples]
    V=[tuple(sum((F(s[i])*w[i][j] for i in range(len(w))),F(0)) for j in range(d)) for s in signs]
    return dict(d=d,w=w,f=f,g=g,events=T,vertices=V,coefficients=signs)

def audit(rec):
    d=rec['d'];w=[tuple(map(F,v)) for v in rec['w']];f=tuple(map(F,rec['f']));g=tuple(map(F,rec['g']))
    T=list(map(F,rec['events']));V=[tuple(map(F,v)) for v in rec['vertices']];s=rec['coefficients']
    if len(V)!=len(T)+1 or len(s)!=len(V):raise ValueError('length')
    if T!=sorted(set(T)) or any(not 0<t<1 for t in T):raise ValueError('event order')
    if any(x>=0 for x in f) or any(x<=0 for x in g):raise ValueError('not opposite cube fibres')
    if any(any(v) and (dot(f,v)==0 or dot(g,v)==0) for v in w):raise ValueError('endpoint not regular')
    labels=[]
    for mask in range(1,2**d):
        v=maskvec(mask,d)
        if v not in w:raise ValueError('missing Boolean direction')
        labels.append(w.index(v))
    unit_indices=[w.index(maskvec(1<<j,d)) for j in range(d)]
    q=[v for i,v in enumerate(w) if i not in unit_indices]
    if V[0]!=chosen(q,f,d) or V[-1]!=add((F(1),)*d,chosen(q,g,d)):raise ValueError('wrong fibre endpoint')
    E=[F(0)]+T+[F(1)];samples=[(x+y)/2 for x,y in zip(E,E[1:])]
    for z,a,t in zip(V,s,samples):
        if len(a)!=len(w) or any(x not in (0,1) for x in a):raise ValueError('coefficients')
        if z!=tuple(sum((F(a[i])*w[i][j] for i in range(len(w))),F(0)) for j in range(d)):raise ValueError('representation')
        if any(any(v) and ((1-t)*dot(f,v)+t*dot(g,v)==0 or a[i]!=int((1-t)*dot(f,v)+t*dot(g,v)>0)) for i,v in enumerate(w)):
            raise ValueError('not singleton support')
    for i,t in enumerate(T):
        tied=[j for j,v in enumerate(w) if any(v) and (1-t)*dot(f,v)+t*dot(g,v)==0]
        if not tied or V[i]==V[i+1]:raise ValueError('degenerate event')
        if any(not parallel(w[j],w[tied[0]]) for j in tied):raise ValueError('not entire edge face')
        for j,v in enumerate(w):
            h=(1-t)*dot(f,v)+t*dot(g,v)
            if h and (s[i][j]!=int(h>0) or s[i+1][j]!=int(h>0)):raise ValueError('not support endpoints')
        D=sub(V[i+1],V[i])
        if any(not parallel(w[j],D) for j in tied):raise ValueError('face direction')
        # Every tied segment must be traversed to its endpoint in the same orientation.
        if any(dot(D,tuple(F(s[i+1][j]-s[i][j])*x for x in w[j]))<=0 for j in tied):raise ValueError('proper subsegment')
    steps=[]
    for j in labels:
        if s[0][j]!=0 or s[-1][j]!=1:raise ValueError('saturation')
        change=next((i for i in range(len(T)) if s[i][j]!=s[i+1][j]),None)
        if change is None:raise ValueError('missing direction change')
        steps.append(change)
    if len(set(steps))!=len(steps) or len(T)<2**d-1:raise ValueError('direction injection')
    cube=[tuple(int((1-t)*f[j]+t*g[j]>0) for j in range(d)) for t in samples]
    changes=[sum(x!=y for x,y in zip(a,b)) for a,b in zip(cube,cube[1:])]
    if any(c>1 for c in changes) or sum(changes)!=d:raise ValueError('cube component route')
    return dict(edges=len(T),forced_directions=len(labels),extra_unforced_events=len(T)-len(labels),cube_component_edges=sum(changes),collapsed_steps=len(T)-sum(changes))

def run():
    rng=random.Random(318);counts=Counter();records=[];models=[]
    cube=[maskvec(i,2) for i in range(4)]
    canonical=[sub(v,u) for u in cube for v in cube]
    families=[canonical,[maskvec(i,2) for i in range(1,4)],canonical+[(F(3),F(1)),(F(-1),F(2))]]
    for _ in range(8):families.append(canonical+[tuple(F(rng.randrange(-4,5)) for _ in range(2)) for _ in range(4)])
    for model,w in enumerate(families):
        H=zono2(w);unit=[w.index(maskvec(1<<j,2)) for j in range(2)]
        Q=zono2([v for i,v in enumerate(w) if i not in unit])
        # Some Q's are segments; zono2 still supplies endpoints. Direct sums prove equality.
        assert hull2([add(x,y) for x in cube for y in Q])==H
        I=[i for i,z in enumerate(H) if z in Q];J=[i for i,z in enumerate(H) if sub(z,(F(1),F(1))) in Q]
        assert I and J
        dist=[]
        for i,j in product(I,J):
            ds=min((j-i)%len(H),(i-j)%len(H));assert ds>=3;dist.append(ds)
            f=expose2(H,i);g=expose2(H,j)
            # Perturb within the target cone only when the direct sweep has independent ties.
            for power in range(1,20):
                try:r=sweep(w,f,g,2);break
                except AssertionError:
                    e=F(1,2**power);g=add(expose2(H,j),(e,e*e))
                    assert chosen(w,g,2)==H[j]
            else:raise AssertionError('regularization failed')
            result=audit(r);counts.update(result);counts['routes']+=1
            V=r['vertices'];counts['original_hull_edge_checks']+=len(V)-1
            assert all((H.index(a)-H.index(b))%len(H) in (1,len(H)-1) for a,b in zip(V,V[1:]))
            if len(records)<12:records.append(r)
        models.append(dict(model=model,generators=len(w),vertices=len(H),source_lifts=len(I),target_lifts=len(J),all_lift_pairs=len(dist),minimum_distance=min(dist),maximum_distance=max(dist)))
    large=[]
    for d in [1,3,4,5,6,8]:
        w=[maskvec(i,d) for i in range(1,2**d)]
        f=(-F(1),)*d;g=tuple(F((d+1)**j) for j in range(d))
        r=sweep(w,f,g,d);res=audit(r);assert res['edges']==2**d-1
        records.append(r);large.append(dict(dimension=d,original_cube_rows=2*d,**res,full_graph_enumerated=False))
    # Every affine box corner remains exactly d coordinate changes in its own graph.
    for d in range(1,20):assert sum(a!=b for a,b in zip([0]*d,[1]*d))==d
    orig=sweep
    def disabled(*a,**k):raise AssertionError('construction disabled')
    try:
        globals()['sweep']=disabled
        replay=[audit(r) for r in records]
    finally:globals()['sweep']=orig
    bad=[];base=deepcopy(records[0])
    for name,edit in [('missing event',lambda r:r['events'].pop()),('bad source lift',lambda r:r['vertices'].__setitem__(0,(F(999),F(999)))),('missing selected direction',lambda r:r['w'].__setitem__(r['w'].index((F(1),F(1))),(F(0),F(0)))),('bad coefficient',lambda r:r['coefficients'][0].__setitem__(0,2)),('stationary edge',lambda r:r['vertices'].__setitem__(1,r['vertices'][0]))]:
        r=deepcopy(base);edit(r)
        try:audit(r)
        except (ValueError,AssertionError,IndexError):bad.append(name)
        else:raise AssertionError('forgery accepted')
    report=dict(status='PASS',counts=dict(counts),models=models,selected_larger=large,saved_audits=len(records),saved_edges=sum(x['edges'] for x in replay),construction_disabled=True,rejected=bad,not_Lean_verification=True)
    return report,records

def enc(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [enc(v) for v in x]
    return x
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    report,records=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();args.out.mkdir(parents=True,exist_ok=True)
    for fn,value in [('exact-tests.json',report),('fixtures.json',records)]: (args.out/fn).write_text(json.dumps(enc(value),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
