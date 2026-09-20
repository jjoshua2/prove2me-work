#!/usr/bin/env python3
"""Exact finite checks of a Lean candidate; not Lean verification or extracted code."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random


def dot(x,y): return sum((a*b for a,b in zip(x,y)), Q(0))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def direction(x):
    a=next((a for a in x if a),None)
    return None if a is None else tuple(Q(b)/a for b in x)

def hull(points):
    p=sorted(set(points))
    if len(p)<=1:return p
    def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    lo=[];hi=[]
    for x in p:
        while len(lo)>=2 and cross(lo[-2],lo[-1],x)<=0:lo.pop()
        lo.append(x)
    for x in reversed(p):
        while len(hi)>=2 and cross(hi[-2],hi[-1],x)<=0:hi.pop()
        hi.append(x)
    return lo[:-1]+hi[:-1]

def table(w):
    out={}
    for bits in product((0,1),repeat=len(w)):
        x=tuple(sum((b*v[j] for b,v in zip(bits,w)),Q(0)) for j in range(2))
        out.setdefault(x,[]).append(bits)
    return out

def regular(w):
    for t in range(1,1000):
        f=(Q(1),Q(t))
        if all(direction(v) is None or dot(f,v) for v in w):return f
    raise RuntimeError('search exhausted')

def support_edge(H,a,b):
    if len(H)==2:
        D=sub(b,a);return (D[1],-D[0])
    i,j=H.index(a),H.index(b)
    if (i+1)%len(H)!=j:a,b=b,a
    D=sub(b,a);return (D[1],-D[0])

def make_record(w,H,T,f,selected,walk):
    # Choose feasible coefficient representations; zero coordinates may differ.
    coeff=[T[x][i%len(T[x])] for i,x in enumerate(walk)]
    return dict(w=w,f=f,selected=selected,vertices=walk,coefficients=coeff,
                objectives=[support_edge(H,a,b) for a,b in zip(walk,walk[1:])])

def audit(c):
    w=[tuple(map(Q,x)) for x in c['w']];f=tuple(map(Q,c['f']));selected=c['selected']
    V=[tuple(map(Q,x)) for x in c['vertices']]
    S=[tuple(map(Q,x)) for x in c['coefficients']]
    G=[tuple(map(Q,x)) for x in c['objectives']]
    ds=[direction(w[i]) for i in selected]
    if any(d is None for d in ds) or len(ds)!=len(set(ds)):raise ValueError('selected directions')
    if any(direction(x) is not None and not dot(f,x) for x in w):raise ValueError('regular objective')
    if len(V)!=len(S) or len(G)+1!=len(V):raise ValueError('record length')
    u=tuple(sum((x[j] for x in w if dot(f,x)>0),Q(0)) for j in range(2))
    v=tuple(sum((x[j] for x in w if dot(f,x)<0),Q(0)) for j in range(2))
    if V[0]!=u or V[-1]!=v:raise ValueError('opposite endpoints')
    T=table(w);pts=set(T);count=Counter()
    for x,s in zip(V,S):
        if len(s)!=len(w) or any(not 0<=a<=1 for a in s):raise ValueError('feasibility')
        if tuple(sum((a*z[j] for a,z in zip(s,w)),Q(0)) for j in range(2))!=x:raise ValueError('representation')
    changed={i:[] for i in selected}
    for k,(a,b,g) in enumerate(zip(V,V[1:],G)):
        if a==b:raise ValueError('stationary edge')
        cap=sum((max(Q(0),dot(g,x)) for x in w),Q(0))
        face={x for x in pts if dot(g,x)==cap}
        if dot(g,a)!=cap or dot(g,b)!=cap:raise ValueError('not supporting')
        D=sub(b,a);jj=next(i for i,x in enumerate(D) if x)
        for x in face:
            t=(x[jj]-a[jj])/D[jj]
            if not 0<=t<=1 or tuple(a[j]+t*D[j] for j in range(2))!=x:raise ValueError('whole face not edge')
        moving=[i for i in selected if S[k][i]!=S[k+1][i]]
        if len(moving)>1:raise ValueError('two selected directions on edge')
        for i in moving:
            if dot(g,w[i]):raise ValueError('changed coordinate not tied')
            changed[i].append(k)
        count['edge_occurrences']+=1;count['face_point_checks']+=len(face)
    if any(S[0][i]==S[-1][i] or not changed[i] for i in selected):raise ValueError('missing required change')
    assigned=[changed[i][0] for i in selected]
    if len(set(assigned))!=len(assigned):raise ValueError('noninjective assignment')
    if len(selected)>len(G):raise ValueError('lower bound')
    count.update(routes=1,selected_direction_assignments=len(selected),zero_length_routes=int(not G),
                 repeated_changes=sum(max(0,len(v)-1) for v in changed.values()))
    return count

def run():
    rng=random.Random(317)
    systems=[[],[(0,0)],[(1,0)],[(1,0),(2,0),(-3,0)],[(1,0),(0,1)],
             [(1,0),(0,1),(1,1)],[(1,0),(0,1),(-1,0),(0,0)]]
    for _ in range(23):
        w=[tuple(rng.randrange(-3,4) for _ in range(2)) for _ in range(rng.randrange(2,8))]
        if len(w)>3:w[-1]=tuple(-x for x in w[0])
        systems.append(w)
    totals=Counter();saved=[];models=[]
    for n,ww in enumerate(systems):
        w=[tuple(map(Q,x)) for x in ww];T=table(w);H=hull(T);f=regular(w)
        directions={}
        for i,x in enumerate(w):
            d=direction(x)
            if d is not None:directions.setdefault(d,i)
        selected=list(directions.values())
        u=tuple(sum((x[j] for x in w if dot(f,x)>0),Q(0)) for j in range(2))
        v=tuple(sum((x[j] for x in w if dot(f,x)<0),Q(0)) for j in range(2))
        i,j=H.index(u),H.index(v);N=len(H)
        if N>1:assert min((j-i)%N,(i-j)%N)==len(selected)
        walks=[]
        for sign in (1,-1):
            L=((j-i)*sign)%N
            walks.append([H[(i+sign*k)%N] for k in range(L+1)])
        if N>1:walks.append([u,H[(i+1)%N],u]+walks[0][1:])
        for walk in walks:
            for sel in [selected,selected[::2],[]]:
                rec=make_record(w,H,T,f,sel,walk);totals.update(audit(rec))
                if sel==selected and len(saved)<45:saved.append(rec)
        totals['models']+=1;totals['hull_vertices']+=N
        totals['zero_generators']+=sum(direction(x) is None for x in w)
        models.append(dict(model=n,generators=len(w),distinct_directions=len(selected),vertices=N,
                           antipodal_distance=min((j-i)%N,(i-j)%N)))
    # All ordered vertex-pair directions of the d-cube. Not a graph enumeration.
    cubes=[]
    for d in range(1,9):
        C=list(product((0,1),repeat=d));D=set()
        for a in C:
            for b in C:
                z=tuple(y-x for x,y in zip(a,b));q=next((x for x in z if x),None)
                if q is not None:D.add(tuple(x*q for x in z))
        assert len(D)==(3**d-1)//2
        selected={ (1,)+bits for bits in product((0,1),repeat=d-1)}
        assert selected<=D and len(selected)==2**(d-1)
        cubes.append(dict(dimension=d,original_cube_rows=2*d,ordered_pair_slots=4**d,
                          distinct_nonzero_directions=len(D),selected_binary_directions=len(selected),
                          complete_zonotope_graph_enumerated=False,Lean_instance_verified=False))
    # Replay without hull or regular-objective construction.
    oldh,oldr=hull,regular
    def fail(*a,**k):raise AssertionError('construction during replay')
    try:
        globals()['hull']=fail;globals()['regular']=fail
        for c in saved:audit(c)
    finally:globals()['hull']=oldh;globals()['regular']=oldr
    base=next(c for c in saved if len(c['selected'])>=2);bad=[]
    edits=[('false support',lambda c:c['objectives'].__setitem__(0,(Q(0),Q(0)))),
           ('parallel double count',lambda c:c['selected'].append(c['selected'][0])),
           ('wrong endpoint',lambda c:c['vertices'].__setitem__(-1,(Q(999),Q(999)))),
           ('wrong coefficient',lambda c:c['coefficients'].__setitem__(0,(Q(2),)*len(c['w']))),
           ('missing step',lambda c:c['objectives'].pop())]
    for name,edit in edits:
        c=deepcopy(base);edit(c)
        try:audit(c)
        except (ValueError,AssertionError,IndexError):bad.append(name)
        else:raise AssertionError('accepted forgery '+name)
    return dict(status='PASS',totals=dict(totals),models=models,cube_direction_checks=cubes,
                saved_records=len(saved),constructors_disabled=True,rejected=bad,
                scope='Supporting exact arithmetic; not Lean verification, extraction, or a universal H-completion lower bound.'),saved

def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    r,s=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,x in [('exact-tests.json',r),('fixtures.json',s)]:
        (a.out/name).write_text(json.dumps(encode(x),sort_keys=True,indent=2)+'\n')
    print(json.dumps(r['totals'],sort_keys=True))
if __name__=='__main__':main()
