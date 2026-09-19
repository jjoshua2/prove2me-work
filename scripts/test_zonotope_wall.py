#!/usr/bin/env python3
"""Exact supporting checks for original zonotope support faces. Not Lean extraction."""
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random


def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(a,x): return tuple(a*b for b in x)
def dot(x,y): return sum((a*b for a,b in zip(x,y)),Q(0))
def point(w,t,d):
    out=(Q(0),)*d
    for a,x in zip(t,w): out=add(out,scale(a,x))
    return out


def rank(rows,d):
    A=[list(x) for x in rows];r=0
    for j in range(d):
        p=next((k for k in range(r,len(A)) if A[k][j]),None)
        if p is None: continue
        A[r],A[p]=A[p],A[r];v=A[r][j];A[r]=[a/v for a in A[r]]
        for k in range(len(A)):
            if k!=r:
                v=A[k][j];A[k]=[a-v*b for a,b in zip(A[k],A[r])]
        r+=1
        if r==len(A):break
    return r


def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def hull(points):
    s=sorted(set(points))
    if len(s)<2:return s
    lo=[];hi=[]
    for p in s:
        while len(lo)>1 and cross(sub(lo[-1],lo[-2]),sub(p,lo[-1]))<=0:lo.pop()
        lo.append(p)
    for p in reversed(s):
        while len(hi)>1 and cross(sub(hi[-1],hi[-2]),sub(p,hi[-1]))<=0:hi.pop()
        hi.append(p)
    return lo[:-1]+hi[:-1]


def on_segment(x,u,v):
    D=sub(v,u);j=next((i for i,a in enumerate(D) if a),None)
    if j is None:return x==u
    t=(x[j]-u[j])/D[j]
    return 0<=t<=1 and x==add(u,scale(t,D))


def certificate(w,f):
    d=len(f);a=[dot(f,x) for x in w]
    tied=[i for i,x in enumerate(w) if a[i]==0 and any(x)]
    if not tied:raise ValueError('zero-dimensional face')
    j=tied[0];D=w[j];k=next(k for k,b in enumerate(D) if b)
    c=[x[k]/D[k] if a[i]==0 else Q(0) for i,x in enumerate(w)]
    if any(a[i]==0 and x!=scale(c[i],D) for i,x in enumerate(w)):raise ValueError('higher-dimensional face')
    low=[Q(c[i]<0) if a[i]==0 else Q(a[i]>0) for i in range(len(w))]
    high=[Q(c[i]>0) if a[i]==0 else Q(a[i]>0) for i in range(len(w))]
    return dict(w=w,f=f,j=j,c=c,low=low,high=high,
                u=point(w,low,d),v=point(w,high,d),mass=sum(abs(c[i]) for i in range(len(w)) if a[i]==0))


def audit(rec):
    w=[tuple(map(Q,x)) for x in rec['w']];f=tuple(map(Q,rec['f']));d=len(f);m=len(w)
    if any(len(x)!=d for x in w):raise ValueError('dimension mismatch')
    j=rec['j'];c=list(map(Q,rec['c']));low=list(map(Q,rec['low']));high=list(map(Q,rec['high']))
    if not isinstance(j,int) or not 0<=j<m or any(len(t)!=m for t in [c,low,high]):raise ValueError('coefficient shape')
    if not any(w[j]) or dot(f,w[j])!=0:raise ValueError('nonzero tied witness required')
    a=[dot(f,x) for x in w]
    if any(a[i]==0 and x!=scale(c[i],w[j]) for i,x in enumerate(w)):raise ValueError('false collinearity')
    if low!=[Q(c[i]<0) if a[i]==0 else Q(a[i]>0) for i in range(m)]:raise ValueError('wrong lower endpoint')
    if high!=[Q(c[i]>0) if a[i]==0 else Q(a[i]>0) for i in range(m)]:raise ValueError('wrong upper endpoint')
    u=tuple(map(Q,rec['u']));v=tuple(map(Q,rec['v']));mass=Q(rec['mass'])
    if u!=point(w,low,d) or v!=point(w,high,d):raise ValueError('endpoint sum')
    if mass!=sum(abs(c[i]) for i in range(m) if a[i]==0) or not mass>0:raise ValueError('width')
    if sub(v,u)!=scale(mass,w[j]):raise ValueError('displacement')
    M=sum(max(Q(0),b) for b in a)
    if dot(f,u)!=M or dot(f,v)!=M:raise ValueError('support')
    return dict(generators=m,dimension=d,tied=sum(b==0 for b in a),displacement_identities=d)


def encode(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x


def run():
    rng=random.Random(312);models=[];tot=Counter();saved=[]
    cases=[(0,[]),(0,[(),()]),(1,[]),(1,[(0,),(1,),(-2,),(1,)]),
           (2,[]),(2,[(0,0),(1,0),(-2,0),(1,0)]),
           (2,[(1,0),(0,1),(1,1)]),(2,[(1,0),(0,1),(0,0),(1,0),(0,-2)]),
           (3,[(1,0,0),(0,1,0),(0,0,1),(1,1,0)]),
           (3,[(0,1,0),(0,-3,0),(1,0,1),(0,0,0)])]
    for d in [1,2,3,4]:
        for m in range(1,8):
            for _ in range(2):
                w=[tuple(Q(rng.randrange(-2,3)) for _ in range(d)) for i in range(m)]
                if m>=3:w[-1]=scale(Q(-2),w[0])
                if m>=5:w[-2]=(Q(0),)*d
                cases.append((d,w))
    for model,(d,w0) in enumerate(cases):
        w=[tuple(map(Q,x)) for x in w0];m=len(w)
        reps=[(bits,point(w,bits,d)) for bits in product([Q(0),Q(1)],repeat=m)]
        vertices=set(x for _,x in reps);fs={(Q(0),)*d}
        for _ in range(14):fs.add(tuple(Q(rng.randrange(-3,4)) for i in range(d)))
        if d==2:
            fs.update((x[1],-x[0]) for x in w)
            fs.update((-x[1],x[0]) for x in w)
        if d==3:
            fs.update((x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0]) for x in w for y in w)
        stat=Counter();H=hull(vertices) if d==2 else None;found_edges=set()
        for f in sorted(fs):
            a=[dot(f,x) for x in w];M=sum(max(Q(0),b) for b in a)
            F={x for x in vertices if dot(f,x)==M}
            assert F
            base=next(iter(F));actual_rank=rank([sub(x,base) for x in F],d)
            tied_rank=rank([x for i,x in enumerate(w) if a[i]==0],d)
            assert actual_rank==tied_rank
            stat['objectives']+=1;stat['face_rank_'+str(actual_rank)]+=1
            for t,x in reps:
                fixed=all(a[i]==0 or t[i]==int(a[i]>0) for i in range(m))
                assert (dot(f,x)==M)==fixed;stat['representation_saturation']+=1
            for _ in range(3):
                t=[Q(rng.randrange(5),4) for i in range(m)];x=point(w,t,d)
                fixed=all(a[i]==0 or t[i]==int(a[i]>0) for i in range(m))
                assert dot(f,x)<=M and (dot(f,x)==M)==fixed;stat['rational_saturation']+=1
            if actual_rank==1:
                rec=certificate(w,f);audit(rec);u,v=rec['u'],rec['v']
                assert u!=v and u in F and v in F and all(on_segment(x,u,v) for x in F)
                stat['face_point_segment_checks']+=len(F);stat['edge_faces']+=1
                if d==2:
                    assert u in H and v in H
                    assert len(H)==2 or (H.index(u)-H.index(v))%len(H) in (1,len(H)-1)
                    found_edges.add(tuple(sorted([u,v])))
                if len(saved)<22 and (any(not any(x) for x in w) or actual_rank<d):saved.append(encode(rec))
            else:
                try:certificate(w,f)
                except ValueError:stat['correct_nonedge_rejections']+=1
                else:raise AssertionError('accepted higher or zero dimensional face')
        if d==2 and len(H)>=2:
            expected={tuple(sorted([x,y])) for x,y in zip(H,H[1:]+H[:1])}
            assert found_edges==expected
            stat['complete_planar_edges']+=len(expected)
        tot.update(stat);models.append(dict(model=model,dimension=d,generators=m,cube_points=len(reps),distinct_sums=len(vertices),**stat))
    high=[]
    for d in [2,8,16,32,64]:
        f=(Q(1),)+(Q(0),)*(d-1);D=(Q(0),Q(1))+(Q(0),)*(d-2)
        w=[scale(c,D) for c in [Q(1),Q(-2),Q(3,2),Q(0),Q(1)]]
        w += [tuple([Q(i)]+[Q(rng.randrange(-3,4),5) for _ in range(d-1)]) for i in [-3,-1,1,2,3]]
        rec=certificate(w,f);audit(rec);saved.append(encode(rec))
        # Explicit fully tied coefficient variation; all frozen indices unchanged.
        for _ in range(20):
            t=[Q(rng.randrange(9),8) if dot(f,x)==0 else Q(dot(f,x)>0) for x in w]
            assert on_segment(point(w,t,d),rec['u'],rec['v'])
        high.append(dict(dimension=d,generators=len(w),whole_body_enumerated=False,tied_segment_samples=20))
    # A cube-edge image can be a diagonal leading to an interior point.
    w=[(Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(1))]
    H=hull(point(w,t,2) for t in product([0,1],repeat=3))
    assert (Q(1),Q(1)) not in H
    bad=[];base=next(r for r in saved if len(r['w'])>=3)
    for name,edit in [('wrong endpoint',lambda r:r.update(u=['999']*len(r['f']))),
                     ('zero width',lambda r:r.update(mass='0')),
                     ('noncollinear tied generator',lambda r:r['c'].__setitem__(r['j'],'2')),
                     ('missing coefficient',lambda r:r['low'].pop()),
                     ('wrong lower sign',lambda r:r['low'].__setitem__(r['j'],'1'))]:
        c=deepcopy(base);edit(c)
        try:audit(c)
        except (ValueError,AssertionError,IndexError):bad.append(name)
        else:raise AssertionError('forged certificate passed')
    original=(certificate,hull,rank)
    def forbidden(*a,**k):raise AssertionError('discovery during audit')
    globals().update(certificate=forbidden,hull=forbidden,rank=forbidden)
    try:
        for r in saved:audit(r)
    finally:globals().update(zip(('certificate','hull','rank'),original))
    return dict(status='PASS',totals=dict(tot),models=models,selected_high=high,
                saved_records=len(saved),discovery_disabled=True,rejected=bad,
                countercontrol='A projected cube-edge endpoint is interior to the actual hexagon.',
                scope='Exact finite support-face and edge checks, not Lean extraction, path bounds, or a verified JSON parser.'),saved


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
    report,fixtures=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,x in [('exact-tests.json',report),('fixtures.json',fixtures)]:
        (a.out/name).write_text(json.dumps(encode(x),indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['totals'],sort_keys=True))
if __name__=='__main__':main()
