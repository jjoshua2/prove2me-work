#!/usr/bin/env python3
"""Exact rational regression for the uniform endpoint perturbation theorem.
Python is neither Lean-extracted nor a replacement for the kernel audit.
Small full tuple sums independently check endpoint uniqueness; large factors
use exact component inequalities and do not enumerate the Minkowski graph.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import random

ROOT = Path(__file__).resolve().parents[1]

def require(ok, message):
    if not ok:
        raise ValueError(message)

def rational(x):
    require(type(x) in (int, str) or isinstance(x, Q), 'exact rational input required')
    return Q(x)

def dot(a, b):
    require(len(a) == len(b), 'shape mismatch')
    return sum((x*y for x, y in zip(a,b)), Q(0))

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(s,a): return tuple(s*x for x in a)
def total(points,d): return tuple(sum((p[j] for p in points),Q(0)) for j in range(d))

def parse(data):
    e = tuple(map(rational,data['direction']))
    f = tuple(map(rational,data['normal']))
    d = len(e)
    require(d and any(e) and len(f)==d, 'nonzero common direction required')
    require(dot(e,f)==0, 'normal does not support the direction')
    factors=[]
    for part in data['factors']:
        a=tuple(map(rational,part['left'])); b=tuple(map(rational,part['right']))
        eta=rational(part['length'])
        S=sorted(set(tuple(map(rational,x)) for x in part['points']))
        require(len(a)==len(b)==d and all(len(x)==d for x in S),'factor shape')
        require(a in S and b in S,'endpoint absent from finite presentation')
        require(eta>=0 and b==add(a,scale(eta,e)),'wrong orientation or displacement')
        require(all(dot(f,x)<=dot(f,a) for x in S),'claimed support bound is false')
        factors.append((S,a,b,eta))
    return e,f,factors

def construct(data, transverse):
    e,f,parts=parse(data)
    q=tuple(map(rational,transverse))
    require(len(q)==len(e) and dot(q,e)==1,'coordinate is not normalized')
    radii=[Q(1)]
    for S,a,b,eta in parts:
        for x in S:
            for p in (a,b):
                z=sub(p,x); gap=dot(f,z)
                if gap>0: radii.append(gap/(abs(dot(q,z))+1))
    cert={'coordinate':[str(x) for x in q],'radius':str(min(radii)/2)}
    verify(data,cert)
    return cert

def verify(data,cert):
    e,f,parts=parse(data);d=len(e)
    q=tuple(map(rational,cert['coordinate']));delta=rational(cert['radius'])
    require(len(q)==d and dot(q,e)==1 and delta>0,'invalid normalized coordinate/radius')
    tied=off=0
    for S,a,b,eta in parts:
        for x in S:
            if dot(f,x)==dot(f,a):
                t=dot(q,sub(x,a))
                require(0<=t<=eta and x==add(a,scale(t,e)),'whole support is not the asserted segment')
                tied+=1
            else:
                off+=1
                for p in (a,b):
                    z=sub(p,x);gap=dot(f,z)
                    require(delta*(abs(dot(q,z))+1)<=gap,'radius does not preserve the strict gap')
    # These exact inequalities prove preservation for ALL 0<s<delta, rather
    # than just recording the finitely many samples checked by the regression.
    return {'factors':len(parts),'tied_points':tied,'off_support_points':off}

def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def example(d,m,seed,gap_power=0,dense=False,point_factors=False):
    rng=random.Random(seed)
    e=tuple(Q(j==0) for j in range(d)); q=e
    f=tuple(Q(j==d-1 and d>1) for j in range(d))
    parts=[]
    for i in range(m):
        a=tuple(Q(rng.randrange(-5,6),3) for _ in range(d))
        eta=Q(0) if point_factors or i%5==0 else Q(rng.randrange(1,8),rng.randrange(1,5))
        b=add(a,scale(eta,e));S=[a,b,add(a,scale(eta/3,e)),add(a,scale(2*eta/3,e)),a]
        if d>1:
            for k in range(3):
                x=list(a)
                x[0]+=Q(rng.randrange(-50,51),7)
                for j in range(1,d-1):x[j]+=Q(rng.randrange(-3,4),5)
                x[-1]-=Q(k+1,2**gap_power)
                S.append(tuple(x))
        parts.append({'left':a,'right':b,'length':eta,'points':S})
    if dense and d>1:
        # T=I+u v^T, with v^T u=0, so its inverse is exactly I-u v^T.
        u=[Q(1)]*d;v=[Q(rng.randrange(-4,5),7) for _ in range(d-1)]
        v.append(-sum(v))
        transform=lambda x:add(x,scale(dot(v,x),u))
        dual=lambda c:sub(c,scale(dot(c,u),v))
        shift=tuple(Q(rng.randrange(-3,4),11) for _ in range(d))
        e=transform(e);f=dual(f);q=dual(q)
        for p in parts:
            for k in ['left','right']:p[k]=add(transform(p[k]),shift)
            p['points']=[add(transform(x),shift) for x in p['points']]
    return {'direction':e,'normal':f,'factors':parts},q

def exercise(data,q):
    cert=construct(data,q);report=verify(data,cert)
    e,f,parts=parse(data);d=len(e);delta=Q(cert['radius'])
    checks=tuplechecks=0
    tupcount=1
    for S,*_ in parts:tupcount*=len(S)
    for fraction in [Q(1,2**100),Q(1,7),Q(1,2),Q(7,8)]:
        s=delta*fraction
        for sign,end in [(-1,1),(1,2)]:
            h=add(f,scale(sign*s,q))
            for part in parts:
                S,a,b,eta=part;target=part[end]
                for x in S:
                    require((x==target) or dot(h,x)<dot(h,target),'strict component comparison failed')
                    checks+=1
            if tupcount<=4096:
                endpoint=total([p[end] for p in parts],d)
                for tup in product(*(p[0] for p in parts)):
                    z=total(tup,d)
                    require(dot(h,z)<=dot(h,endpoint),'whole-sum bound failed')
                    require(dot(h,z)!=dot(h,endpoint) or z==endpoint,'whole-sum singleton failed')
                    tuplechecks+=1
    return cert,{**report,'component_sample_checks':checks,'full_tuple_comparisons':tuplechecks,
                 'raw_tuple_count':tupcount,'tuple_sums_enumerated':tupcount<=4096}

def main():
    totals={'cases':0,'factors':0,'tied_points':0,'off_support_points':0,'component_sample_checks':0,'full_tuple_comparisons':0}
    fixtures=[]
    cases=[(2,0,1,0,False,False),(1,3,2,0,False,False),(3,4,3,0,False,True)]
    cases += [(2,3,10+p,p,True,False) for p in [8,40,120,240]]
    cases += [(2+j%5,j%6,200+j,j%11,j%2==0,False) for j in range(120)]
    cases += [(12,64,991,160,True,False)]
    for index,args in enumerate(cases):
        data,q=example(*args);cert,r=exercise(data,q)
        totals['cases']+=1
        for k in totals:
            if k!='cases':totals[k]+=r[k]
        if index<7 or index==len(cases)-1:fixtures.append({'input':serial(data),'certificate':cert,'result':r})
    data,q=example(2,2,420,20,False,False);c=construct(data,q);bad=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):bad.append(name)
        else:raise AssertionError('invalid certificate accepted: '+name)
    t=deepcopy(c);t['radius']='0';reject('zero_radius',lambda:verify(data,t))
    t=deepcopy(c);t['radius']='100';reject('oversized_radius',lambda:verify(data,t))
    t=deepcopy(c);t['coordinate']=['0','0'];reject('zero_coordinate',lambda:verify(data,t))
    t=deepcopy(c);t['coordinate']=['-1','0'];reject('reversed_coordinate',lambda:verify(data,t))
    x=deepcopy(data);x['direction']=[0,0];reject('zero_direction',lambda:verify(x,c))
    x=deepcopy(data);x['normal']=[1,0];reject('unsupported_common_direction',lambda:verify(x,c))
    x=deepcopy(data);x['factors'][1]['length']=-1;reject('negative_length',lambda:verify(x,c))
    x=deepcopy(data);x['factors'][1]['right']=list(x['factors'][1]['right']);x['factors'][1]['right'][0]+=1
    reject('wrong_endpoint_displacement',lambda:verify(x,c))
    x=deepcopy(data);x['factors'][1]['points']=[x['factors'][1]['left']];reject('missing_right_endpoint',lambda:verify(x,c))
    x=deepcopy(data);a=x['factors'][0]['left'];x['factors'][0]['points'].append((a[0],a[1]+1))
    reject('point_above_support',lambda:verify(x,c))
    x=deepcopy(data);a=x['factors'][0]['left'];x['factors'][0]['points'].append((a[0]+1,a[1]))
    reject('extra_point_on_zero_length_support',lambda:verify(x,c))
    x=deepcopy(data);a=x['factors'][1]['right'];x['factors'][1]['points'].append((a[0]+1,a[1]))
    reject('point_beyond_support_segment',lambda:verify(x,c))
    extra,qextra=example(3,1,11,0,False,False)
    cextra=construct(extra,qextra)
    a=extra['factors'][0]['left']
    extra['factors'][0]['points'].append((a[0],a[1]+1,a[2]))
    reject('higher_dimensional_support_face',lambda:verify(extra,cextra))
    t=deepcopy(c);t['radius']=0.01;reject('floating_radius',lambda:verify(data,t))
    path=ROOT/'research/publication_packets/uniform_bridge_endpoint_exposers/solution.lean'
    out={'status':'PASS','scope':'Exact rational regression; not a Lean verdict, JSON kernel evaluation, or ordinary-edge route count.',
         'totals':totals,'rejected':len(bad),'negative_cases':bad,'fixtures':fixtures,
         'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
         'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'research/UNIFORM_ENDPOINT_EXPOSERS_TESTS.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
    print(json.dumps({'totals':totals,'rejected':len(bad),'last':fixtures[-1]['result']},indent=2))

if __name__=='__main__':main()
