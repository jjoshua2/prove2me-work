#!/usr/bin/env python3
"""Exact rational controls for the ordered minimal-nonface proof packet.
This does not compile Lean. The checker independently evaluates ORIGINAL rows.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
from math import prod
import hashlib, json, random

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/publication_packets/moment_ordered_minimal_nonfaces'

def require(ok, text):
    if not ok: raise ValueError(text)

def rat(x):
    require(type(x) in (int,str,Q), 'exact rational input required')
    return Q(x)

def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

def validate(k,a,b):
    require(type(k)is int and k>=0,'invalid half-dimension')
    a=list(map(rat,a));m=len(a)
    require(len(set(a))==m,'parameters not injective')
    require(type(b)is list and len(b)==2*k+3 and all(type(i)is int and 0<=i<m for i in b),'invalid chain indices')
    require(all(a[i]<a[j] for i,j in zip(b,b[1:])),'chain not strictly ordered')
    return a

def rows(k,a):
    m=len(a);d=2*k
    mu=[sum(t**j for t in a)/m for j in range(1,d+1)]
    return [[t**j-mu[j-1] for j in range(1,d+1)] for t in a]

def support(k,a,T):
    p=[Q(1)]
    for i in T:
        for _ in range(2):
            out=[Q(0)]*(len(p)+1)
            for j,c in enumerate(p):out[j]-=a[i]*c;out[j+1]+=c
            p=out
    vals=[sum(c*t**j for j,c in enumerate(p)) for t in a]
    h=sum(vals)/len(a);require(h>0,'not a proper positive-average support')
    x=[-(p[j] if j<len(p) else Q(0))/h for j in range(1,2*k+1)]
    return {'tight':sorted(T),'point':x}

def construct(k,a,b,complete=True):
    a=validate(k,a,b);N=b[1::2]
    weights=[Q(1)/prod(a[i]-a[j] for j in b if i!=j) for i in b]
    if complete:
        Ts=[T for s in range(k+1) for T in combinations(sorted(N),s)]
    else:
        Ts=[()] + [tuple(j for j in sorted(N) if j!=i) for i in sorted(N)]
    return {'k':k,'a':a,'b':b,'odd_labels':sorted(N),'weights':weights,
            'complete_proper_subsets':complete,'supports':[support(k,a,T) for T in Ts]}

def verify(c):
    k=c['k'];a=validate(k,c['a'],c['b']);b=c['b'];N=set(b[1::2]);d=2*k
    require(c['odd_labels']==sorted(N) and len(N)==k+1,'wrong alternating set')
    w=list(map(rat,c['weights']));require(len(w)==len(b),'missing weights')
    for pos,(i,wi) in enumerate(zip(b,w)):
        denominator=prod(a[i]-a[j] for j in b if j!=i)
        require(wi*denominator==1,'false barycentric coefficient')
        require((wi<0)==(pos%2==1) and (wi>0)==(pos%2==0),'wrong derived ordered signs')
        require(sum(a[j]>a[i] for j in b)==2*k+2-pos,'wrong count of negative factors')
    for power in range(d+2):
        require(sum(wi*a[i]**power for i,wi in zip(b,w))==0,'false moment annihilation')
    A=rows(k,a);stored=set();inequalities=strict=0
    for p in c['supports']:
        T=p['tight'];require(T==sorted(set(T)) and set(T)<N,'not a proper subset')
        require(tuple(T) not in stored,'duplicate support');stored.add(tuple(T))
        x=list(map(rat,p['point']));require(len(x)==d,'bad witness dimension')
        vals=[sum(ai*xj for ai,xj in zip(row,x)) for row in A]
        require(all(value<=1 and ((value==1)==(i in T)) for i,value in enumerate(vals)),
                'incorrect original-H support witness')
        inequalities+=len(a);strict+=len(a)-len(T)
    wanted={T for s in range(k+1) for T in combinations(sorted(N),s)} if c['complete_proper_subsets'] else {()}|{tuple(j for j in sorted(N) if j!=i) for i in sorted(N)}
    require(stored==wanted,'omitted required proper face')
    # All immediate proper subsets are present even for the large compact test.
    require(all(tuple(j for j in sorted(N) if j!=i) in stored for i in N),'missing maximal proper witness')
    return {'status':'PASS','k':k,'dimension':d,'original_rows':len(a),'selected_chain':len(b),
            'minimal_set_size':len(N),'sign_checks':len(b),'moment_equations':d+2,
            'proper_subsets_checked':len(stored),'original_inequalities':inequalities,'strict_rows':strict}

def main():
    rng=random.Random(287);totals={key:0 for key in ['cases','sign_checks','moment_equations','proper_subsets_checked','original_inequalities','strict_rows','feasible_point_checks','strict_negative_side_checks']};saved=[]
    for k in range(5):
        for m in (2*k+3,2*k+5,3*k+7):
            # Nonuniform rationals with scrambled original labels, not just integers.
            a=[Q(j**3+3*j-7,3) for j in range(m)];rng.shuffle(a)
            for trial in range(8):
                b=sorted(rng.sample(range(m),2*k+3),key=lambda i:a[i])
                c=construct(k,a,b);r=verify(c);totals['cases']+=1
                for key in ('sign_checks','moment_equations','proper_subsets_checked','original_inequalities','strict_rows'):totals[key]+=r[key]
                A=rows(k,a)
                for _ in range(3):
                    v=[Q(rng.randrange(-7,8),11) for _ in range(2*k)]
                    maxima=max([Q(0)]+[sum(ai*x for ai,x in zip(row,v)) for row in A])
                    x=[z/(maxima+1) for z in v]
                    vals=[sum(ai*z for ai,z in zip(row,x)) for row in A]
                    require(all(z<=1 for z in vals),'bad feasible test point')
                    require(any(vals[i]<1 for i in b[1::2]),'no strict odd row at feasible point')
                    totals['feasible_point_checks']+=1;totals['strict_negative_side_checks']+=1
                if trial==0:saved.append(serial(c))
    large=[]
    for k in (8,16,32):
        m=4*k+1;a=[Q(i) for i in range(m)]
        odd=sorted(rng.sample(list(range(1,4*k,2)),k+1))
        sep=[odd[0]-1]+[i+1 for i in odd]
        b=sorted(odd+sep)
        c=construct(k,a,b,complete=False);r=verify(c)
        require(c['odd_labels']==odd,'separated odd family has wrong rank partition')
        large.append(r);saved.append(serial(c))
    # Exhaustive odd-subset family instantiations, counted separately, all proper faces checked.
    catalogue=[]
    for k in (1,2,3,4):
        m=4*k+1;cnt=faces=0
        for N in combinations(range(1,4*k,2),k+1):
            b=sorted(list(N)+[N[0]-1]+[i+1 for i in N])
            c=construct(k,list(range(m)),b);r=verify(c);cnt+=1;faces+=r['proper_subsets_checked']
        catalogue.append({'k':k,'minimal_sets_checked':cnt,'proper_face_checks':faces})
    negatives=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,ZeroDivisionError,IndexError):negatives.append(name)
        else:raise AssertionError('accepted malformed input '+name)
    baseline=next(c for c in saved if c['k']==2)
    mutations=[('unordered_chain',lambda c:c['b'].reverse()),
      ('duplicate_parameter',lambda c:c['a'].__setitem__(0,c['a'][1])),
      ('wrong_weight',lambda c:c['weights'].__setitem__(0,'999')),
      ('even_side_as_minimal_set',lambda c:c.update(odd_labels=sorted(c['b'][::2]))),
      ('missing_maximal_proper_face',lambda c:c['supports'].pop()),
      ('false_support_point',lambda c:c['supports'][-1]['point'].__setitem__(0,'999')),
      ('wrong_half_dimension',lambda c:c.update(k=c['k']+1)),
      ('boolean_chain_label',lambda c:c['b'].__setitem__(0,True)),
      ('float_parameter',lambda c:c['a'].__setitem__(0,0.0))]
    for name,mut in mutations:
        bad=deepcopy(baseline);mut(bad);reject(name,lambda bad=bad:verify(bad))
    # All consumers run with coefficient/witness production disabled.
    old_support,old_construct=globals()['support'],globals()['construct']
    def disabled(*a,**kw):raise AssertionError('consumer invoked witness generation')
    globals()['support']=globals()['construct']=disabled
    try:
        for c in saved:verify(c)
    finally:globals()['support'],globals()['construct']=old_support,old_construct
    src=(PACKET/'solution.lean').read_text();meta=json.loads((PACKET/'problem.json').read_text())
    signature=src.split('\ntheorem solution ',1)[1].split(' := by\n',1)[0]
    formal=meta['formal_statement'].split('\ntheorem moment_curve_ordered_minimal_nonfaces ',1)[1].split(' := by sorry',1)[0]
    require(signature==formal,'public target signature mismatch')
    require(all(t not in src for t in ['sorry','admit','native_decide','unsafe']),'proof admission/unsafe token')
    require(meta['preamble']=='import Mathlib\n\nopen scoped BigOperators','custom declaration in preamble')
    report={'status':'PASS','scope':'Exact rational interpretation/signature checks; NOT Lean verification',
      'small':totals,'large':large,'odd_catalogue_instantiations':catalogue,
      'producer_disabled_audits':len(saved),'negative_controls':negatives,'exact_target_signature_match':True,
      'solution_lines':len(src.splitlines()),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/ORDERED_MOMENT_PACKET_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'fixtures/ordered_moment_examples.json').write_text(json.dumps(saved,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
