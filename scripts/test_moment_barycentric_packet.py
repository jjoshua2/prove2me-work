#!/usr/bin/env python3
"""Exact arithmetic/signature tests; NOT Lean verification.

The main witnesses are explicit inverse products evaluated on ORIGINAL centered
rows. Tests include arbitrary order, nonuniform rational nodes, zero dimension,
selected subsets, both signs, and the odd-label application to prior #285.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import prod
from pathlib import Path
from copy import deepcopy
import hashlib, json, random

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/publication_packets/moment_barycentric_nonfaces'

def rat(v):
    if type(v) not in (int,str,Q): raise ValueError('exact rational input required')
    return Q(v)

def check(ok,msg):
    if not ok: raise ValueError(msg)

def polynomial(roots):
    p=[Q(1)]
    for r in roots:
        for _ in range(2):
            q=[Q(0)]*(len(p)+1)
            for i,c in enumerate(p):q[i]-=r*c;q[i+1]+=c
            p=q
    return p

def horner(p,t):
    v=Q(0)
    for c in reversed(p):v=v*t+c
    return v

def node_weights(a,s):
    return {i:1/prod((a[i]-a[j] for j in s if j!=i),start=Q(1)) for i in s}

def rows(a,d):
    mean=[sum((x**j for x in a),Q(0))/len(a) for j in range(1,d+1)]
    return [[x**j-mean[j-1] for j in range(1,d+1)] for x in a]

def point(a,d,tight):
    p=polynomial([a[i] for i in tight]);h=sum((horner(p,x) for x in a),Q(0))/len(a)
    check(h>0 and len(p)<=d+1,'invalid small-face witness')
    return [-p[j]/h if j<len(p) else Q(0) for j in range(1,d+1)]

def make(a,d,s,x):
    w=node_weights(a,s)
    return {'dimension':d,'parameters':list(map(str,a)),'selected':sorted(s),
            'weights':{str(i):str(w[i]) for i in s},'point':list(map(str,x))}

def verify(c):
    d=c['dimension'];check(type(d)is int and d>=0,'dimension')
    a=list(map(rat,c['parameters']));s=c['selected'];x=list(map(rat,c['point']))
    check(type(s)is list and s==sorted(set(s)) and len(s)>=d+2,'selected count')
    check(all(type(i)is int and 0<=i<len(a) for i in s),'indices')
    check(len(a)==len(set(a)) and len(x)==d,'distinct nodes/point dimension')
    check(set(c['weights'])==set(map(str,s)),'exact weight table')
    w={i:rat(c['weights'][str(i)]) for i in s}
    # Multiplication checks the actual inverse identities; do not call producer.
    for i in s:
        den=prod((a[i]-a[j] for j in s if j!=i),start=Q(1))
        check(w[i]!=0 and w[i]*den==1,'incorrect inverse-product weight')
    for r in range(d+1):
        check(sum((w[i]*a[i]**r for i in s),Q(0))==0,'moment annihilation failed')
    A=rows(a,d);values=[sum((t*y for t,y in zip(row,x)),Q(0)) for row in A]
    check(all(y<=1 for y in values),'infeasible original point')
    check(sum(values,Q(0))==0,'mean centering failed')
    slack=[1-y for y in values]
    check(sum((w[i]*slack[i] for i in s),Q(0))==0,'weighted slack failed')
    neg=[i for i in s if w[i]<0 and slack[i]>0]
    pos=[i for i in s if w[i]>0 and slack[i]>0]
    check(neg and pos,'no strict slack on a sign side')
    return {'negative_strict':neg,'positive_strict':pos,'moment_equations':d+1,
            'original_rows':len(a),'selected_rows':len(s)}

def main():
    global node_weights,point
    rng=random.Random(286);counts={'cases':0,'moment_equations':0,'original_row_checks':0,
       'selected_weight_checks':0,'odd_nonface_applications':0,'proper_face_checks':0}
    saved=[]
    def case(a,d,s,x,keep=False):
        c=make(a,d,s,x);r=verify(c)
        counts['cases']+=1;counts['moment_equations']+=r['moment_equations']
        counts['original_row_checks']+=r['original_rows'];counts['selected_weight_checks']+=r['selected_rows']
        if keep:saved.append(c)
        return c,r
    # Small d, arbitrary order and nonuniform exact rational nodes. More than
    # d+2 selected nodes and proper subsets of the original parameter family.
    for d in range(8):
        for extra in range(4):
            m=d+2+extra
            for trial in range(12):
                a=[Q(i*i+3*i+1,trial+2) for i in range(m)];rng.shuffle(a)
                s=sorted(rng.sample(range(m),rng.randint(d+2,m)))
                q=rng.randint(0,min(d//2,m-1));tight=rng.sample(range(m),q)
                x=point(a,d,tight)
                case(a,d,s,x,trial==0 and extra==0)
                # Strictly internal convex combination of a valid witness and0.
                case(a,d,s,[Q(2,5)*v for v in x])
    # Every small odd (k+1)-set is exactly the negative sign side after adding
    # the explicit even separators. Proper subsets use squared-root witnesses.
    odds=[]
    for k in (1,2,3,4):
        d=2*k;a=list(map(Q,range(4*k+1)));ncase=0
        for N in combinations(range(1,4*k,2),k+1):
            Y=[N[0]-1]+[n+1 for n in N];s=sorted(set(N)|set(Y));w=node_weights(a,s)
            check({i for i in s if w[i]<0}==set(N),'wrong odd sign side')
            check({i for i in s if w[i]>0}==set(Y),'wrong separator sign side')
            counts['odd_nonface_applications']+=1;ncase+=1
            for omitted in N:
                T=[n for n in N if n!=omitted];x=point(a,d,T);c,r=case(a,d,s,x)
                vals=[sum((v*z for v,z in zip(row,x)),Q(0)) for row in rows(a,d)]
                check({i for i,y in enumerate(vals) if y==1}==set(T),'proper-face active set')
                check(r['negative_strict']==[omitted],'missing row slack certificate')
                counts['proper_face_checks']+=1
            if ncase==1:saved.append(c)
        odds.append({'k':k,'dimension':d,'original_rows':len(a),'all_odd_sets_checked':ncase})
    large=[]
    for k in (8,16,32):
        a=list(map(Q,range(4*k+1)));N=sorted(rng.sample(range(1,4*k,2),k+1))
        s=sorted(set(N)|{N[0]-1}|{n+1 for n in N});w=node_weights(a,s)
        check({i for i in s if w[i]<0}==set(N),'large parity signs')
        omitted=N[len(N)//2];x=point(a,2*k,[i for i in N if i!=omitted])
        c,r=case(a,2*k,s,x,True)
        check(r['negative_strict']==[omitted],'large exact proper-subset witness')
        large.append({'dimension':2*k,'original_rows':len(a),'selected_rows':len(s),
             'negative_rows':len(N),'positive_rows':len(s)-len(N),
             'omitted_label':omitted,'negative_strict_rows':r['negative_strict'],
             'all_odd_sets_enumerated':False})
    failures=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,ZeroDivisionError,KeyError):failures.append(name)
        else:raise AssertionError('accepted false '+name)
    base=saved[4]
    for name,edit in [
        ('false_weight',lambda c:c['weights'].__setitem__(str(c['selected'][0]),'0')),
        ('reversed_sign',lambda c:c['weights'].__setitem__(str(c['selected'][0]),str(-Q(c['weights'][str(c['selected'][0])])))),
        ('omitted_weight',lambda c:c['weights'].pop(str(c['selected'][0]))),
        ('insufficient_nodes',lambda c:c.update(selected=c['selected'][:c['dimension']+1])),
        ('duplicate_parameter',lambda c:c['parameters'].__setitem__(1,c['parameters'][0])),
        ('bool_dimension',lambda c:c.update(dimension=True)),
        ('wrong_point_dimension',lambda c:c['point'].append('0')),
        ('float_parameter',lambda c:c['parameters'].__setitem__(0,0.0))]:
        bad=deepcopy(base);edit(bad);reject(name,lambda bad=bad:verify(bad))
    invalid=make(list(map(Q,range(5))),2,list(range(5)),[Q(100),Q(100)])
    reject('infeasible_point',lambda:verify(invalid))
    # The strict conclusion fails without the extra node required by hp.
    # A degree1 polynomial at only2 nodes has nonzero leading weighted sum.
    a=[Q(0),Q(1)];w=node_weights(a,[0,1]);check(sum(w[i]*a[i] for i in range(2))==1,'degree boundary control')
    # Consumer independent of witness generators.
    old_weights,old_point=node_weights,point
    def disabled(*args):raise AssertionError('consumer invoked producer')
    node_weights=point=disabled
    try:
        for c in saved:verify(c)
    finally:node_weights,point=old_weights,old_point
    sol=(PACKET/'solution.lean').read_text();meta=json.loads((PACKET/'problem.json').read_text())
    sig=sol.split('theorem solution ',1)[1].split(' := by\n',1)[0]
    target=meta['formal_statement'].split('theorem moment_curve_barycentric_nonfaces ',1)[1].split(' := by sorry',1)[0]
    check(sig==target,'public signature mismatch')
    for token in ('sorry','admit','sorryAx','native_decide','unsafe'):
        check(token not in sol,'forbidden proof token '+token)
    check(meta['preamble']=='import Mathlib\nopen scoped BigOperators','preamble')
    check(meta['env']=='c5ea00351c28e24afc9f0f84379aa41082b1188f','pin')
    report={'status':'PASS','scope':'Exact rational semantics and signature checks, NOT Lean compilation or Prove2Me acceptance',
       **counts,'small_odd_families':odds,'large_selected_examples':large,
       'rejected_controls':failures,'degree_boundary_control':True,'producer_disabled_replays':len(saved),
       'exact_public_signature_match':True,'proof_lines':len(sol.splitlines()),
       'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/MOMENT_BARYCENTRIC_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'fixtures/moment_barycentric_examples.json').write_text(json.dumps(saved,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
