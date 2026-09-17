#!/usr/bin/env python3
"""Exact tests of the original moment-H bounding proof; not Lean verification.

The producer supplies Lagrange coefficients. The consumer verifies every nodal
Kronecker identity and independently constructs/evaluates the ORIGINAL rows.
No vertex catalogue, LP, refinement, floating determinant or library is used.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/publication_packets/moment_compact_body'

def require(ok,msg):
    if not ok:raise ValueError(msg)

def rat(x):
    require(type(x) in (int,str,Q),'exact rational value required')
    return Q(x)

def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

def product_polynomial(nodes):
    p=[Q(1)]
    for t in nodes:
        q=[Q(0)]*(len(p)+1)
        for j,c in enumerate(p):q[j]-=t*c;q[j+1]+=c
        p=q
    return p

def evaluate(p,t):
    v=Q(0)
    for c in reversed(p):v=v*t+c
    return v

def rows(d,nodes):
    m=len(nodes)
    means=[sum(a**j for a in nodes)/m for j in range(1,d+1)]
    return [[a**j-means[j-1] for j in range(1,d+1)] for a in nodes]

def dot(a,b):
    require(len(a)==len(b),'dot dimensions')
    return sum((x*y for x,y in zip(a,b)),Q(0))

def lagrange(nodes):
    # Synthetic division of the nodal polynomial, not m independent products.
    p=product_polynomial(nodes);m=len(nodes);out=[]
    for t in nodes:
        q=[Q(0)]*m;q[-1]=p[-1]
        for j in range(m-2,-1,-1):q[j]=p[j+1]+t*q[j+1]
        require(p[0]+t*q[0]==0,'not divisible by node root')
        denominator=evaluate(q,t);require(denominator!=0,'repeated node')
        out.append([c/denominator for c in q])
    return out

def original_support(d,nodes,T):
    p=product_polynomial([nodes[i] for i in T for _ in range(2)])
    require(len(p)-1<=d,'support degree exceeds dimension')
    h=sum(evaluate(p,t) for t in nodes)/len(nodes);require(h>0,'no positive support average')
    return [-p[j]/h if j<len(p) else Q(0) for j in range(1,d+1)]

def produce(k,nodes,seed=0):
    require(type(k)is int and k>0,'positive k required')
    a=list(map(rat,nodes));d=2*k;m=len(a)
    require(d<m and len(set(a))==m,'insufficient or repeated nodes')
    A=rows(d,a);L=lagrange(a)
    R=[m*sum(abs(l[j+1]) for l in L) for j in range(d)]
    inner=1/(1+max(sum(abs(c) for c in r) for r in A))
    rng=random.Random(seed);points=[[Q(0)]*d]
    for _ in range(4):
        u=[Q(rng.randrange(-8,9),7) for j in range(d)]
        maximum=max([Q(0)]+[dot(row,u) for row in A])
        points.append([c/(maximum+1) for c in u])
    # Exact supports approach many boundary hyperplanes, unlike only tiny points.
    supports=[]
    for i in range(m):
        x=original_support(d,a,[i]);supports.append({'row':i,'point':x});points.append(x)
    for _ in range(3):points.append(original_support(d,a,rng.sample(range(m),k)))
    return serial({'format':'moment-compact-body-v1','k':k,'nodes':a,'lagrange_coefficients':L,
        'coordinate_radius':R,'interior_cube_radius':inner,'points':points,'singleton_supports':supports})

def verify(c):
    require(c['format']=='moment-compact-body-v1','format mismatch')
    k=c['k'];require(type(k)is int and k>0,'positive k required')
    a=list(map(rat,c['nodes']));d=2*k;m=len(a)
    require(d<m and len(set(a))==m,'insufficient/inexact distinct nodes')
    A=rows(d,a);L=[list(map(rat,p)) for p in c['lagrange_coefficients']]
    require(len(L)==m and all(len(p)==m for p in L),'Lagrange degree/size mismatch')
    nodal=0
    for i,p in enumerate(L):
        for j,t in enumerate(a):
            require(evaluate(p,t)==int(i==j),'invalid nodal Lagrange basis');nodal+=1
    # Uniqueness at m distinct nodes fixes these degree<m polynomials without
    # rerunning the coefficient producer or synthetic division.
    R=list(map(rat,c['coordinate_radius']))
    expected=[m*sum(abs(p[j+1]) for p in L) for j in range(d)]
    require(R==expected and all(r>=0 for r in R),'incorrect explicit coordinate box')
    eps=rat(c['interior_cube_radius'])
    require(eps>0 and all(eps*sum(abs(v) for v in row)<1 for row in A),'false interior radius')
    inequalities=coefficient_checks=bound_checks=0
    for raw in c['points']:
        x=list(map(rat,raw));require(len(x)==d,'point dimension mismatch')
        vals=[dot(row,x) for row in A];slacks=[1-v for v in vals]
        require(all(v<=1 for v in vals),'test point is not feasible')
        require(all(0<=s<=m for s in slacks) and sum(slacks)==m,'false nonnegative slack simplex')
        # Independently compute every interpolated coefficient, including the
        # unused high-degree tail; evaluate original row values separately above.
        co=[sum(slacks[i]*L[i][j] for i in range(m)) for j in range(m)]
        for j in range(1,m):
            require(co[j]==(-x[j-1] if j<=d else 0),'coordinate/slack coefficient identity failed')
            coefficient_checks+=1
        for j in range(d):
            require(abs(x[j])<=R[j],'original coordinate escapes box');bound_checks+=1
        inequalities+=m
    seen=set();strict=0
    for p in c['singleton_supports']:
        i=p['row'];require(type(i)is int and 0<=i<m and i not in seen,'bad singleton label');seen.add(i)
        x=list(map(rat,p['point']));require(len(x)==d,'bad singleton dimension')
        vals=[dot(row,x) for row in A]
        require(all(v<=1 and (v==1)==(i==l) for l,v in enumerate(vals)),'not a unique-tight original row')
        strict+=m-1
    require(len(seen)==m,'missing original row support')
    return {'status':'PASS','dimension':d,'original_rows':m,'nodal_identities':nodal,
            'points':len(c['points']),'original_inequalities':inequalities,
            'reconstructed_nonconstant_coefficients':coefficient_checks,'coordinate_checks':bound_checks,
            'uniquely_supported_rows':m,'strict_other_row_checks':strict}

def main():
    saved=[];reports=[];rng=random.Random(290)
    for k in (1,2,3,4):
        for m in (2*k+1,2*k+3,4*k+1):
            # All are genuinely nonuniform and label-scrambled, not just integer
            # nodes for the particular cyclic example.
            a=[Q(j**3+2*j-5,7) for j in range(m)];rng.shuffle(a)
            c=produce(k,a,seed=k*100+m);r=verify(c);reports.append(r)
            saved.append(c)
    large=[]
    for k in (8,16):
        c=produce(k,list(range(4*k+1)),seed=k);r=verify(c);large.append(r);saved.append(c)
    negative=[]
    def reject(name,f):
        try:f()
        except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):negative.append(name)
        else:raise AssertionError('forgery accepted: '+name)
    proto=saved[4]
    mutations=[('repeated_parameter',lambda x:x['nodes'].__setitem__(0,x['nodes'][1])),
        ('wrong_lagrange_coefficient',lambda x:x['lagrange_coefficients'][0].__setitem__(1,'999')),
        ('false_coordinate_radius',lambda x:x['coordinate_radius'].__setitem__(0,'0')),
        ('nonpositive_interior_radius',lambda x:x.update(interior_cube_radius='0')),
        ('wrong_singleton_point',lambda x:x['singleton_supports'][0]['point'].__setitem__(0,'999')),
        ('missing_singleton',lambda x:x['singleton_supports'].pop()),
        ('nonfeasible_sample',lambda x:x['points'][0].__setitem__(0,'999999999999')),
        ('boolean_dimension',lambda x:x.update(k=True)),
        ('float_node',lambda x:x['nodes'].__setitem__(0,0.0))]
    for name,mutation in mutations:
        q=deepcopy(proto);mutation(q);reject(name,lambda q=q:verify(q))
    reject('too_few_nodes',lambda:produce(2,[0,1,2,3]))
    # Hypothesis controls: too few nodes can leave an explicit feasible line.
    # d=2,m=2,nodes0,1 has identical centered coordinate columns. Every (t,-t)
    # lies in the kernel, while with three identical nodes all rows are zero.
    shortA=rows(2,[Q(0),Q(1)]);v=[Q(1),Q(-1)]
    require(all(dot(row,v)==0 for row in shortA),'missing-node countercontrol wrong')
    repeatedA=rows(2,[Q(0)]*3)
    require(all(row==[Q(0),Q(0)] for row in repeatedA),'repeated-node countercontrol wrong')
    original=(globals()['produce'],globals()['lagrange'],globals()['original_support'],globals()['product_polynomial'])
    def blocked(*args,**kw):raise AssertionError('consumer used polynomial/witness production')
    globals()['produce']=globals()['lagrange']=globals()['original_support']=globals()['product_polynomial']=blocked
    try:
        for c in saved:verify(json.loads(json.dumps(c)))
    finally:globals()['produce'],globals()['lagrange'],globals()['original_support'],globals()['product_polynomial']=original
    source=(PACKET/'solution.lean').read_text();meta=json.loads((PACKET/'problem.json').read_text())
    sig=source.split('\ntheorem solution ',1)[1].split(' := by\n',1)[0]
    statement=meta['formal_statement'].split('\ntheorem moment_curve_compact_body ',1)[1].split(' := by sorry',1)[0]
    require(sig==statement,'formal target mismatch')
    require(all(s not in source for s in ('sorry','admit','native_decide','unsafe')),'proof admission token')
    totals={key:sum(r[key] for r in reports) for key in reports[0] if type(reports[0][key])is int}
    totals.pop('dimension');totals.pop('original_rows')
    report={'status':'PASS','scope':'exact rational interpretation and source checks, NOT Lean verification',
       'small_cases':reports,'small_totals':totals,'large_cases':large,'producer_disabled_audits':len(saved),
       'negative_controls':negative,'missing_hypothesis_controls':['insufficient_nodes_allow_kernel_line','repeated_nodes_allow_whole_space'],
       'exact_target_match':True,'source_lines':len(source.splitlines()),
       'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/MOMENT_COMPACT_BODY_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'fixtures/moment_compact_body_examples.json').write_text(json.dumps(saved,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
