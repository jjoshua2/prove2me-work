#!/usr/bin/env python3
"""Original-H ordinary-edge certificates for arbitrary rational two-variable rows.

The previous signed shadow state machine is reused unchanged. This module
replaces signed constants by exact multiplicative gain-component kernels and
independently verifies every original edge. Optional gain-lattice certificates
supply a classical diameter-existence bound; unrecognized/unconditioned input
may still produce a checked route, without a uniform length/runtime assertion.
The inherited finite objective sampler is NOT the published random-shift sampler.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from pathlib import Path
from signed_basis_shadow import SignedModel
from gain_lattice_certificate import (
    parse_rows, rat, dot, serial, require, gain_kernel, gain_inverse,
    certify as certify_condition, verify as verify_condition,
)


class GainModel(SignedModel):
    def __init__(self,data,condition=None,discover=True):
        self.originalA=parse_rows(data['A']);self.originalb=tuple(map(rat,data['b']))
        self.d=len(self.originalA[0]);self.m=len(self.originalA)
        require(len(self.originalb)==self.m,'right-hand-side count')
        self.start=tuple(map(rat,data['start']));self.end=tuple(map(rat,data['end']))
        require(len(self.start)==self.d==len(self.end),'endpoint shape')
        for x in (self.start,self.end):
            require(all(dot(a,x)<=b for a,b in zip(self.originalA,self.originalb)),'infeasible endpoint')
        if condition is None and data.get('gain_base') is not None:
            require(discover,'missing conditioning certificate')
            condition=certify_condition(data['A'],data['gain_base'])['certificate']
        self.condition=condition;self.condition_result=None
        if condition is not None:
            require(data.get('gain_base') is not None and rat(condition['base'])==rat(data['gain_base']),
                    'conditioning base changed')
            self.condition_result=verify_condition(data['A'],condition)
            self.scale=list(map(rat,condition['diagonal']))
        else:self.scale=[Q(1)]*self.d
        self.fullA=[];self.row_scale=[]
        for a in self.originalA:
            row=tuple(x*s for x,s in zip(a,self.scale));t=max(map(abs,row),default=Q(0))or Q(1)
            self.row_scale.append(t);self.fullA.append(tuple(x/t for x in row))
        self.fullb=tuple(b/t for b,t in zip(self.originalb,self.row_scale))
        xs=tuple(x/s for x,s in zip(self.start,self.scale));ys=tuple(x/s for x,s in zip(self.end,self.scale))
        acts=[[i for i,(a,b) in enumerate(zip(self.fullA,self.fullb))if dot(a,x)==b]for x in(xs,ys)]
        for act in acts:
            require(gain_kernel([self.fullA[i]for i in act],self.d)['rank']==self.d,'endpoint is not a vertex')
        self.common=sorted(set(acts[0])&set(acts[1]));ker=gain_kernel([self.fullA[i]for i in self.common],self.d)
        self.lift_columns=ker['kernel'];self.h=len(self.lift_columns);self.offset=xs
        self.A=[];self.b=[];self.quotient_scale=[]
        for a,b in zip(self.fullA,self.fullb):
            row=tuple(dot(a,g)for g in self.lift_columns);t=max(map(abs,row),default=Q(0))or Q(1)
            self.A.append(tuple(x/t for x in row));self.b.append((b-dot(a,xs))/t);self.quotient_scale.append(t)
            require(sum(bool(x)for x in row)<=2,'gain face model lost two-variable support')
        self.b=tuple(self.b);self.s=(Q(0),)*self.h
        self.t=tuple((ys[next(i for i,x in enumerate(g)if x)]-xs[next(i for i,x in enumerate(g)if x)]) /
                     next(x for x in g if x) for g in self.lift_columns)
        require(self.lift(self.t)==self.end,'target not in exact common-face image')
        mid=tuple(x/2 for x in self.t)
        require(all(not any(a) or dot(a,mid)<b for a,b in zip(self.A,self.b)),
                'midpoint not strict in common-face quotient')
        self.inv_cache={};self.basis_searches=0
        self.digest=hashlib.sha256(json.dumps(serial({'A':self.originalA,'b':self.originalb,
                              'start':self.start,'end':self.end}),sort_keys=True).encode()).hexdigest()

    def inverse(self,B):
        B=tuple(B)
        if B not in self.inv_cache:self.inv_cache[B]=gain_inverse([self.A[i]for i in B])[0]
        return self.inv_cache[B]


def construct(data,attempts=12,limit=20000):
    P=GainModel(data);failed=[]
    for seed in range(attempts):
        try:
            c=serial(P.one_attempt(seed,limit));c['conditioning']=P.condition
            return {'certificate':c,'verified':verify(data,c),'retry_failures':failed}
        except ValueError as e:
            if 'objective tie' not in str(e):raise
            failed.append(str(e))
    raise ValueError('objective trial cap; no geometric nonexistence conclusion')


def verify(data,cert):
    """No path, gauge, or basis-search call. Recompute the finite proof evidence."""
    P=GainModel(data,cert.get('conditioning'),discover=False)
    require(cert['input_sha256']==P.digest,'changed input or endpoints')
    require(type(cert['dimension'])is int and cert['dimension']==P.h,'false intrinsic dimension')
    if P.h==0:
        require(P.start==P.end and not cert['basis_steps']and cert['route']==[serial(P.start)],'false stationary route')
        return {'status':'PASS','dimension':P.d,'intrinsic_dimension':0,'edges':0,'stationary_pivots':0,'pivots':0,'row_checks':P.m,
                'conditioning':P.condition_result,'scope':'Exact original-H route only; not a Lean/platform verdict.'}
    Bs=tuple(cert['source_basis']);Bt=tuple(cert['target_basis'])
    def valid_basis(B):
        require(len(B)==P.h and len(set(B))==P.h and all(type(i)is int and 0<=i<P.m for i in B),'invalid basis labels')
        require(P.feasible_basis(B),'symbolically infeasible basis')
    valid_basis(Bs);valid_basis(Bt)
    require(P.point(Bs)==P.s and P.point(Bt)==P.t,'basis endpoints changed')
    ws=tuple(map(rat,cert['source_weights']));wt=tuple(map(rat,cert['target_weights']))
    require(len(ws)==P.h==len(wt)and all(w>0 for w in ws+wt),'invalid exposing weights')
    c0=tuple(map(rat,cert['source_objective']));c1=tuple(map(rat,cert['target_objective']))
    for c,w,B in[(c0,ws,Bs),(c1,wt,Bt)]:
        require(len(c)==P.h and c==tuple(sum((w[k]*P.A[r][j]for k,r in enumerate(B)),Q(0))for j in range(P.h)),
                'false exposing objective')
    B=Bs;time=Q(0);route=[P.start];stationary=checks=0;largest_inverse=Q(0)
    for step in cert['basis_steps']:
        require(tuple(step['basis'])==B,'broken basis chain');inv=P.inverse(B)
        largest_inverse=max(largest_inverse,max(abs(x)for row in inv for x in row))
        t=rat(step['time']);j=step['leave_position'];enter=step['enter']
        require(type(j)is int and 0<=j<P.h and type(enter)is int and 0<=enter<P.m,'invalid pivot index')
        require(time<=t<1,'invalid objective time')
        l0=P.coefficients(c0,inv);ld=P.coefficients(tuple(v-u for u,v in zip(c0,c1)),inv)
        require(all(a+time*b>=0 and a+t*b>=0 for a,b in zip(l0,ld)),'dual interval failed')
        require(l0[j]+t*ld[j]==0 and ld[j]<0,'false leaving event')
        direction=tuple(-row[j]for row in inv);den=dot(P.A[enter],direction)
        require(den>0,'entering row is not a blocker');chosen=P.ratio_series(B,enter,inv,den)
        require(P.series_cmp(chosen,{})>0,'nonpositive formal step')
        for r,a in enumerate(P.A):
            v=dot(a,direction)
            if v>0:require(P.series_cmp(chosen,P.ratio_series(B,r,inv,v))<=0,'wrong lexicographic ratio')
        require(rat(step['alpha_constant'])==chosen.get(0,Q(0)),'false real step length')
        newB=tuple(enter if k==j else r for k,r in enumerate(B))
        require(tuple(step['next_basis'])==newB,'false basis replacement');valid_basis(newB)
        x=P.lift(P.point(B));y=P.lift(P.point(newB))
        for p in(x,y):
            require(all(dot(a,p)<=b for a,b in zip(P.originalA,P.originalb)),'infeasible original point');checks+=P.m
        if x==y:stationary+=1
        else:
            common=[a for a,b in zip(P.originalA,P.originalb)if dot(a,x)==b==dot(a,y)]
            require(gain_kernel(common,P.d)['rank']==P.d-1,'non-edge in original polyhedron')
            require(dot(P.originalA[B[j]],x)==P.originalb[B[j]]and dot(P.originalA[B[j]],y)<P.originalb[B[j]],'missing original leaving bound')
            require(dot(P.originalA[enter],y)==P.originalb[enter]and dot(P.originalA[enter],x)<P.originalb[enter],'missing original entering bound')
            route.append(y)
        B=newB;time=t
    require(tuple(cert['final_basis'])==B,'false final basis')
    require(all(x>=0 for x in P.coefficients(c1,P.inverse(B))),'target objective not optimal')
    require(P.lift(P.point(B))==P.end,'wrong final endpoint')
    require([tuple(map(rat,p))for p in cert['route']]==route,'forged route coordinates')
    require(all(all(dot(P.originalA[i],x)==P.originalb[i]for i in P.common)for x in route),'lost endpoint-common equality')
    bound=None
    if P.condition_result:
        R=P.condition_result['integer_gauge_radius']
        if R==0:bound=36*P.h**3
        elif P.condition_result['quartic_regime_certified']:bound=360*R**2*P.d**2*P.h**2
    return {'status':'PASS','dimension':P.d,'intrinsic_dimension':P.h,'rows':P.m,'edges':len(route)-1,
            'pivots':len(cert['basis_steps']),'stationary_pivots':stationary,'row_checks':checks,
            'largest_visited_quotient_inverse_entry':str(largest_inverse),
            'conditioning':P.condition_result,'classical_safe_existence_bound':bound,
            'sample_within_existence_bound':None if bound is None else len(route)-1<=bound,
            'scope':'Exact ORIGINAL-H edges. The finite objective sampler has no asserted uniform polynomial pivot bound; classical diameter existence is separate.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--limit',type=int,default=20000);p.add_argument('--output',type=Path);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());result=verify(data,json.loads(a.certificate.read_text()))if a.certificate else construct(data,limit=a.limit)
        text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError)as e:p.exit(2,f'No route certificate: {e}\n')
if __name__=='__main__':main()
