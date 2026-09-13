#!/usr/bin/env python3
"""Exact joint Minkowski extraction region for supplied finite candidate shapes.

Return ALL nonnegative scale vectors t for which R=E(t)+sum_l t_l Q_l.
Each coefficient inequality is supplied with matching primal/dual original-H
witnesses. This handles the competition between nonsegment summands: their
separate maximum scales generally cannot all be removed simultaneously.
The positive-circuit enumeration is exponential in the TOTAL number of
non-anchor candidate points, and capped explicitly. It never claims universal
shape discovery, minimum-diameter residual choice or polynomial simplex pivots.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from pathlib import Path
from exact_farkas_lp import (parse,rat,serial,dot,require,ExactLP,feasible_point,verify_optimum)
from finite_summand_capacity import candidate,enumerate_circuits


class JointData:
    def __init__(self,A,b,shapes,cap=300000):
        self.A,self.b=parse(A,b);self.d=len(self.A[0]);self.m=len(self.A)
        require(isinstance(shapes,(list,tuple)) and shapes,'candidate shape list empty')
        self.parts=[candidate(v,self.d) for v in shapes];self.s=len(shapes)
        self.G=tuple(g for _,part in self.parts for g in part);self.k=len(self.G)
        self.H=tuple(tuple(max([Q(0)]+[dot(a,g) for g in part]) for _,part in self.parts) for a in self.A)
        blocks=[];start=0
        for _,part in self.parts:
            end=start+len(part);blocks.append(tuple(Q(start<=i<end) for i in range(self.k)));start=end
        self.C=tuple(tuple(-dot(a,g) for g in self.G) for a in self.A)+\
            tuple(tuple(-Q(i==j) for j in range(self.k)) for i in range(self.k))+tuple(blocks)
        self.circuits,self.subsets=enumerate_circuits(self.C,cap);self.constraints=[]
        for I,w in self.circuits:
            v=tuple(sum((t*self.A[i][j] for i,t in zip(I,w) if i<self.m),Q(0)) for j in range(self.d))
            const=sum((t*self.b[i] for i,t in zip(I,w) if i<self.m),Q(0))
            gam=tuple(sum((t*self.H[i][l] if i<self.m else -t if i==self.m+self.k+l else Q(0)
                           for i,t in zip(I,w)),Q(0)) for l in range(self.s))
            if any(g>0 for g in gam):
                # An external minimal positive circuit cannot contain the
                # complete internal simplex circuit of any shape. Thus its
                # simplex multiplier is exactly that shape's support at v,
                # and every coefficient is a nonnegative support deficit.
                require(all(g>=0 for g in gam),'minimal circuit violated nonnegative packing structure')
                self.constraints.append((I,w,v,const,gam))
        payload={'A':self.A,'b':self.b,'anchored_shapes':self.parts}
        self.digest=hashlib.sha256(json.dumps(serial(payload),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def discover_region(A,b,shapes,seed=None,subset_cap=300000,pivot_cap=20000):
    P=JointData(A,b,shapes,subset_cap);x=feasible_point(P.A,P.b,seed,pivot_cap)
    lp=ExactLP(P.A,P.b,x,pivot_cap);cache={};rows=[]
    for I,w,v,const,gam in P.constraints:
        scale=max(map(abs,v),default=Q(0)) or Q(1);key=tuple(z/scale for z in v)
        if key not in cache:cache[key]=lp.maximize(key)
        o=cache[key];bound=rat(o['value'])*scale
        opt={'point':o['point'],'dual':[[i,str(rat(t)*scale)] for i,t in o['dual']],'value':str(bound)}
        rows.append({'support':list(I),'circuit_weights':serial(w),'coefficients':serial(gam),
                     'rhs':str(const-bound),'optimum':opt})
    c={'problem_sha256':P.digest,'rows':rows,'enumerated_supports':P.subsets,'positive_circuits':len(P.circuits),
       'original_feasible_point':serial(x)}
    return {'certificate':c,'verified':verify_region(A,b,shapes,c,subset_cap),
            'discovery':{'lp_calls':lp.calls,'lp_pivots':lp.pivots}}


def verify_region(A,b,shapes,c,subset_cap=300000):
    P=JointData(A,b,shapes,subset_cap);require(c['problem_sha256']==P.digest,'changed joint extraction input')
    require(type(c['enumerated_supports'])is int and c['enumerated_supports']==P.subsets,'false enumeration coverage')
    require(type(c['positive_circuits'])is int and c['positive_circuits']==len(P.circuits),'false positive-circuit count')
    x=tuple(map(rat,c['original_feasible_point']))
    require(len(x)==P.d and all(dot(a,x)<=b for a,b in zip(P.A,P.b)),'original feasibility not certified')
    wanted={I:(w,v,const,gam) for I,w,v,const,gam in P.constraints};seen=set()
    for row in c['rows']:
        require(isinstance(row['support'],list) and all(type(i)is int for i in row['support']),'invalid support')
        I=tuple(row['support']);require(I in wanted and I not in seen,'unknown/duplicate joint circuit')
        seen.add(I);w,v,const,gam=wanted[I]
        require(tuple(map(rat,row['circuit_weights']))==w,'false positive-circuit weights')
        require(tuple(map(rat,row['coefficients']))==gam,'false joint scale coefficients')
        _,value=verify_optimum(P.A,P.b,v,row['optimum'])
        require(rat(row['rhs'])==const-value and const>=value,'joint region row not exact')
    require(seen==set(wanted),'joint coefficient region is missing a restrictive circuit')
    return {'status':'PASS','shapes':P.s,'barycentric_variables':P.k,'original_rows':P.m,
        'enumerated_supports':P.subsets,'positive_circuits':len(P.circuits),'region_inequalities':len(wanted),
        'complete_joint_scale_region':True,'nonnegative_packing_region':True,'scope':'Exact parameter region for the SUPPLIED shapes; all scales nonnegative. No universal shape discovery.'}


def verify_scales(A,b,shapes,c,scales,subset_cap=300000):
    info=verify_region(A,b,shapes,c,subset_cap);t=tuple(map(rat,scales))
    require(len(t)==len(shapes) and all(z>=0 for z in t),'negative/missing extraction scale')
    require(all(dot(tuple(map(rat,r['coefficients'])),t)<=rat(r['rhs']) for r in c['rows']),
            'simultaneous scales violate the exact extraction region')
    return {**info,'scales':serial(t),'global_simultaneous_minkowski_equality':True}


def optimize_scales(A,b,shapes,c,objective,subset_cap=300000,pivot_cap=20000):
    verify_region(A,b,shapes,c,subset_cap);s=len(shapes)
    M=[tuple(map(rat,r['coefficients'])) for r in c['rows']]+[tuple(-Q(i==j) for j in range(s)) for i in range(s)]
    rhs=[rat(r['rhs']) for r in c['rows']]+[Q(0)]*s
    require(M,'empty scale LP');lp=ExactLP(M,rhs,(Q(0),)*s,pivot_cap);o=lp.maximize(objective)
    verify_optimum(tuple(M),tuple(rhs),tuple(map(rat,objective)),o)
    verify_scales(A,b,shapes,c,o['point'],subset_cap)
    return {'objective':serial(objective),'optimum_certificate':o,
            'scope':'Optimal supplied linear extraction objective, NOT an optimal graph diameter or residual complexity claim.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path);a=p.parse_args()
    try:
        d=json.loads(a.input.read_text());out=discover_region(d['A'],d['b'],d['candidate_shapes'],d.get('start'))
        if 'scale_objective' in d:out['scale_optimization']=optimize_scales(d['A'],d['b'],d['candidate_shapes'],out['certificate'],d['scale_objective'])
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,ZeroDivisionError,OSError) as e:p.exit(2,f'No exact joint region: {e}\n')
if __name__=='__main__':main()
