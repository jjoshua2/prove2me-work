#!/usr/bin/env python3
"""Seeded exact construction, whole-sum audits, and forgery controls."""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction as F
import hashlib
import json
from math import prod
from pathlib import Path
import random
from deterministic_fibre_path import Model,add,sub,scale,dot,total,construct,verify,exhaustive,encode,avoid,need

def make(dim:int,factors:int,seed:int)->Model:
    rng=random.Random(seed);zero=(F(0),)*dim
    if dim==1:
        core=(zero,);f=(F(-1),);g=(F(1),)
    else:
        f=(F(-3),)+(F(0),)*(dim-2)+(F(5),)
        g=(F(3),)+(F(0),)*(dim-2)+(F(5),)
        cs=[zero]
        for _ in range(min(dim,5)):
            p=[F(rng.randint(-3,3)) for _ in range(dim)];p[-1]=-2-abs(p[0]);cs.append(tuple(p))
        core=tuple(cs+[zero])
    lists=[]
    for i in range(factors):
        for attempt in range(100):
            size=1+(i+seed)%3
            s=tuple(tuple(F(rng.randint(-5,5),rng.randint(1,4)) for _ in range(dim)) for _ in range(size))
            if i%4==0:s=(*s,s[0])
            if i%5==1 and len(set(s))>1:s=(*s,scale(F(1,2),add(s[0],s[-1])))
            trial=Model(core,zero,tuple([*lists,s]),f,g)
            try:trial.validate()
            except ValueError:continue
            lists.append(s);break
        else:raise RuntimeError('could not construct strict endpoint fixture')
    return Model(core,zero,tuple(lists),f,g)

def polynomial(roots):
    c=[F(1)]
    for r in roots:
        nc=[F(0)]*(len(c)+1)
        for i,a in enumerate(c):nc[i]-=r*a;nc[i+1]+=a
        c=nc
    return tuple(c)

def run(fixtures:Path|None=None)->dict:
    counts=dict(small_models=0,paths=0,edges=0,independent_edge_tuple_checks=0,
                whole_sum_models=0,parallel_crossings=0,full_face_point_checks=0,rejected_controls=0)
    chain=hashlib.sha256();max_ratio=F(0)
    for dim in (1,2,3,4,5):
        for j in range(16):
            m=make(dim,j%5,2026091400+dim*100+j)
            c=construct(m);v=verify(m,c);r=exhaustive(m,c)
            counts['small_models']+=1;counts['paths']+=1;counts['edges']+=v['edges']
            counts['whole_sum_models']+=1;counts['independent_edge_tuple_checks']+=r['edge_tuple_comparisons']
            counts['parallel_crossings']+=v['simultaneous_parallel_switches']
            counts['full_face_point_checks']+=v['full_face_comparisons']
            if v['factor_budget']:max_ratio=max(max_ratio,F(v['edges'],v['factor_budget']))
            chain.update(json.dumps(encode(c),sort_keys=True,separators=(',',':')).encode())
    # Force the original affine path through the whole square. The construction
    # must split its independent simultaneous changes while keeping endpoints.
    z=(F(0),F(0));x=(F(1),F(0));y=(F(0),F(1))
    square=Model((z,),z,((z,x),(z,y)),(-F(1),-F(1)),(F(1),F(1)))
    c=construct(square);v=verify(square,c);r=exhaustive(square,c)
    need(len(c['edges'])==2,'independent square switches were not split')
    counts['paths']+=1;counts['edges']+=2;counts['whole_sum_models']+=1
    counts['independent_edge_tuple_checks']+=r['edge_tuple_comparisons']
    # Several true parallel switches are retained as ONE genuine edge.
    parallel=Model((z,),z,((z,x),(z,scale(F(2),x)),(x,scale(F(3),x))),(-F(1),F(0)),(F(1),F(0)))
    cp=construct(parallel);vp=verify(parallel,cp);rp=exhaustive(parallel,cp)
    need(len(cp['edges'])==1 and vp['simultaneous_parallel_switches']==1,'parallel changes not retained')
    counts['paths']+=1;counts['edges']+=1;counts['parallel_crossings']+=1;counts['whole_sum_models']+=1
    counts['independent_edge_tuple_checks']+=rp['edge_tuple_comparisons']
    def rejects(name,call):
        try:call()
        except (ValueError,KeyError,IndexError,ZeroDivisionError,TypeError):counts['rejected_controls']+=1;return
        raise AssertionError('accepted forgery: '+name)
    def forged(name,mutate):
        cc=copy.deepcopy(c);mutate(cc);rejects(name,lambda:verify(square,cc))
    forged('input hash',lambda q:q.update(model_sha256='wrong'))
    forged('lost endpoint',lambda q:q.update(nodes=[q['nodes'][-1],*q['nodes'][1:]]))
    forged('wrong normal',lambda q:q['edges'][0].update(normal=z))
    forged('wrong full support',lambda q:q['edges'][0].update(support=999))
    forged('negative parallel length',lambda q:q['edges'][0]['factors'][0].update(eta=-1))
    forged('missing factor',lambda q:q['edges'][0].update(factors=[]))
    forged('outside time',lambda q:q['edges'][0].update(time=2))
    forged('same times',lambda q:q['edges'][1].update(time=q['edges'][0]['time']))
    forged('false state index',lambda q:q.update(nodes=[(999,0),*q['nodes'][1:]]))
    forged('false additive budget',lambda q:q.update(factor_budget=0))
    forged('endpoint perturbation wrong',lambda q:q.update(first=q['last']))
    forged('disconnected sum endpoint',lambda q:q['edges'][0].update(right=z))
    # Independent directions tied together expose a square, not its diagonal.
    diagonal=dict(model_sha256=square.digest(),first=square.first,last=square.last,nodes=[(0,0),(1,1)],
      edges=[dict(time=F(1,2),normal=z,left=z,right=add(x,y),support=0,
                  factors=[dict(lo=0,hi=1,eta=F(1,2),support=0)]*2)],factor_budget=2)
    rejects('rank-two diagonal',lambda:verify(square,diagonal))
    bad=Model((z,(F(2),F(2))),z,square.factors,square.first,square.last)
    rejects('different core endpoint cone',lambda:construct(bad))
    rejects('empty factor',lambda:construct(Model((z,),z,((),),square.first,square.last)))
    rejects('inexact JSON',lambda:Model.read(dict(core=[[0.0,0]],fixed=[0,0],factors=[],first=[1,0],last=[1,0])))
    # Check all tied listed points, including a point beyond purported endpoints.
    extended=Model((z,),z,((z,x,scale(F(4),x)),),(-F(1),F(0)),(F(1),F(0)))
    ce=construct(extended);ce['nodes'][-1]=(1,);ce['edges'][0]['factors'][0]['hi']=1;ce['edges'][0]['right']=x
    rejects('omitted tied listed point',lambda:verify(extended,ce))
    stress=[]
    for dim,m in ((2,12),(4,6),(7,4)):
        forms=[polynomial(range(i*(dim-1),(i+1)*(dim-1))) for i in range(m)]
        _,log=avoid((F(0),)*dim,[],forms)
        need(log['trials']==m*(dim-1)+1==log['trial_bound'],'root bound saturation failed')
        stress.append(dict(dimension=dim,forms=m,trials=log['trials'],bound=log['trial_bound']))
    large=[]
    # Coordinate triangles give large implicit products without expanding them.
    for dim,r in ((12,10),(24,16),(32,24)):
        zero=(F(0),)*dim
        core_points=[zero]
        for j in range(dim):
            v=[F(0)]*dim
            if j<dim-1:v[j]=F(1)
            v[-1]=F(-1);core_points.append(tuple(v))
        core=tuple(core_points)
        a=tuple([F(-2)]*(dim-1)+[F(10)])
        b=tuple([F(2)]*(dim-1)+[F(10)])
        lists=[]
        for i in range(r):
            u=[F(0)]*dim;v=[F(0)]*dim
            u[i%(dim-1)]=F(1);v[(i+1)%(dim-1)]=F(3,2)
            # Distinct positive lengths give a unique maximizing end point.
            lists.append((zero,tuple(u),tuple(v)))
        m=Model(core,zero,tuple(lists),a,b)
        cc=construct(m);vv=verify(m,cc)
        large.append(dict(dimension=dim,triangle_lists=r,core_generators=len(core),raw_point_tuple_count_not_enumerated=len(core)*3**r,
                          edges=vv['edges'],factor_budget=vv['factor_budget'],
                          direction_classes=cc['difference_directions'],pair_obstructions=cc['pair_obstructions'],
                          first_trials=cc['first_search']['trials'],first_bound=cc['first_search']['trial_bound'],
                          last_trials=cc['last_search']['trials'],last_bound=cc['last_search']['trial_bound'],
                          full_face_point_checks=vv['full_face_comparisons']))
        counts['paths']+=1;counts['edges']+=vv['edges'];counts['parallel_crossings']+=vv['simultaneous_parallel_switches']
        counts['full_face_point_checks']+=vv['full_face_comparisons']
        if fixtures and dim==32:
            fixtures.mkdir(parents=True,exist_ok=True)
            (fixtures/'fibre-32d-input.json').write_text(json.dumps(m.data(),indent=2)+'\n')
            (fixtures/'fibre-32d-certificate.json').write_text(json.dumps(encode(cc),indent=2)+'\n')
    return dict(status='PASS',seed=2026091400,counts=counts,small_certificate_chain_sha256=chain.hexdigest(),
                root_bound_saturation=stress,large=large,maximum_small_edges_to_factor_budget=str(max_ratio),
                square_control=dict(original_simultaneous_rank=2,constructed_edges=2,endpoints_unchanged=True),
                scope='Exact finite component support certificates. Not Lean compilation/extraction, arbitrary H-decomposition discovery, or a uniform Hirsch diameter bound.')

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path);p.add_argument('--fixtures',type=Path);args=p.parse_args()
    result=run(args.fixtures)
    result['source_sha256']={s:hashlib.sha256((Path(__file__).parent/s).read_bytes()).hexdigest()
                            for s in ('deterministic_fibre_path.py','test_deterministic_fibre_path.py')}
    text=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
