#!/usr/bin/env python3
"""Original-H route after removing a supplied finite nonsegment summand SHAPE.

Shape vertices are inputs. Its maximal scale, residual H-data, short residual
route and exact exposing objectives are discovered and checked. Uses the earlier
point/pyramid/feedback recognizer plus a directly certified simplex core. The
unchanged implicit Minkowski lifter certifies whole exposed edges of the sum.
Final edges are independently verified on the ORIGINAL input inequalities.

This is not universal shape discovery or a general segment-free residual solver.
"""
from __future__ import annotations
import argparse,json
from fractions import Fraction as Q
from pathlib import Path
from exact_farkas_lp import parse,rat,serial,dot,require,problem_hash,verify_dual
from antipodal_segment_catalogue import boundedness_certificate
from finite_summand_capacity import Data,discover,verify as verify_capacity
from recognized_segment_routes import erase_redundancy,verify_redundancy,rank,verify_edges,inverse
from automatic_segment_routes import identify_core,core_path
import implicit_minkowski_lift as lifter


def projected_endpoint(A,b,rhs,x,points):
    x=tuple(map(rat,x));d=len(x)
    require(all(dot(a,x)<=t for a,t in zip(A,b)),'infeasible original endpoint')
    active=[i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t]
    require(rank([A[i] for i in active])==d,'requested endpoint not a vertex')
    w=[Q(int(i in active)) for i in range(len(A))]
    c=tuple(sum((A[i][j] for i in active),Q(0)) for j in range(d))
    value=max(dot(c,g) for g in points);choices=[g for g in points if dot(c,g)==value]
    require(len(choices)==1,'ambiguous candidate support at original vertex')
    p=tuple(u-v for u,v in zip(x,choices[0]))
    require(all(dot(a,p)<=t for a,t in zip(A,rhs)),'projected endpoint outside residual')
    require(all(dot(A[i],p)==rhs[i] for i in active),'endpoint supporting rows not inherited')
    return p,w


def simplex_core(A,rhs,keep):
    d=len(A[0]);require(len(keep)==d+1,'not a full-dimensional simplex row count')
    vertices=[]
    for omit in keep:
        I=[i for i in keep if i!=omit];inv=inverse([A[i] for i in I])
        x=tuple(dot(row,[rhs[i] for i in I]) for row in inv)
        require(all(dot(a,x)<=t for a,t in zip(A,rhs)),'simplex candidate outside residual')
        require(dot(A[omit],x)<rhs[omit],'collapsed simplex facet')
        vertices.append(x)
    require(len(set(vertices))==d+1,'duplicate simplex vertices')
    return {'kind':'simplex','vertices':serial(vertices)}


def get_core(A,rhs,keep,source,target):
    try:return simplex_core(A,rhs,keep)
    except ValueError:return identify_core(A,rhs,keep,source,target)


def route_core(A,rhs,keep,source,target,c):
    if c['kind']!='simplex':return core_path(A,rhs,keep,source,target,c)
    expected=simplex_core(A,rhs,keep)
    require(c==expected,'false simplex certificate')
    V=[tuple(map(rat,v)) for v in c['vertices']]
    require(source in V and target in V,'simplex endpoint not in its complete vertex list')
    path=[source] if source==target else [source,target];verify_edges(A,rhs,path)
    return path,1


def lift_input(data,c,subset_cap=300000):
    A,b=parse(data['A'],data['b']);P=Data(A,b,data['candidate_vertices'],subset_cap)
    tau=rat(c['capacity_certificate']['removed']);rhs=P.rhs(tau)
    points=sorted(set([(Q(0),)*P.d]+[tuple(tau*z for z in g) for g in P.G]))
    s,sw=projected_endpoint(A,b,rhs,data['start'],points)
    t,tw=projected_endpoint(A,b,rhs,data['end'],points)
    keep=verify_redundancy(A,rhs,c['redundancy'])
    path,bound=route_core(A,rhs,keep,s,t,c['core'])
    return serial({'A':A,'b':rhs,'base_route':path,'summands':[points],
        'source_weights':sw,'target_weights':tw}),bound


def build(data,subset_cap=300000,pivot_cap=20000):
    A,b=parse(data['A'],data['b']);found=discover(A,b,data['candidate_vertices'],data['start'],
        subset_cap=subset_cap,pivot_cap=pivot_cap)
    P=Data(A,b,data['candidate_vertices'],subset_cap);cc=found['certificate'];tau=rat(cc['removed']);rhs=P.rhs(tau)
    red=erase_redundancy(A,rhs,tuple(map(rat,cc['core_seed'])),pivot_cap)
    points=sorted(set([(Q(0),)*P.d]+[tuple(tau*z for z in g) for g in P.G]))
    source,_=projected_endpoint(A,b,rhs,data['start'],points);target,_=projected_endpoint(A,b,rhs,data['end'],points)
    keep=verify_redundancy(A,rhs,red);core=get_core(A,rhs,keep,source,target)
    bounds,_=boundedness_certificate(A,b,tuple(map(rat,data['start'])),pivot_cap)
    c={'problem_sha256':problem_hash(A,b),'capacity_certificate':cc,'redundancy':red,'core':core,'boundedness':bounds}
    inp,_=lift_input(data,c,subset_cap);c['lift']=lifter.build(inp)['certificate']
    return {'certificate':c,'verified':verify(data,c,subset_cap),'discovery':found['discovery']}


def verify(data,c,subset_cap=300000):
    A,b=parse(data['A'],data['b']);require(c['problem_sha256']==problem_hash(A,b),'original H-data changed')
    seen=set();d=len(A[0])
    for item in c['boundedness']:
        j,sg=item['coordinate'],item['sign']
        require(type(j)is int and 0<=j<d and type(sg)is int and sg in (-1,1) and (j,sg) not in seen,'invalid boundedness coordinate')
        seen.add((j,sg));objective=tuple(Q(sg)*Q(i==j) for i in range(d))
        require(verify_dual(A,b,objective,item['dual'])==rat(item['bound']),'false original coordinate bound')
    require(len(seen)==2*d,'original compactness certificate incomplete')
    cap=verify_capacity(A,b,data['candidate_vertices'],c['capacity_certificate'],subset_cap)
    inp,bound=lift_input(data,c,subset_cap);r=lifter.verify(inp,c['lift'])
    path=[tuple(map(rat,p)) for p in c['lift']['route']]
    require(path[0]==tuple(map(rat,data['start'])) and path[-1]==tuple(map(rat,data['end'])),'requested endpoints changed')
    edges=verify_edges(A,b,path);q=r['added_directions']
    # A single finite candidate has at most v-1 genuine support changes on
    # each linear objective segment: each affine support line wins on an interval.
    nv=len(inp['summands'][0]);per_leg=min(q,nv-1)
    if c['lift'].get('kind')=='normal_itinerary':
        for j in range(r['base_edges']+1):
            events=[e for e in c['lift']['events'] if e['kind']=='wall' and e['leg']==j]
            choices=[]
            for e in events:
                u,v=e['before_choices'][0],e['after_choices'][0]
                if not choices: choices.append(u)
                require(choices[-1]==u and v not in choices,'a candidate maximizer reappeared within one objective segment')
                choices.append(v)
            require(len(events)<=per_leg,'finite candidate support-change count failed')
    require(edges<=(per_leg+1)*bound+per_leg,'core-to-original budget failure')
    return {**cap,'core_kind':c['core']['kind'],'core_rows':len(c['redundancy']['kept']),
        'candidate_direction_lines':q,'core_route_edges':r['base_edges'],'original_ordinary_edges':edges,
        'refinement_changes_per_segment':per_leg,'recognized_model_diameter_bound':(per_leg+1)*bound+per_leg,'candidate_shape_supplied':True,
        'scale_or_residual_or_route_supplied':False,
        'scope':'Exact finite-summand equality, maximality and original-H graph route; no universal candidate discovery or Lean verdict.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);a=p.parse_args()
    try:
        d=json.loads(a.input.read_text());r=verify(d,json.loads(a.certificate.read_text())) if a.certificate else build(d)
        text=json.dumps(serial(r),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,ZeroDivisionError,OSError) as e:p.exit(2,f'No recognized nonsegment route: {e}\n')
if __name__=='__main__':main()
