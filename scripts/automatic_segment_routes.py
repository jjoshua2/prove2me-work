#!/usr/bin/env python3
"""Original A,b,start,end -> complete segment discovery -> certified direct route.

No candidate directions, parent polytope, parent route, or affine chart supplied.
The complete extractor can leave a lower-dimensional core. A zero-dimensional
core or a pyramid apex is certified directly from retained H-rows. A previously
proved feedback-chart test is a fallback. Failed recognition does NOT invalidate
an already successful complete segment catalogue and is not a diameter claim.
"""
from __future__ import annotations
import argparse,json
from fractions import Fraction as Q
from pathlib import Path
from antipodal_segment_catalogue import catalogue,verify_catalogue
from exact_farkas_lp import parse,rat,serial,dot,require,problem_hash
from recognized_segment_routes import erase_redundancy,verify_redundancy,endpoint_data,feedback_route,verify_edges,rank
import implicit_minkowski_lift as lifter


def solve_equations(A,b,d):
    rows=[list(a)+[t] for a,t in zip(A,b)];pivots=[];k=0
    for j in range(d):
        p=next((i for i in range(k,len(rows)) if rows[i][j]),None)
        if p is None:continue
        rows[k],rows[p]=rows[p],rows[k];v=rows[k][j];rows[k]=[x/v for x in rows[k]]
        for i in range(len(rows)):
            if i!=k and rows[i][j]:
                v=rows[i][j];rows[i]=[x-v*y for x,y in zip(rows[i],rows[k])]
        pivots.append(j);k+=1
    if any(not any(row[:d]) and row[-1] for row in rows):return None
    if k!=d:return None
    x=[Q(0)]*d
    for row,j in zip(rows,pivots):x[j]=row[-1]
    return tuple(x)


def identify_core(A,b,keep,source,target):
    """Boundedness inherited from original input, not assumed from row counts."""
    d=len(source)
    point=solve_equations([A[i] for i in keep],[b[i] for i in keep],d)
    if point is not None:return {'kind':'point','point':serial(point)}
    for excluded in keep:
        rows=[i for i in keep if i!=excluded]
        point=solve_equations([A[i] for i in rows],[b[i] for i in rows],d)
        if point is not None and dot(A[excluded],point)<b[excluded]:
            return {'kind':'pyramid','apex':serial(point),'base_row':excluded}
    try:
        _,chart=feedback_route(A,b,keep,source,target)
        return {'kind':'feedback','chart':chart}
    except ValueError as exc:
        raise ValueError('complete catalogue obtained, but residual is not recognized as point/pyramid/feedback core') from exc


def core_path(A,b,keep,source,target,c):
    """The global row certificate proves the core class. Edge ranks then check
    the particular requested path independently of that all-endpoint argument."""
    d=len(source);kind=c['kind']
    if kind=='point':
        x=tuple(map(rat,c['point']))
        require(len(x)==d and rank([A[i] for i in keep])==d and all(dot(A[i],x)==b[i] for i in keep),'invalid point-core equalities')
        require(source==x==target,'point-core endpoint disagreement')
        path=[x];bound=0
    elif kind=='pyramid':
        x=tuple(map(rat,c['apex']));j=c['base_row']
        require(type(j)is int and j in keep and len(x)==d,'invalid pyramid labels')
        require(dot(A[j],x)<b[j] and all(dot(A[i],x)==b[i] for i in keep if i!=j),'apex is not common to every other retained face')
        require(all(dot(a,x)<=t for a,t in zip(A,b)),'pyramid apex not in original residual')
        require(rank([A[i] for i in keep if i!=j])==d,'apex not uniquely fixed')
        path=[]
        for y in [source,x,target]:
            if not path or y!=path[-1]:path.append(y)
        if source==target:path=[source]
        bound=2
    elif kind=='feedback':
        path,_=feedback_route(A,b,keep,source,target,c['chart']);bound=d
    else:raise ValueError('unknown residual core')
    verify_edges(A,b,path)
    return path,bound


def make_lift(data,c):
    A,b=parse(data['A'],data['b']);p=c['catalogue']['peeling']
    rhs=tuple(map(rat,p['core_b']));segs=[tuple(map(rat,g)) for g in p['segments']]
    source,sw=endpoint_data(A,b,rhs,data['start'],segs)
    target,tw=endpoint_data(A,b,rhs,data['end'],segs)
    keep=verify_redundancy(A,rhs,c['redundancy'])
    path,bound=core_path(A,rhs,keep,source,target,c['core'])
    inp={'A':A,'b':rhs,'base_route':path,'summands':[[[Q(0)]*len(A[0]),g] for g in segs],
         'source_weights':sw,'target_weights':tw}
    return serial(inp),bound


def build(data,pivot_cap=20000):
    A,b=parse(data['A'],data['b'])
    require('candidate_directions' not in data,'automatic entry point does not consume supplied directions')
    # Standalone catalogue is a separate successful artifact if core recognition fails.
    cat=catalogue(A,b,data['start'],pivot_cap=pivot_cap)['certificate']
    p=cat['peeling'];rhs=tuple(map(rat,p['core_b']));seed=tuple(map(rat,p['core_seed']))
    red=erase_redundancy(A,rhs,seed,pivot_cap)
    keep=verify_redundancy(A,rhs,red);segs=[tuple(map(rat,g)) for g in p['segments']]
    source,_=endpoint_data(A,b,rhs,data['start'],segs);target,_=endpoint_data(A,b,rhs,data['end'],segs)
    core=identify_core(A,rhs,keep,source,target)
    c={'problem_sha256':problem_hash(A,b),'catalogue':cat,'redundancy':red,'core':core}
    inp,_=make_lift(data,c);c['lift']=lifter.build(inp)['certificate']
    c['lower_bound']=lower_bound_witness(A,b,data['start'],data['end'],cat['peeling']['segments'])
    return {'certificate':c,'verified':verify(data,c)}


def verify(data,c):
    A,b=parse(data['A'],data['b']);d=len(A[0])
    require(c['problem_sha256']==problem_hash(A,b),'changed original H-data')
    cat=verify_catalogue(A,b,c['catalogue']['walk']['route'][0],c['catalogue'])
    inp,bound=make_lift(data,c);report=lifter.verify(inp,c['lift'])
    path=[tuple(map(rat,x)) for x in c['lift']['route']]
    require(path[0]==tuple(map(rat,data['start'])) and path[-1]==tuple(map(rat,data['end'])),'changed requested route endpoints')
    length=verify_edges(A,b,path);q=report['added_directions']
    require(q==cat['positive_segment_directions'],'factor count changed')
    require(length<=(q+1)*bound+q,'coarse lift bound failed')
    lower=verify_lower_bound(A,b,data['start'],data['end'],c['catalogue']['peeling']['segments'],c['lower_bound'])
    require(lower<=length,'invalid route versus certified lower bound')
    return {'status':'PASS','dimension':d,'original_rows':len(A),
            'diagnostic_walk_edges':cat['walk_edges'],'tested_candidate_directions':cat['candidate_directions'],
            'positive_segment_directions':q,'zero_capacity_candidates':cat['zero_capacity_candidates'],
            'complete_maximal_zonotope_factor':True,'residual_segment_free':True,
            'core_kind':c['core']['kind'],'core_all_endpoint_bound':bound,
            'actual_original_route_edges':length,'model_all_endpoint_bound':(q+1)*bound+q,
            'certified_distance_lower_bound':lower,'shortest_certified':length==lower,
            'diagnostic_basis_pivots':c['catalogue']['walk']['discovery']['original_basis_pivots'],
            'diagnostic_stationary_pivots':c['catalogue']['walk']['discovery']['stationary_pivots'],
            'original_graph_enumerated':False,'candidate_directions_supplied':False,
            'scope':'Exact complete discovery and original-edge route; no uniform pivot bound or universal residual-core solver.'}



def kernel_basis(rows,d):
    a=[list(map(rat,r)) for r in rows];k=0;piv=[]
    for j in range(d):
        i=next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None:continue
        a[k],a[i]=a[i],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][j]:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
    out=[]
    for j in range(d):
        if j in piv:continue
        g=[Q(0)]*d;g[j]=1
        for row,i in zip(a,piv):g[i]=-row[j]
        out.append(tuple(g))
    return out


def endpoint_normal(A,b,x):
    x=tuple(map(rat,x));ids=[i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t]
    require(rank([A[i] for i in ids])==len(x),'lower-bound endpoint not a vertex')
    return tuple(sum((A[i][j] for i in ids),Q(0)) for j in range(len(x)))


def lower_bound_witness(A,b,start,end,segments):
    S=[tuple(map(rat,g)) for g in segments];d=len(A[0]);delta=tuple(rat(y)-rat(x) for x,y in zip(start,end))
    normal=next((h for h in kernel_basis(S,d) if dot(h,delta)),None)
    cs,ct=endpoint_normal(A,b,start),endpoint_normal(A,b,end)
    flips=sum((dot(cs,g)>0)!=(dot(ct,g)>0) for g in S)
    return serial({'segment_bit_changes':flips,'quotient_separator':normal})


def verify_lower_bound(A,b,start,end,segments,c):
    S=[tuple(map(rat,g)) for g in segments];d=len(A[0]);cs=endpoint_normal(A,b,start);ct=endpoint_normal(A,b,end)
    require(all(dot(cs,g) and dot(ct,g) for g in S),'ambiguous segment endpoint')
    flips=sum((dot(cs,g)>0)!=(dot(ct,g)>0) for g in S)
    require(type(c['segment_bit_changes'])is int and c['segment_bit_changes']==flips,'forged summand-bit lower bound')
    extra=0
    if c['quotient_separator'] is not None:
        h=tuple(map(rat,c['quotient_separator']));delta=tuple(rat(y)-rat(x) for x,y in zip(start,end))
        require(len(h)==d and all(dot(h,g)==0 for g in S) and dot(h,delta)!=0,'invalid quotient separator')
        extra=1
    return flips+extra


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--pivot-cap',type=int,default=20000);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else build(data,a.pivot_cap)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No recognized automatic route: {exc}\n')
if __name__=='__main__':main()
