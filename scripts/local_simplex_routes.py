#!/usr/bin/env python3
"""Automatic local-simplex proposals, global exact tests, and original-H routes.

No simplex directions/lengths/chart are supplied. The proposal is deliberately
local: it is NOT a complete catalogue of all higher-dimensional factors.
Global acceptance uses complete low-rank Farkas obstructions, not local shape.
Core recognition remains a sufficient point/pyramid/feedback test.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
from itertools import combinations
from fractions import Fraction as Q
from exact_farkas_lp import ExactLP,parse,rat,serial,dot,require,problem_hash,verify_dual
from recognized_segment_routes import inverse,rank,verify_edges,erase_redundancy,verify_redundancy
from automatic_segment_routes import identify_core,core_path
from simplex_summand_certificate import extract,verify as verify_simplex,SimplexModel
import implicit_minkowski_lift as lift

def propose(A,b,start,max_rank=2):
    """At a simple vertex all outgoing edges are available. Neighbor cliques
    suggest simplex shapes (rank-two proposals are triangular faces).
    Higher-rank cliques are NOT asserted to be entire simplex faces.
    Nonsimple inputs use only feasible rays from one basis. No completeness
    theorem for global simplex factors is attached to these proposals."""
    d=len(A[0]);x=tuple(map(rat,start));verify_edges(A,b,[x])
    active=[i for i,(a,z) in enumerate(zip(A,b)) if dot(a,x)==z]
    basis=[]
    for i in active:
        if rank([A[j] for j in basis+[i]])>len(basis):basis.append(i)
        if len(basis)==d:break
    inv=inverse([A[i] for i in basis]);neighbors=[]
    for j in range(d):
        g=tuple(-row[j] for row in inv)
        bounds=[(z-dot(a,x))/dot(a,g) for a,z in zip(A,b) if dot(a,g)>0]
        if not bounds:continue
        t=min(bounds)
        if t<=0:continue
        y=tuple(v+t*w for v,w in zip(x,g));verify_edges(A,b,[x,y]);neighbors.append(y)
    adjacency=set()
    for i,j in combinations(range(len(neighbors)),2):
        try:verify_edges(A,b,[neighbors[i],neighbors[j]])
        except ValueError:continue
        adjacency.add((i,j))
    cliques=[]
    for k in range(2,min(max_rank,len(neighbors))+1):
        for I in combinations(range(len(neighbors)),k):
            if all((i,j) in adjacency for i,j in combinations(I,2)):cliques.append(I)
    # Try larger faces first; do not repeat their proper simplex subfaces.
    selected=[I for I in cliques if not any(set(I)<set(J) for J in cliques)]
    shapes=[tuple(tuple(y-v for y,v in zip(neighbors[i],x)) for i in I) for I in selected]
    return shapes,{'simple_source':len(active)==d,'incident_edges_used':len(neighbors),
                   'candidate_shapes':len(shapes),'rank_cap':max_rank}

def endpoint(A,b,rhs,x,summands):
    x=tuple(map(rat,x));verify_edges(A,b,[x]);d=len(x)
    weights=[Q(dot(a,x)==t) for a,t in zip(A,b)]
    c=tuple(sum((w*a[j] for w,a in zip(weights,A)),Q(0)) for j in range(d))
    choices=[];picked=[]
    for block in summands:
        values=[dot(c,v) for v in block];top=max(values);ids=[i for i,t in enumerate(values) if t==top]
        require(len(ids)==1,'ambiguous original endpoint decomposition')
        choices.append(ids[0]);picked.append(block[ids[0]])
    p=tuple(x[j]-sum((v[j] for v in picked),Q(0)) for j in range(d))
    require(all(dot(a,p)<=z for a,z in zip(A,rhs)),'wrong core endpoint')
    require(all(not w or dot(a,p)==z for w,a,z in zip(weights,A,rhs)),'lost original support row')
    return p,weights,choices

def decode(A,b,c):
    rhs=b;blocks=[]
    for step in c['extractions']:
        G=step['simplex_generators'];v=verify_simplex(A,rhs,G,step)
        t=rat(step['removed']);P=SimplexModel(A,rhs,G)
        rhs=tuple(z-t*h for z,h in zip(rhs,P.support))
        if t:blocks.append([(Q(0),)*len(A[0])]+[tuple(t*x for x in g) for g in P.G])
    require(list(rhs)==list(map(rat,c['core_b'])),'wrong residual right-hand sides')
    return rhs,blocks

def route_data(data,c):
    A,b=parse(data['A'],data['b']);rhs,blocks=decode(A,b,c)
    p,sw,choices_s=endpoint(A,b,rhs,data['start'],blocks)
    q,tw,choices_t=endpoint(A,b,rhs,data['end'],blocks)
    keep=verify_redundancy(A,rhs,c['redundancy'])
    path,B=core_path(A,rhs,keep,p,q,c['core'])
    return {'A':A,'b':rhs,'base_route':path,'summands':blocks,'source_weights':sw,'target_weights':tw},B,choices_s,choices_t

def construct_route(data,c):
    inp,B,s,t=route_data(data,c);d=len(inp['A'][0]);blocks=inp['summands']
    gens=[g for block in blocks for g in block[1:]]
    if c['core']['kind']=='point' and rank(gens)==len(gens):
        # Direct-sum simplex factors: every edge changes exactly one factor.
        p=inp['base_route'][0];current=list(s)
        point=lambda ids:tuple(p[j]+sum((block[i][j] for block,i in zip(blocks,ids)),Q(0)) for j in range(d))
        route=[point(current)]
        for i in range(len(blocks)):
            if s[i]!=t[i]:current[i]=t[i];route.append(point(current))
        return serial({'kind':'direct_product','route':route,'lower_bound':sum(a!=b for a,b in zip(s,t))})
    return {'kind':'lift','certificate':lift.build(serial(inp))['certificate']}

def build(data,max_rank=2):
    A,b=parse(data['A'],data['b']);start=tuple(map(rat,data['start']))
    bound_solver=ExactLP(A,b,start);bounds=[]
    for j in range(len(start)):
        for sign in (-1,1):
            obj=tuple(Q(sign*int(i==j)) for i in range(len(start)))
            sol=bound_solver.maximize(obj)
            bounds.append({'coordinate':j,'sign':sign,'dual':sol['dual'],'bound':sol['value']})
    shapes,proposal=propose(A,b,start,max_rank);rhs=b;extractions=[]
    for G in shapes:
        out=extract(A,rhs,G,start)
        step=out['certificate'];extractions.append(step)
        t=rat(step['removed']);P=SimplexModel(A,rhs,G)
        rhs=tuple(z-t*h for z,h in zip(rhs,P.support))
        require(all(dot(a,start)<=z for a,z in zip(A,rhs)),'local-origin core seed lost')
    red=erase_redundancy(A,rhs,start)
    positive=[]
    for step in extractions:
        t=rat(step['removed'])
        if t:positive.append([(Q(0),)*len(start)]+[tuple(t*rat(x) for x in g) for g in step['simplex_generators']])
    p,_,_=endpoint(A,b,rhs,data['start'],positive);q,_,_=endpoint(A,b,rhs,data['end'],positive)
    core=identify_core(A,rhs,red['kept'],p,q)
    c=serial({'problem_sha256':problem_hash(A,b),'proposal':proposal,'extractions':extractions,
              'core_b':rhs,'redundancy':red,'core':core,'boundedness':bounds})
    c['route']=construct_route(data,c)
    return {'certificate':c,'verified':verify(data,c)}

def verify(data,c):
    A,b=parse(data['A'],data['b']);require(c['problem_sha256']==problem_hash(A,b),'changed original H-data')
    d=len(A[0]);seen=set()
    for item in c['boundedness']:
        j,sg=item['coordinate'],item['sign']
        require(type(j)is int and type(sg)is int and 0<=j<d and sg in (-1,1) and (j,sg) not in seen,'bad bound label')
        seen.add((j,sg));obj=tuple(Q(sg*int(i==j)) for i in range(d))
        require(verify_dual(A,b,obj,item['dual'])==rat(item['bound']),'wrong compactness bound')
    require(len(seen)==2*d,'missing compactness certificate')
    inp,B,s,t=route_data(data,c);blocks=inp['summands'];r=c['route']
    if r['kind']=='direct_product':
        gens=[g for block in blocks for g in block[1:]]
        require(c['core']['kind']=='point' and rank(gens)==len(gens),'false direct-sum factorization')
        route=[tuple(map(rat,x)) for x in r['route']]
        lower=sum(a!=b for a,b in zip(s,t))
        require(type(r['lower_bound'])is int and r['lower_bound']==lower==len(route)-1,'false shortestness count')
        bound=len(blocks);short=True
    elif r['kind']=='lift':
        report=lift.verify(serial(inp),r['certificate']);route=[tuple(map(rat,x)) for x in r['certificate']['route']]
        bound=(report['added_directions']+1)*B+report['added_directions'];short=False
    else:raise ValueError('unknown route mode')
    require(route[0]==tuple(map(rat,data['start'])) and route[-1]==tuple(map(rat,data['end'])),'changed requested endpoints')
    L=verify_edges(A,b,route);require(L<=bound,'route count bound')
    return {'status':'PASS','dimension':len(A[0]),'original_rows':len(A),
            'candidate_simplex_shapes':len(c['extractions']),'positive_simplex_factors':len(blocks),
            'removed_dimensions':[len(block)-1 for block in blocks],'core_kind':c['core']['kind'],
            'ordinary_edges':L,'all_endpoint_bound':bound,'shortest_certified':short,
            'candidate_shapes_supplied':False,'global_simplex_catalogue_complete':False,
            'scope':'Exact tested simplex decomposition and original-H ordinary edges. Local proposals are not globally complete.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);ap.add_argument('--max-rank',type=int,default=2);ap.add_argument('--output',type=Path)
    a=ap.parse_args()
    try:
        data=json.loads(a.input.read_text());out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else build(data,a.max_rank)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:ap.exit(2,f'No recognized simplex route: {e}\n')
if __name__=='__main__':main()
