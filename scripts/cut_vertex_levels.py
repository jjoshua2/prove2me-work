#!/usr/bin/env python3
"""Finite vertex-level closure under cuts; exact ORIGINAL-edge coordinate routes.

A base has a proved coordinate alphabet (box or fractional stable-set system).
A cut image of each base vertex lies in a finite grouped-column spectrum.
Small affine systems then cover EVERY new coordinate, without enumerating
base vertices or edge directions. The actual route uses changing coordinate
objectives; only exact ranks in the alphabet enter its length bound.

Research software, not Lean-extracted. No arbitrary-H alphabet claim is trusted.
The capped exact Bland solver has no polynomial internal-pivot guarantee.
"""
from __future__ import annotations
from fractions import Fraction as Q
from collections import Counter
from itertools import combinations, product
from math import comb
from pathlib import Path
import argparse, hashlib, json
import cut_direction_routes as old

lp=old.lp
require,rat,serial,dot=lp.require,lp.rat,lp.serial,lp.dot


def model(data):
    B=data['base'];d=B['dimension']
    require(type(d)is int and d>0,'positive ambient dimension required')
    eye=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
    A=[tuple(-v for v in a) for a in eye]+eye;b=[Q(0)]*d+[Q(1)]*d
    if B['kind']=='box':levels=(Q(0),Q(1))
    elif B['kind']=='fractional_stable_set':
        edges=B['edges']
        require(type(edges)is list and all(type(e)is list and len(e)==2 and
            all(type(i)is int for i in e) and 0<=e[0]<e[1]<d for e in edges)
            and len(set(map(tuple,edges)))==len(edges),'invalid graph edge list')
        for i,j in edges:A.append(tuple(Q(k in (i,j)) for k in range(d)));b.append(Q(1))
        levels=(Q(0),Q(1,2),Q(1))
    else:raise ValueError('unproved base alphabet; arbitrary H-data not recognized')
    C=tuple(tuple(map(rat,a)) for a in data.get('cuts_A',[]));h=tuple(map(rat,data.get('cuts_b',[])))
    require(len(C)==len(h) and all(len(a)==d for a in C),'cut shape mismatch')
    A,b=tuple(A)+C,tuple(b)+h
    if 'A' in data or 'b' in data:
        AA,bb=lp.parse(data['A'],data['b']);require((A,b)==(AA,bb),'original H description changed')
    return A,b,levels,C,h


def cut_spectrum(C,ids,d,levels,cap):
    """Grouped-column image of the ENTIRE level grid, not sampled base vertices."""
    p=len(ids);groups=Counter(tuple(C[i][j] for i in ids) for j in range(d))
    groups.pop((Q(0),)*p,None);q=len(levels)-1
    # Both recognized alphabets are the full equally-spaced grid in [0,1].
    require(levels==tuple(Q(j,q) for j in range(q+1)),'spectrum requires an exact grid alphabet')
    budget=1
    for count in groups.values():budget*=q*count+1
    require(budget<=cap,'cut-image spectrum cap; no partial inventory returned')
    values={(Q(0),)*p}
    for column,count in sorted(groups.items()):
        values={tuple(x+Q(t,q)*a for x,a in zip(v,column)) for v in values for t in range(q*count+1)}
    return tuple(sorted(values)),{'rows':list(ids),'coefficient_column_types':len(groups),
        'group_sizes':sorted(groups.values()),'grid_image_upper_bound':budget,'distinct_cut_images':len(values)}


def alphabet(data,cap=2000000):
    require(type(cap)is int and cap>0,'positive integer alphabet cap required')
    A,b,L,C,h=model(data);d=len(A[0]);s=len(C);levels=set(L);records=[];bases=feasible=0;preflight=0
    cut_rank=len(old.rref(C,d)[1])
    column_types={tuple(C[i][j] for i in range(s)) for j in range(d)}
    column_types.discard((Q(0),)*s)
    weights={(Q(1),)}
    for r in range(1,cut_rank+1):
        for I in combinations(range(s),r):
            if len(old.rref([C[i] for i in I],d)[1])<r:continue
            images,report=cut_spectrum(C,I,d,L,cap)
            work=comb(len(images),r+1)*len(L)**(r+1)
            preflight+=work
            require(preflight<=cap,'affine-alphabet enumeration cap; incomplete cover rejected')
            report.update(affine_assignments_upper_bound=work);records.append(report)
            rhs=(Q(1),)+tuple(h[i] for i in I)
            for V in combinations(images,r+1):
                if r==1:
                    a,c=V[0][0],V[1][0]
                    if not a<=rhs[1]<=c:continue
                    t=(rhs[1]-a)/(c-a);lam=(1-t,t);bases+=1
                else:
                    M=[(Q(1),)*(r+1)]+[tuple(v[j] for v in V) for j in range(r)]
                    if len(old.rref(M,r+1)[1])!=r+1:continue
                    bases+=1;lam=tuple(dot(row,rhs) for row in old.inverse(M))
                    if any(z<0 for z in lam):continue
                feasible+=1
                # Coordinate assignments are independent of the order of these weights.
                weights.add(tuple(sorted(z for z in lam if z)))
    for lam in weights:
        for values in product(L,repeat=len(lam)):levels.add(dot(lam,values))
    ans=tuple(sorted(levels))
    require(all(0<=x<=1 for x in ans),'invalid convex coordinate alphabet')
    return ans,{'base_levels':serial(L),'cut_rows':s,'cut_rank':cut_rank,'nonzero_joint_column_types':len(column_types),
        'cut_image_records':records,'assignment_preflight':preflight,
        'nonsingular_or_bracketing_image_bases':bases,'nonnegative_barycentric_bases':feasible,
        'distinct_positive_weight_multisets':len(weights),'post_cut_levels':len(ans),
        'all_pair_route_bound':d*(len(ans)-1),'base_vertices_or_directions_enumerated':False}


def vertex_packet(A,b,x):return old.rank_certificate(A,old.active(A,b,x),len(x))


def edge_packet(A,b,x,y):
    require(x!=y,'stationary point offered as an edge')
    return old.rank_certificate(A,sorted(set(old.active(A,b,x))&set(old.active(A,b,y))),len(x)-1)


def extreme_improving_ray(H,rhs,x,witness,cost,pivot_cap,stats):
    d=len(x);J=old.active(H,rhs,x);rows=[H[j] for j in J]
    height=tuple(-sum((a[j] for a in rows),Q(0)) for j in range(d))
    v=tuple(a-b for a,b in zip(witness,x));scale=dot(height,v)
    require(scale>0 and dot(cost,v)>0,'feasible optimizer did not give a positive tangent direction')
    seed=tuple(t/scale for t in v)
    T=tuple(rows)+(height,tuple(-z for z in height));b=(Q(0),)*len(rows)+(Q(1),-Q(1))
    objectives=[cost]+[tuple(Q(i==j) for j in range(d)) for i in range(d)]
    for c in objectives:
        solver=lp.ExactLP(T,b,seed,pivot_cap);out=solver.maximize(c)
        stats['LP_calls']+=1;stats['LP_pivots']+=solver.pivots
        seed,value=lp.verify_optimum(T,b,c,out)
        zero=[a for a in rows if dot(a,seed)==0]
        if len(old.rref(zero,d)[1])==d-1:
            require(dot(cost,seed)>0,'ray refinement lost coordinate progress')
            return seed
        # Exact successive optimization, not a finite epsilon that might change sign.
        T=T+(tuple(c),tuple(-a for a in c));b=b+(value,-value)
    raise ValueError('lexicographic tangent optimizer was not an extreme ray')


def make_leg(A,b,H,rhs,start,witness,coordinate,sign,goal,levels,pivot_cap,edge_cap,stats):
    x=tuple(start);path=[x];cost=tuple(Q(sign*(j==coordinate)) for j in range(len(x)))
    ranks={z:i for i,z in enumerate(levels)}
    require(x[coordinate] in ranks and goal in ranks,'level coverage failed at phase endpoints')
    cap=abs(ranks[x[coordinate]]-ranks[goal])
    while x[coordinate]!=goal:
        require(len(path)-1<min(cap,edge_cap),'rank or edge cap; no completed leg')
        ray=extreme_improving_ray(H,rhs,x,witness,cost,pivot_cap,stats)
        alpha,_=old.base.original.maximal_step(A,b,x,ray)
        require(alpha>0,'zero original edge length')
        y=tuple(z+alpha*v for z,v in zip(x,ray))
        require(all(dot(a,y)<=t for a,t in zip(H,rhs)),'edge left a previously fixed original face')
        require(y[coordinate] in ranks and sign*(y[coordinate]-x[coordinate])>0,'nonmonotone coordinate edge')
        vertex_packet(A,b,y);edge_packet(A,b,x,y);path.append(y);x=y
    return path


def path_packet(A,b,path):
    return serial({'path':path,'vertex_rank':[vertex_packet(A,b,x) for x in path],
        'edge_rank':[edge_packet(A,b,x,y) for x,y in zip(path,path[1:])]})


def input_hash(data):return hashlib.sha256(json.dumps(serial(data),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def construct(data,alphabet_cap=2000000,edge_cap=10000,pivot_cap=20000):
    require(type(edge_cap)is int and edge_cap>=0,'nonnegative integer edge cap required')
    A,b,L,C,h=model(data);levels,info=alphabet(data,alphabet_cap);d=len(A[0])
    u=tuple(map(rat,data['start']));v=tuple(map(rat,data['target']))
    require(len(u)==len(v)==d and all(dot(a,x)<=t for x in (u,v) for a,t in zip(A,b)),'infeasible endpoint')
    vertex_packet(A,b,u);vertex_packet(A,b,v)
    locked=sorted(set(old.active(A,b,u))&set(old.active(A,b,v)))
    H=A+tuple(tuple(-x for x in A[i]) for i in locked);rhs=b+tuple(-b[i] for i in locked)
    stages=[];left=[u];right=[v];rank={x:i for i,x in enumerate(levels)};stats={'LP_calls':0,'LP_pivots':0}
    for j in range(d):
        if u==v:break
        # Both fronts go to the SAME supporting extreme, never an arbitrary section.
        r0,r1=rank[u[j]],rank[v[j]];sign=-1 if r0+r1<=len(levels)-1 else 1
        cost=tuple(Q(sign*(i==j)) for i in range(d));solver=lp.ExactLP(H,rhs,u,pivot_cap)
        optimum=solver.maximize(cost);w,value=lp.verify_optimum(H,rhs,cost,optimum);goal=sign*value
        stats['LP_calls']+=1;stats['LP_pivots']+=solver.pivots
        p=make_leg(A,b,H,rhs,u,w,j,sign,goal,levels,pivot_cap,edge_cap,stats)
        q=make_leg(A,b,H,rhs,v,w,j,sign,goal,levels,pivot_cap,edge_cap,stats)
        require(len(p)+len(q)-2<=len(levels)-1,'joint phase rank charge exceeded')
        left+=p[1:];right+=q[1:];require(len(left)+len(right)-2<=edge_cap,'overall edge cap')
        stages.append(serial({'coordinate':j,'sign':sign,'optimum':optimum,
                              'left':path_packet(A,b,p),'right':path_packet(A,b,q)}))
        u,v=p[-1],q[-1];e=tuple(Q(i==j) for i in range(d))
        H=H+(e,tuple(-x for x in e));rhs=rhs+(goal,-goal)
    require(u==v,'coordinate-face assembly did not join endpoints')
    path=left+list(reversed(right[:-1]))
    cert=serial({'format':'cut-vertex-level-route-v1','input_sha256':input_hash(data),
        'alphabet_cap':alphabet_cap,'alphabet':levels,'alphabet_report':info,
        'locked_original_rows':locked,'endpoint_ranks':[vertex_packet(A,b,left[0]),vertex_packet(A,b,right[0])],
        'stages':stages,'path':path})
    return {'certificate':cert,'verified':verify(data,cert),'discovery':stats}


def check_path(A,b,H,rhs,p):
    path=[tuple(map(rat,x)) for x in p['path']];d=len(A[0])
    require(path and len(path)==len(p['vertex_rank'])==len(p['edge_rank'])+1,'path packet lengths')
    for x,c in zip(path,p['vertex_rank']):
        require(len(x)==d and all(dot(a,x)<=t for a,t in zip(H,rhs)),'point outside retained face')
        I=old.check_rank(A,c,d);require(all(dot(A[i],x)==b[i] for i in I),'original vertex rank not tight')
    for x,y,c in zip(path,path[1:],p['edge_rank']):
        I=old.check_rank(A,c,d-1)
        require(x!=y and all(dot(A[i],x)==dot(A[i],y)==b[i] for i in I),'not an entire original edge')
    return path


def verify(data,c):
    require(c['format']=='cut-vertex-level-route-v1' and c['input_sha256']==input_hash(data),'input binding changed')
    A,b,L,C,h=model(data);levels,info=alphabet(data,c['alphabet_cap']);d=len(A[0])
    require(c['alphabet']==serial(levels) and c['alphabet_report']==info,'incomplete or altered coordinate inventory')
    rank={x:i for i,x in enumerate(levels)};u=tuple(map(rat,data['start']));v=tuple(map(rat,data['target']))
    require(len(c['endpoint_ranks'])==2,'missing endpoint certificates')
    for x,rp in zip((u,v),c['endpoint_ranks']):
        require(len(x)==d and all(dot(a,x)<=t for a,t in zip(A,b)),'infeasible endpoint')
        I=old.check_rank(A,rp,d);require(all(dot(A[i],x)==b[i] for i in I),'endpoint rank not tight')
    locked=sorted(set(old.active(A,b,u))&set(old.active(A,b,v)))
    require(c['locked_original_rows']==locked,'common original facets changed')
    H=A+tuple(tuple(-x for x in A[i]) for i in locked);rhs=b+tuple(-b[i] for i in locked)
    left=[u];right=[v];charges=[]
    for j,s in enumerate(c['stages']):
        require(j<d and type(s['coordinate'])is int and s['coordinate']==j and type(s['sign'])is int and s['sign'] in (-1,1),'invalid phase coordinate')
        sign=s['sign'];r0,r1=rank[u[j]],rank[v[j]]
        require(sign==(-1 if r0+r1<=len(levels)-1 else 1),'not the proved shorter rank side')
        cost=tuple(Q(sign*(i==j)) for i in range(d));w,val=lp.verify_optimum(H,rhs,cost,s['optimum']);goal=sign*val
        require(goal in rank,'extreme coordinate missing from complete alphabet')
        p=check_path(A,b,H,rhs,s['left']);q=check_path(A,b,H,rhs,s['right'])
        require(p[0]==u and q[0]==v and p[-1][j]==q[-1][j]==goal,'phase endpoints not tied to same extreme')
        for path in (p,q):
            require(all(x[j] in rank for x in path),'coordinate not in certified inventory')
            require(all(sign*(y[j]-x[j])>0 for x,y in zip(path,path[1:])),'phase coordinate not strict')
        budget=abs(rank[p[0][j]]-rank[goal])+abs(rank[q[0][j]]-rank[goal])
        edges=len(p)+len(q)-2;require(edges<=budget<=len(levels)-1,'invalid joint rank charge')
        charges.append({'coordinate':j,'edges':edges,'rank_charge':budget})
        left+=p[1:];right+=q[1:];u,v=p[-1],q[-1]
        e=tuple(Q(i==j) for i in range(d));H=H+(e,tuple(-x for x in e));rhs=rhs+(goal,-goal)
    require(u==v,'unfinished face descent')
    # When source=target with no stages, still prove that point is an original vertex.
    if not c['stages']:
        require(len(u)==d and all(dot(a,u)<=t for a,t in zip(A,b)),'invalid stationary endpoint')
    path=left+list(reversed(right[:-1]));require(c['path']==serial(path),'assembled route mismatch')
    require(len(path)-1<=d*(len(levels)-1),'coordinate-level diameter bound failed')
    return {'status':'PASS','ambient_dimension':d,'original_H_rows':len(A),**info,
            'original_edges':len(path)-1,'phase_charges':charges,
            'common_original_rows_retained':len(locked),'whole_base_graph_enumerated':False,
            'single_monotone_objective_claimed':False,'shortest_claimed':False,
            'scope':'Proved-base finite levels and exact cut-image closure; original-edge path, not Lean/Prove2Me verification.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--alphabet-cap',type=int,default=2000000);a=p.parse_args()
    try:
        out=construct(json.loads(a.input.read_text()),a.alphabet_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as e:p.exit(2,f'No completed level route: {e}\n')
if __name__=='__main__':main()
