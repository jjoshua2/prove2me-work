#!/usr/bin/env python3
"""Replay saved cactus certificates with planner, geometry producer and route
constructor disabled. Geometry uses original-row rational checks. This is not
Lean extraction; it does not infer shortest distances or recompute the BFS data.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
import argparse, copy, json
import cactus_defect_refinement as C
import test_cactus_defect_refinement as T


def forbidden(*args, **kwargs): raise RuntimeError('producer disabled in saved audit')


def geometry_check(raw, r):
    A=tuple(tuple(Q(x)for x in row)for row in raw['A']);b=tuple(map(Q,raw['b']))
    q=4*r;n=2*q+2;points=list(A[:n]);F=[]
    for i in range(q):
        j=(i+1)%q;F.extend([{2*q,i,j},{2*q+1,q+i,q+j},{i,j,q+i},{j,q+i,q+j}])
    F=C.base.ordered(F)
    for f in F:T.support(points,f)
    for log in raw['stacking']:
        f=frozenset(log['facet']);C.require(f in F and log['new_label']==len(points),'bad stack facet/label')
        a,beta=T.support(points,f);eps=Q(log['epsilon']);C.require(eps>0,'nonpositive stack step')
        center=tuple(sum((points[i][j]for i in f),Q(0))/3 for j in range(3))
        z=tuple(Q(x)for x in log['point']);C.require(z==tuple(x+eps*y for x,y in zip(center,a)),'false outward stack position')
        C.require(T.dot(a,z)>beta,'new point not beyond selected facet')
        for h in F:
            if h!=f:
                c,d=T.support(points,h);C.require(T.dot(c,z)<d,'stack sees other facet')
        label=len(points);points.append(z)
        F=C.base.ordered([h for h in F if h!=f]+[{label,*e}for e in combinations(f,2)])
    C.require(tuple(points)==A and F==list(map(frozenset,raw['facets'])),'stack history not bound to original H data')
    K=T.missing(len(A),F);C.require(K.payload()==raw['complex'],'incomplete minimal nonfaces')
    for i,z in enumerate(raw['anchors']):
        z=tuple(map(Q,z));C.require(all(T.dot(a,z)==1 if i==j else T.dot(a,z)<1 for j,a in enumerate(A)),'bad facet anchor')
    C.verify(K,raw['refinement'])
    for saved in raw['saved_routes']:
        route=saved['route'];steps,_=C.flatten(K,raw['refinement'])
        path=C.base.transport(K,steps,route['refined_path'],3)
        C.require([sorted(f)for f in path]==route['original_path'],'bad projected path')
        coords=[tuple(map(Q,x))for x in saved['coordinates']]
        C.require(len(coords)==len(path),'wrong coordinate count')
        for x,y,f,h in zip(coords,coords[1:],path,path[1:]):T.edge_audit(A,b,x,y,f,h)
    return K,A,b,sum(s['route']['original_edges']for s in raw['saved_routes'])


def run(folder):
    C.select=C.construct=C.with_twin_prelude=C.flag_route=forbidden
    T.geometric_bouquet=T.wedge=forbidden
    records={};edges=0
    for r in (1,2,3):
        raw=json.loads((folder/f'cactus-polytope-r{r}.json').read_text())
        K,A,b,n=geometry_check(raw,r);records[r]=(K,A,b);edges+=n
    raw=json.loads((folder/'cactus-wedge-route.json').read_text());K0,A0,b0=records[3]
    A=tuple(tuple(map(Q,row))for row in raw['A']);b=tuple(map(Q,raw['b']));w=len(A[0])-3;n=K0.n
    selected=[]
    C.require(len(A)==n+w and b==tuple([Q(1)]*n+[Q(0)]*w),'bad wedge dimensions/RHS')
    for j in range(w):
        owners=[i for i in range(n)if A[i][3+j]!=0]
        C.require(len(owners)==1 and A[owners[0]][3+j]==1,'bad wedge upper row');selected.append(owners[0])
        C.require(A[n+j]==tuple(Q(-int(t==3+j))for t in range(3+w)),'bad lower row')
    C.require(len(set(selected))==w and tuple(row[:3]for row in A[:n])==A0,'changed base rows')
    subst={i:{i,n+j}for j,i in enumerate(selected)}
    KK=C.Complex.create(n+w,[set().union(*(subst.get(i,{i})for i in N))for N in K0.missing])
    C.require(KK.payload()==raw['complex'],'incorrect complete wedge nonfaces')
    C.verify_prelude(KK,raw['refinement']);steps,_=C.flatten(KK,raw['refinement'])
    path=C.base.transport(KK,steps,raw['route']['refined_path'],3+w)
    C.require([sorted(f)for f in path]==raw['route']['original_path'],'incorrect wedge carriers')
    coords=[tuple(map(Q,x))for x in raw['coordinates']]
    for x,y,f,h in zip(coords,coords[1:],path,path[1:]):T.edge_audit(A,b,x,y,f,h)
    for i,x in enumerate(raw['anchors']):
        z=tuple(map(Q,x));C.require(all(T.dot(a,z)==beta if i==j else T.dot(a,z)<beta for j,(a,beta)in enumerate(zip(A,b))),'false original facet anchor')
    edges+=len(path)-1
    rejected=0
    for change in ('edge','potential'):
        rr=copy.deepcopy(raw)
        if change=='edge':rr['coordinates'][1][0]=str(Q(rr['coordinates'][1][0])+1)
        else:rr['refinement']['tail']['initial']['potential']+=1
        try:
            if change=='edge':T.edge_audit(A,b,coords[0],tuple(map(Q,rr['coordinates'][1])),path[0],path[1])
            else:C.verify_prelude(KK,rr['refinement'])
        except ValueError:rejected+=1
        else:raise AssertionError('saved forgery accepted')
    return {'status':'PASS','saved_models':4,'audited_original_edges':edges,
            'rejected_saved_forgeries':rejected,'selectors_and_producers_disabled':True,
            'scope':'Operation and original-edge replay; no shortest-distance or Lean claim.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('fixtures',type=Path);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    r=run(a.fixtures);a.out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r)
