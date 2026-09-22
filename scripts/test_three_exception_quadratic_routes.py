#!/usr/bin/env python3
"""Exact nested original-row incidence checks; not Lean or parser verification.

The original hull/edge reference and route producer are reused unchanged. New
certificates contain a complete motion basis and per-row planar incidence tables.
The consumer reconstructs the tables independently and checks serialized data.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import sympy as sp
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old
import test_few_exception_target_routes as few


def require(ok, message):
    if not ok:
        raise ValueError(message)


def kernel(rows, labels, dimension):
    matrix=sp.Matrix([rows[i][:-1] for i in sorted(labels)]) if labels else sp.zeros(0,dimension)
    return [tuple(Q(x) for x in v) for v in matrix.nullspace()]


def table(model, rows, vertices, basis):
    V=model['vertices']; d=len(V[0]); r=len(basis)
    I=[i for i,row in enumerate(rows) if any(g.dot(row[:-1],z) for z in basis)]
    pairs=[[i,[x for x in vertices if i in old.active(rows,V[x])]] for i in I]
    vertex_rows=[[x, sorted(old.active(rows,V[x]) & set(I))] for x in vertices]
    return dict(vertices=vertices,basis=basis,dimension=r,nonzero_rows=I,
                row_incidence=pairs,vertex_incidence=vertex_rows,
                total=sum(len(X) for _,X in pairs))


def make_certificate(model,rows,v,B):
    few.check_B(model,rows,v,B); require(len(B)<=3,'more than three exceptions')
    V=model['vertices']; d=len(V[0]); G=old.active(rows,V[v])-set(B)
    D=[x for x in range(len(V)) if G<=old.active(rows,V[x])]
    basis=kernel(rows,G,d); primary=table(model,rows,D,basis)
    slices=[]
    for i,X in primary['row_incidence']:
        slices.append(dict(label=i,table=table(model,rows,X,kernel(rows,G|{i},d))))
    return dict(target=v,exceptions=sorted(B),good=sorted(G),vertices=D,
                bound=len(rows)**2+1,primary=primary,slices=slices)


def consume_table(model,rows,T,vertices,expected_basis,max_dimension):
    V=model['vertices']; d=len(V[0]); basis=[tuple(map(Q,z)) for z in T['basis']]
    r=len(basis)
    require(T['vertices']==vertices,'missing slice or residual vertex')
    require(all(len(z)==d for z in basis),'wrong ambient dimension')
    require(r==T['dimension'] and r<=max_dimension,'incorrect dimension')
    require(g.rank(basis)==r==len(expected_basis),'dependent or incomplete basis')
    require(g.rank(basis+expected_basis)==r,'wrong kernel subspace')
    if vertices:
        origin=V[vertices[0]]
        require(all(g.rank(basis+[g.sub(V[x],origin)])==r for x in vertices),'difference outside kernel')
    I=[i for i,row in enumerate(rows) if any(g.dot(row[:-1],z) for z in basis)]
    rr=[[i,[x for x in vertices if i in old.active(rows,V[x])]] for i in I]
    vr=[[x,sorted(old.active(rows,V[x]) & set(I))] for x in vertices]
    require(T['nonzero_rows']==I,'zero restriction included or nonzero row omitted')
    require(T['row_incidence']==rr and T['vertex_incidence']==vr,'incorrect incidence table')
    total=sum(len(X) for _,X in rr)
    require(total==T['total']==sum(len(J) for _,J in vr),'double-count mismatch')
    for x,J in vr:
        restrictions=[[g.dot(rows[i][:-1],z) for z in basis] for i in J]
        require(g.rank(restrictions)==r and len(J)>=r,'active restrictions fail injectivity')
    if r<=1:
        require(len(vertices)<=2,'too many extreme points on a line')
    elif r==2:
        require(all(len(X)<=2 for _,X in rr),'nonzero planar row slice exceeds two')
        require(2*len(vertices)<=total<=2*len(I),'planar incidence inequality')
        require(len(vertices)<=len(rows),'planar vertex inequality')
    if max_dimension<=2:
        require(len(vertices)<=len(rows)+1,'uniform planar bound')
    return r,total,I,rr


def consume_certificate(model,rows,c):
    V=model['vertices'];d=len(V[0]);m=len(rows);v=c['target'];B=c['exceptions']
    require(0<=v<len(V),'invalid target')
    few.check_B(model,rows,v,B);require(len(B)<=3,'more than three exceptions')
    G=old.active(rows,V[v])-set(B)
    D=[x for x in range(len(V)) if G<=old.active(rows,V[x])]
    require(c['good']==sorted(G) and c['vertices']==D,'incorrect retained face')
    basis=kernel(rows,G,d)
    r,total,I,rr=consume_table(model,rows,c['primary'],D,basis,3)
    require(r<=len(B),'exception evaluations fail dimensional bound')
    require([x['label'] for x in c['slices']]==I,'missing or duplicate row slices')
    for (i,X),rec in zip(rr,c['slices']):
        sr,_,_,_=consume_table(model,rows,rec['table'],X,kernel(rows,G|{i},d),2)
        require(sr==r-1,'nonzero restriction did not reduce dimension')
    if r==3:
        require(3*len(D)<=total<=len(I)*(m+1)<=m*(m+1),'spatial incidence inequality')
    require(c['bound']==m*m+1 and len(D)<=c['bound'],'quadratic vertex bound')
    return True


def cases():
    ans=old.cases()
    ans += [('three_roofs',few.roof_points(1,3),False),
            ('two_roofs',few.roof_points(2,2),False),
            ('hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],False),
            ('polygon_prism',[(i,i*i,t) for i in range(6) for t in (0,1)],False),
            ('moment4_exclusion',[(i,i*i,i**3,i**4) for i in range(7)],False)]
    return ans


def controls(model,rows,c,route):
    mutations=[
        ('oversized exceptions',lambda x:x.update(exceptions=list(range(4)))),
        ('missing residual vertex',lambda x:x['vertices'].pop()),
        ('missing row slice',lambda x:x['slices'].pop()),
        ('incorrect dimension',lambda x:x['primary'].update(dimension=4)),
        ('zero motion basis',lambda x:x['primary'].update(basis=[[0]*len(z) for z in x['primary']['basis']])),
        ('false total',lambda x:x['primary'].update(total=x['primary']['total']+1)),
        ('wrong bound',lambda x:x.update(bound=1)),
        ('false planar table',lambda x:x['slices'][0]['table'].update(total=-1)),
    ]
    out=[]
    for name,mutate in mutations:
        candidate=deepcopy(c);mutate(candidate)
        try: consume_certificate(model,rows,candidate)
        except (ValueError,AssertionError):out.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted malformed certificate: '+name)
    for name,mutate in [
        ('wrong endpoint',lambda x:x.update(v=x['u'])),
        ('stationary edge',lambda x:x['records'][0]['edge'].update(v=x['path'][0])),
        ('wrong prefix',lambda x:x.update(prefix_length=x['prefix_length']+1)),
    ]:
        candidate=deepcopy(route);mutate(candidate)
        try:few.consume(model,rows,c,candidate)
        except (ValueError,AssertionError):out.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted malformed route: '+name)
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--only',default='all')
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    reports=[];fixtures=[];bad=[]
    for name,points,extra in cases():
        if args.only!='all' and args.only!=name:continue
        model=g.reference(points);rows=old.h_rows(model);V=model['vertices'];d=len(V[0]);m=len(rows)
        if extra:rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])];m=len(rows)
        old.validate_h(model,rows)
        certs=[];routes=[];rejected=new_targets=edges=shortest=nonshortest=nonacq=slice_over_two=0
        dims={i:0 for i in range(4)}
        distances=[old.distances(model,u) for u in range(len(V))]
        for v in range(len(V)):
            B=few.bad_rows(model,rows,v)
            if len(B)>3:rejected+=1;continue
            new_targets+=len(B)==3
            options=[B]
            extraB=B | set(sorted(old.active(rows,V[v])-B)[:3-len(B)])
            if extraB!=B:options.append(extraB)
            for B1 in options:
                c=make_certificate(model,rows,v,B1);consume_certificate(model,rows,c)
                dims[c['primary']['dimension']]+=1;certs.append(c)
                slice_over_two+=sum(len(s['table']['vertices'])>2 for s in c['slices'])
                for u in range(len(V)):
                    route=few.produce(model,rows,u,v,c);few.consume(model,rows,c,route)
                    routes.append(dict(certificate=len(certs)-1,route=route))
                    L=len(route['path'])-1;dist=distances[u][v]
                    edges+=L;shortest+=dist;nonshortest+=L>dist
                    nonacq+=sum(s['before']==s['after'] for s in route['records'])
                    if name=='three_roofs' and not bad and u!=v:
                        bad=controls(model,rows,c,route)
        frozen=json.loads(json.dumps(g.encoded(dict(certificates=certs,routes=routes))))
        originals=(globals()['make_certificate'],few.produce,g.improving_edge)
        def disabled(*a,**kw):raise RuntimeError('producer disabled')
        globals()['make_certificate']=few.produce=g.improving_edge=disabled
        try:
            for c in frozen['certificates']:consume_certificate(model,rows,c)
            for r in frozen['routes']:few.consume(model,rows,frozen['certificates'][r['certificate']],r['route'])
        finally:globals()['make_certificate'],few.produce,g.improving_edge=originals
        result=dict(name=name,dimension=d,vertices=len(V),rows=m,qualifying_targets=len(V)-rejected,
            newly_admitted_three_exception_targets=new_targets,rejected_targets=rejected,
            certificates=len(certs),residual_dimensions=dims,
            nonzero_row_slices_with_more_than_two_vertices=slice_over_two,
            routes=len(routes),edges=edges,shortest_edges=shortest,nonshortest_routes=nonshortest,
            nonacquiring_steps=nonacq)
        reports.append(result);fixtures.append(dict(name=name,points=model['points'],rows=rows,**frozen))
        print(json.dumps(result),flush=True)
    (args.out/'report.json').write_text(json.dumps(dict(kind='exact_computation_not_Lean_verification',models=reports),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    (args.out/'negative-controls.json').write_text(json.dumps(dict(controls=bad),indent=2)+'\n')

if __name__=='__main__':main()
