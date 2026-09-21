#!/usr/bin/env python3
"""Exact regression for one-exception original-row routes, not Lean verification.

Small models use independent exhaustive hull geometry. Large roof models use
explicit vertex and common-row rank certificates, without enumerating a graph.
The exceptional scalar can have exponentially many levels; none are enumerated
in the large-model route producer or consumer.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import test_target_two_level_routes as old
import test_geometric_coordinate_routes as g


def exceptions(model, rows, v):
    V=model['vertices']; T=old.active(rows,V[v])
    bad={i for i in T if len({g.dot(rows[i][:-1],x) for x in V})>2}
    if len(bad)>1: raise ValueError('more than one exceptional target row')
    return bad


def produce(model,rows,u,v):
    old.validate_h(model,rows)
    B=exceptions(model,rows,v); V=model['vertices']; T=old.active(rows,V[v])
    path=[u]; records=[]
    while path[-1]!=v:
        x=path[-1]; common=old.active(rows,V[x]) & T; missing=T-common
        if not missing: raise AssertionError('target rows do not determine vertex')
        good=missing-B; j=min(good) if good else min(missing)
        F=frozenset(k for k,z in enumerate(V) if common<=old.active(rows,z))
        w,edge=g.improving_edge(model,F,x,rows[j][:-1])
        after=old.active(rows,V[w]) & T
        if not common < after or j not in after: raise AssertionError('no new target row')
        terminal=not good
        if terminal and (len(missing)!=1 or w!=v): raise AssertionError('one-row finish failed')
        records.append(dict(edge=edge,chosen_row=j,before=sorted(common),after=sorted(after),terminal=terminal))
        path.append(w)
        if len(path)>len(T-old.active(rows,V[u]))+1: raise AssertionError('charge overflow')
    return dict(u=u,v=v,path=path,records=records,exceptions=sorted(B),
                initial_missing=sorted(T-old.active(rows,V[u])),displayed_rows=len(rows),
                ambient_dimension=len(V[0]))


def consume(model,rows,cert):
    old.validate_h(model,rows); V=model['vertices']; n=len(V); d=len(V[0]); m=len(rows)
    u=cert['u'];v=cert['v'];p=cert['path'];records=cert['records']
    if not 0<=u<n or not 0<=v<n: raise ValueError('endpoint index')
    B=exceptions(model,rows,v);T=old.active(rows,V[v]);missing=T-old.active(rows,V[u])
    if cert['exceptions']!=sorted(B): raise ValueError('false exception set')
    if cert['initial_missing']!=sorted(missing): raise ValueError('false initial charge')
    if cert['displayed_rows']!=m or cert['ambient_dimension']!=d: raise ValueError('false original size')
    if not p or p[0]!=u or p[-1]!=v or any(not 0<=i<n for i in p): raise ValueError('path endpoints')
    if len(records)!=len(p)-1 or len(p)-1>len(missing) or len(missing)>m-d: raise ValueError('length bound')
    for k,r in enumerate(records):
        x,w=p[k:k+2];j=r['chosen_row'];before=old.active(rows,V[x])&T;after=old.active(rows,V[w])&T
        if x==w or not before<after or j not in T-before or j not in after: raise ValueError('acquisition')
        if r['before']!=sorted(before) or r['after']!=sorted(after): raise ValueError('false tight rows')
        terminal=not ((T-before)-B)
        if r['terminal']!=terminal or (terminal and (len(T-before)!=1 or w!=v)): raise ValueError('false finish')
        edge=r['edge']; F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
        if edge['u']!=x or edge['v']!=w or set(edge['face'])!=F: raise ValueError('incorrect whole face')
        if tuple(Q(a) for a in edge['objective'])!=rows[j][:-1]: raise ValueError('wrong objective')
        g.verify_record(model,edge)
    return True


def roof_points(d):
    return [tuple(Q(a) for a in x)+(Q(side)*(1+sum((Q(a,2**(j+1)) for j,a in enumerate(x)),Q(0))),)
            for x in product(range(2),repeat=d-1) for side in [0,1]]


def small(out, model_filter='all'):
    cases=old.cases()+[(f'roof{d}',roof_points(d),False) for d in [2,3,4]]
    cases+=[('dense_roof3',old.transform(roof_points(3)),False)]
    report=[];fixtures=[]
    for name,points,redundant in cases:
        if model_filter!='all' and model_filter!=name: continue
        model=g.reference(points);rows=old.h_rows(model);V=model['vertices'];d=len(V[0])
        if redundant: rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])]
        qualified=[];rejected=0;new_targets=0
        for v in range(len(V)):
            try:
                B=exceptions(model,rows,v);qualified.append(v);new_targets+=bool(B)
            except ValueError: rejected+=1
        certs=[];edges=shortest=nonshortest=terminals=0
        for u in range(len(V)):
            dist=old.distances(model,u)
            for v in qualified:
                cert=produce(model,rows,u,v);consume(model,rows,cert);certs.append(cert)
                L=len(cert['path'])-1;edges+=L;shortest+=dist[v];nonshortest+=int(L>dist[v])
                terminals+=sum(r['terminal'] for r in cert['records'])
        producer=g.improving_edge
        g.improving_edge=lambda *a,**k: (_ for _ in ()).throw(RuntimeError('producer disabled'))
        try:
            for cert in certs:consume(model,rows,cert)
        finally:g.improving_edge=producer
        entry=dict(name=name,dimension=d,vertices=len(V),rows=len(rows),eligible_targets=len(qualified),
                   newly_eligible_targets=new_targets,rejected_targets=rejected,routes=len(certs),
                   edge_occurrences=edges,shortest_edge_total=shortest,nonshortest_routes=nonshortest,
                   terminal_exception_edges=terminals)
        report.append(entry);fixtures.append(dict(name=name,points=model['points'],rows=rows,certificates=certs))
        print(json.dumps(entry),flush=True)
    out.mkdir(parents=True,exist_ok=True)
    (out/'small-report.json').write_text(json.dumps(dict(kind='exact_tests_not_Lean',models=report),indent=2)+'\n')
    (out/'small-fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')


def roof_rows(d):
    rows=[]
    for i in range(d-1):
        a=[Q(0)]*d;a[i]=-1;rows.append(tuple(a)+(Q(0),))
        a=[Q(0)]*d;a[i]=1;rows.append(tuple(a)+(Q(1),))
    rows.append(tuple([Q(0)]*(d-1)+[Q(-1),Q(0)]))
    rows.append(tuple([-Q(1,2**(i+1)) for i in range(d-1)]+[Q(1),Q(1)]))
    return rows


def roof_vertex(bits,side):
    return tuple(Q(x) for x in bits)+(Q(side)*(1+sum((Q(a,2**(j+1)) for j,a in enumerate(bits)),Q(0))),)


def identity_product(rows,R):
    """Check a supplied exact right inverse, exploiting zeros only."""
    k=len(rows)
    sparse_R=[[(j,b) for j,b in enumerate(r) if b] for r in R]
    for i,row in enumerate(rows):
        values=[Q(0)]*k
        for t,a in enumerate(row):
            if a:
                for j,b in sparse_R[t]: values[j]+=a*b
        if any(value!=int(i==j) for j,value in enumerate(values)):
            raise ValueError('false rank certificate')


def rank_certificate(rows,labels,free,d):
    """Solve a common-row system with one coordinate set to zero."""
    R=[[Q(0)]*len(labels) for _ in range(d)]
    for col,label in enumerate(labels):
        if label<2*(d-1):
            i=label//2;R[i][col]=1/rows[label][i]
        else:
            R[d-1][col]=1/rows[label][d-1]
    face=[label for label in labels if label>=2*(d-1)]
    if face:
        f=face[0]
        for col,label in enumerate(labels):
            if label<2*(d-1):
                R[d-1][col]=-sum((rows[f][i]*R[i][col] for i in range(d-1)),Q(0))/rows[f][d-1]
    identity_product([rows[i][:-1] for i in labels],R)
    return R


def roof_route(d):
    start=[1]*(d-1); target=[0]*(d-1);side=1
    path=[roof_vertex(start,side)];bits=start[:]
    for i in range(d-1):bits[i]=0;path.append(roof_vertex(bits,side))
    path.append(roof_vertex(target,0));rows=roof_rows(d);records=[]
    for u,v in zip(path,path[1:]):
        common=sorted(old.active(rows,u)&old.active(rows,v))
        if len(common)!=d-1:raise AssertionError('wrong common codimension')
        differing=[i for i,(a,b) in enumerate(zip(u,v)) if a!=b]
        free=next((i for i in differing if i<d-1),d-1)
        R=rank_certificate(rows,common,free,d)
        records.append(dict(common=common,right_inverse=R))
    return dict(d=d,rows=rows,path=path,records=records,
                exceptional_vertex_levels=str(2**(d-1)+1),level_count_is_formula=True)


def audit_roof(cert):
    d=cert['d'];rows=[tuple(Q(x) for x in r) for r in cert['rows']];p=[tuple(Q(x) for x in v) for v in cert['path']]
    if rows!=roof_rows(d):raise ValueError('wrong original rows')
    if len(cert['records'])!=len(p)-1:raise ValueError('wrong record length')
    for x in p:
        if any(g.dot(r[:-1],x)>r[-1] for r in rows):raise ValueError('infeasible point')
        bits=x[:-1];height=1+sum((Q(a,2**(j+1)) for j,a in enumerate(bits)),Q(0))
        if any(a not in (0,1) for a in bits) or x[-1] not in (0,height):raise ValueError('not a constructed vertex')
        # Independent active right inverse for d selected rows.
        labels=[2*i+int(x[i]==1) for i in range(d-1)]+[2*(d-1)+int(x[-1]!=0)]
        rank_certificate(rows,labels,None,d)
    T=old.active(rows,p[-1]);initial=T-old.active(rows,p[0]);last=old.active(rows,p[0])&T
    if len(p)-1>len(initial) or len(initial)>len(rows)-d:raise ValueError('wrong count')
    for u,v,record in zip(p,p[1:],cert['records']):
        labels=record['common'];R=[[Q(x) for x in r] for r in record['right_inverse']]
        if len(labels)!=d-1 or len(set(labels))!=d-1 or len(R)!=d or any(len(r)!=d-1 for r in R):raise ValueError('rank shape')
        if not set(labels)<=old.active(rows,u)&old.active(rows,v) or u==v:raise ValueError('common rows')
        identity_product([rows[i][:-1] for i in labels],R)
        # A target acquired at v, and a source row lost at v, bound both
        # ends of the one-dimensional common supporting slice.
        if not (old.active(rows,u)-old.active(rows,v)) or not (old.active(rows,v)-old.active(rows,u)):raise ValueError('not maximal endpoints')
        now=old.active(rows,v)&T
        if not last<now:raise ValueError('target acquisition')
        last=now
    if cert['exceptional_vertex_levels']!=str(2**(d-1)+1) or cert['level_count_is_formula'] is not True:raise ValueError('level formula')
    return True


def large(out):
    fixtures=[];report=[]
    for d in [8,16,32,64]:
        cert=roof_route(d);audit_roof(cert);fixtures.append(cert)
        report.append(dict(dimension=d,original_rows=2*d,route_edges=d,exceptional_levels=str(2**(d-1)+1),
                           counted_by_formula_not_enumeration=True,full_graph_enumerated=False))
    producer=globals()['roof_route'];globals()['roof_route']=lambda *a: (_ for _ in ()).throw(RuntimeError('producer disabled'))
    try:
        for cert in fixtures:audit_roof(cert)
    finally:globals()['roof_route']=producer
    controls=[]
    base=roof_route(3)
    for name,mutate in [
        ('false_inverse',lambda c:c['records'][0]['right_inverse'][0].__setitem__(0,Q(3))),
        ('wrong_original_row',lambda c:c['rows'].__setitem__(0,tuple([Q(1),Q(0),Q(0),Q(0)]))),
        ('false_level_count',lambda c:c.update(exceptional_vertex_levels='2')),
        ('stationary_edge',lambda c:c['path'].__setitem__(1,c['path'][0])),
        ('missing_rank_row',lambda c:c['records'][0]['common'].pop()),
        ('wrong_endpoint',lambda c:c['path'].__setitem__(-1,tuple([Q(0),Q(0),Q(-1)]))),
    ]:
        c=deepcopy(base);mutate(c)
        try:audit_roof(c)
        except (ValueError,IndexError):controls.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    h=g.reference([(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]);rows=old.h_rows(h)
    v=h['vertices'].index((Q(2),Q(2)))
    try:exceptions(h,rows,v)
    except ValueError:controls.append(dict(case='two_bad_target_rows_hexagon',rejected=True))
    else:raise AssertionError('two exceptions accepted')
    out.mkdir(parents=True,exist_ok=True)
    (out/'large-report.json').write_text(json.dumps(dict(kind='exact_route_checks_not_Lean',models=report,negative_controls=controls),indent=2)+'\n')
    (out/'large-fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    print(json.dumps(report,indent=2));print('rejected',len(controls),'controls')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--stage',choices=['small','large'],required=True);ap.add_argument('--model',default='all');args=ap.parse_args()
    if args.stage=='small':small(args.out,args.model)
    else:large(args.out)

if __name__=='__main__':main()
