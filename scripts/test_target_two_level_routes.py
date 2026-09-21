#!/usr/bin/env python3
"""Exact original-row target-locking regression; not Lean verification.

Reuses #322's unchanged rational hull/edge implementation. Original H data
include both signs of affine equations in lower-dimensional cases. The route
producer never reads the independently enumerated edge graph. The consumer
checks the complete original row list, target-only level property, ordinary
edges, per-step target locking/acquisition and the m-d bound.
"""
from __future__ import annotations
import argparse
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json
import sympy as sp
import test_geometric_coordinate_routes as g


def h_rows(model):
    """Complete reference facets PLUS affine-hull equalities, both signs."""
    V=model['vertices']; d=len(V[0]); origin=V[0]
    rows=[tuple(Q(x) for x in row) for row in model['rows']]
    diffs=[g.sub(x,origin) for x in V]
    ns=sp.Matrix(diffs).nullspace() if d else []
    for n in ns:
        a=tuple(Q(x) for x in n); row=(*a,g.dot(a,origin))
        rows.extend([row,tuple(-x for x in row)])
    return rows


def canonical(row):
    return g.primitive(row)


def validate_h(model,rows):
    """Completeness relative to an exhaustively constructed small-hull reference.

Every required facet/equality must occur up to POSITIVE scaling. Additional
rows may be redundant, but must hold on every reference vertex. This is not a
general independently formalized H-to-V procedure.
"""
    d=len(model['vertices'][0])
    if any(len(row)!=d+1 for row in rows): raise ValueError('wrong row dimension')
    actual={canonical(row) for row in rows}
    if not {canonical(row) for row in h_rows(model)} <= actual:
        raise ValueError('missing original facet or affine equation')
    if any(g.dot(row[:-1],v)>row[-1] for row in rows for v in model['vertices']):
        raise ValueError('row cuts off a true hull vertex')
    for v in model['vertices']:
        tight=[row[:-1] for row in rows if g.dot(row[:-1],v)==row[-1]]
        if g.rank(tight)!=d: raise ValueError('actual active map not injective')


def active(rows,x):
    return {i for i,row in enumerate(rows) if g.dot(row[:-1],x)==row[-1]}


def target_levels(model,rows,v):
    levels={}
    for i in active(rows,model['vertices'][v]):
        row=rows[i]
        other={g.dot(row[:-1],x) for x in model['vertices']} - {row[-1]}
        if len(other)>1: raise ValueError('target row has more than two vertex levels')
        levels[i]=next(iter(other)) if other else row[-1]
    return levels


def produce(model,rows,u,v):
    validate_h(model,rows); target_levels(model,rows,v)
    V=model['vertices']; T=active(rows,V[v]); path=[u]; records=[]
    while path[-1]!=v:
        x=path[-1]; common=active(rows,V[x]) & T
        absent=T-common
        if not absent: raise AssertionError('target-active rows did not determine target')
        F=frozenset(k for k,z in enumerate(V) if common <= active(rows,z))
        j=min(absent)
        w,record=g.improving_edge(model,F,x,rows[j][:-1])
        new=active(rows,V[w]) & T
        if not common < new or j not in new:
            raise AssertionError('improving edge did not acquire target row')
        records.append(dict(edge=record,chosen_row=j,before=sorted(common),after=sorted(new)))
        path.append(w)
        if len(path)-1>len(T-active(rows,V[u])): raise AssertionError('charge exhausted')
    return dict(u=u,v=v,path=path,records=records,
                initial_missing=sorted(T-active(rows,V[u])),
                displayed_rows=len(rows),ambient_dimension=len(V[0]))


def consume(model,rows,cert):
    validate_h(model,rows); V=model['vertices']; n=len(V); d=len(V[0]); m=len(rows)
    u=cert['u']; v=cert['v']; p=cert['path']; records=cert['records']
    if not 0<=u<n or not 0<=v<n: raise ValueError('endpoint index')
    target_levels(model,rows,v); T=active(rows,V[v])
    absent=T-active(rows,V[u])
    if cert['displayed_rows']!=m or cert['ambient_dimension']!=d:
        raise ValueError('incorrect original size parameters')
    if cert['initial_missing']!=sorted(absent): raise ValueError('incorrect initial charge')
    if not p or p[0]!=u or p[-1]!=v or any(not 0<=x<n for x in p):
        raise ValueError('invalid path endpoints')
    if len(records)!=len(p)-1: raise ValueError('incorrect edge count')
    if len(p)-1>len(absent) or len(absent)>m-d: raise ValueError('original count exceeded')
    for k,rec in enumerate(records):
        x,w=p[k:k+2]; j=rec['chosen_row']; old=active(rows,V[x]) & T; new=active(rows,V[w]) & T
        if x==w or not old < new: raise ValueError('target lock/acquisition failed')
        if j not in T-old or j not in new: raise ValueError('claimed new row not acquired')
        if rec['before']!=sorted(old) or rec['after']!=sorted(new): raise ValueError('forged tight set')
        edge=rec['edge']
        if edge['u']!=x or edge['v']!=w: raise ValueError('wrong edge endpoints')
        if tuple(Q(t) for t in edge['objective'])!=rows[j][:-1]: raise ValueError('wrong original objective')
        F={i for i,z in enumerate(V) if old <= active(rows,z)}
        if set(edge['face'])!=F: raise ValueError('incomplete locked face')
        g.verify_record(model,edge)
    return True


def distances(model,u):
    adj=[set() for _ in model['vertices']]
    for a,b in model['edges']: adj[a].add(b);adj[b].add(a)
    dist={u:0};q=deque([u])
    while q:
        x=q.popleft()
        for z in adj[x]:
            if z not in dist:dist[z]=dist[x]+1;q.append(z)
    return dist


def transform(points):
    d=len(points[0]); M=[[Q(2 if i==j else 1) for j in range(d)] for i in range(d)]
    t=[Q(i+1,3) for i in range(d)]
    assert sp.Matrix(M).det()!=0
    return [tuple(g.dot(row,x)+a for row,a in zip(M,t)) for x in points]


def cases():
    base=g.models()
    selected=[(n,p,False) for n,p in base if n!='tiny_gap']
    cube_cut=[x for x in product(range(2),repeat=3) if sum(x)<=2]
    selected.extend([('target_only_cut_cube',cube_cut,False),
        ('dense_target_only_cut_cube',transform(cube_cut),False),
        ('rescaled_redundant_cube',list(product(range(2),repeat=3)),True),
        ('simplex5',[(0,)*5]+[tuple(int(i==j) for j in range(5)) for i in range(5)],False),
        ('dense_cube',transform(list(product(range(2),repeat=3))),False)])
    return selected


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    report=[];fixtures=[]
    for name,points,redundant in cases():
        model=g.reference(points);rows=h_rows(model);V=model['vertices'];d=len(V[0])
        if redundant:
            rows=[tuple(Q(i+1,7)*x for x in row) for i,row in enumerate(rows)]
            rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])]
        validate_h(model,rows)
        allowed=[];rejected=0
        for v in range(len(V)):
            try:target_levels(model,rows,v);allowed.append(v)
            except ValueError:rejected+=1
        count=0;edge_count=0;shortest=0;nonshortest=0;certs=[]
        for u in range(len(V)):
            dist=distances(model,u)
            for v in allowed:
                cert=produce(model,rows,u,v);consume(model,rows,cert)
                L=len(cert['path'])-1;count+=1;edge_count+=L;shortest+=dist[v]
                nonshortest+=int(L>dist[v]);certs.append(cert)
        producer=g.improving_edge
        g.improving_edge=lambda *a,**k: (_ for _ in ()).throw(RuntimeError('producer disabled'))
        for cert in certs:consume(model,rows,cert)
        g.improving_edge=producer
        non_target_many=False
        for v in allowed:
            T=active(rows,V[v])
            non_target_many|=any(len({g.dot(r[:-1],x) for x in V})>2 for i,r in enumerate(rows) if i not in T)
        entry=dict(name=name,ambient_dimension=d,intrinsic_dimension=model['dimension'],
                   generators=len(model['points']),vertices=len(V),original_rows=len(rows),
                   facets=len(model['rows']),eligible_targets=len(allowed),rejected_targets=rejected,
                   routes=count,edge_occurrences=edge_count,shortest_edge_total=shortest,
                   nonshortest_routes=nonshortest,target_only_not_global=non_target_many)
        report.append(entry);fixtures.append(dict(name=name,points=model['points'],rows=rows,certificates=certs))
        print(json.dumps(entry),flush=True)
    # Explicit structural counterexample: a hexagon needs 3 edges, and neither
    # source neighbor acquires a target row. Its target-level hypothesis fails.
    hexagon=g.reference([(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)])
    rows=h_rows(hexagon);V=hexagon['vertices'];u=V.index((Q(0),Q(0)));v=V.index((Q(2),Q(2)))
    T=active(rows,V[v]);neighbors=[j if i==u else i for i,j in hexagon['edges'] if u in (i,j)]
    assert distances(hexagon,u)[v]==3
    assert all(not (active(rows,V[z]) & T) for z in neighbors)
    try:target_levels(hexagon,rows,v)
    except ValueError:pass
    else:raise AssertionError('hexagon must fail the target-only condition')
    structural=dict(distance=3,no_source_neighbor_acquires_target_row=True,
                    target_row_vertex_level_counts=[len({g.dot(rows[i][:-1],x) for x in V}) for i in sorted(T)])
    controls=[]
    model=g.reference(list(product(range(2),repeat=2)));rows=h_rows(model)
    good=produce(model,rows,0,3)
    for name,edit in [
      ('wrong_size',lambda c:c.update(displayed_rows=99)),
      ('wrong_charge',lambda c:c.update(initial_missing=[])),
      ('wrong_target',lambda c:c.update(v=0)),
      ('missing_edge',lambda c:c['records'].pop()),
      ('false_tight_set',lambda c:c['records'][0].update(after=[])),
      ('zero_support',lambda c:c['records'][0]['edge'].update(support=[0,0])),
      ('wrong_original_row',lambda c:c['records'][0].update(chosen_row=-1)),
      ('chord',lambda c:c.update(path=[0,3],records=[c['records'][0]])),
    ]:
        c=deepcopy(good);edit(c)
        try:consume(model,rows,c)
        except (ValueError,AssertionError,KeyError,IndexError):controls.append(dict(name=name,rejected=True))
        else:raise AssertionError('forgery accepted '+name)
    line=g.reference([(0,0),(1,2),(2,4)])
    for name,fn in [
        ('missing_affine_equations',lambda:validate_h(line,[tuple(Q(x) for x in r) for r in line['rows']])),
        ('false_two_levels',lambda:produce(hexagon,h_rows(hexagon),u,v)),
        ('missing_original_facet',lambda:validate_h(model,rows[:-1])),
        ('infeasible_added_row',lambda:validate_h(model,rows+[(Q(1),Q(0),Q(-1))])),
    ]:
        try:fn()
        except (ValueError,AssertionError):controls.append(dict(name=name,rejected=True))
        else:raise AssertionError('bad input accepted '+name)
    result=dict(kind='exact_rational_supporting_tests_not_Lean_or_parser_verification',
                models=report,structural_counterexample=structural,negative_controls=controls)
    (args.out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    print('TOTAL',json.dumps({k:sum(x[k] for x in report) for k in ['routes','edge_occurrences','nonshortest_routes','eligible_targets','rejected_targets']}),flush=True)
    print('NEGATIVE',len(controls),flush=True)

if __name__=='__main__':main()
