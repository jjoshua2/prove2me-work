#!/usr/bin/env python3
"""Sparse product-of-hexagons checks. No full product graph is enumerated.

The actual global H rows are the block embeddings of all six local inequalities.
Each delivered edge is checked through the whole local supporting slices. Their
product is one nondegenerate segment; a block rank sum verifies codimension one.
The all-dimensional product interpretation is a written application, not a Lean
instance theorem or a proof of this Python consumer.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old
import test_target_row_level_budget as t

POINTS=[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]


def original_rows(local,r):
    result=[]
    for j in range(r):
        for a,b,c in local:
            row=[Q(0)]*(2*r);row[2*j:2*j+2]=[a,b]
            result.append(tuple(row+[c]))
    return result


def construct(r):
    model=g.reference(POINTS); local=old.h_rows(model);V=model['vertices']
    u=V.index((Q(0),Q(0)));v=V.index((Q(2),Q(2)))
    cert=t.produce(model,local,u,v);t.consume(model,local,cert)
    p=[tuple(V[u]*r)];which=[]
    for j in range(r):
        for idx in cert['path'][1:]:
            x=list(p[-1]);x[2*j:2*j+2]=V[idx];p.append(tuple(x));which.append(j)
    return dict(r=r,base_points=V,base_rows=local,local_certificate=cert,
                rows=original_rows(local,r),path=p,changed_block=which,
                dimensions=2*r,inequalities=6*r,multilevel_target_rows=2*r,
                K=2,weighted_bound=4*r,uniform_bound=8*r)


def consume(c):
    r=c['r']; model=g.reference(POINTS);local=old.h_rows(model);V=model['vertices']
    rows=[tuple(map(Q,row)) for row in c['rows']]
    require=t.require
    require(r>0 and rows==original_rows(local,r),'not the full original product H system')
    p=[tuple(map(Q,x)) for x in c['path']];d=2*r
    require(all(len(x)==d for x in p),'wrong ambient dimension')
    vals=t.row_values(model,local);T=old.active(local,(Q(2),Q(2)))
    require(len(T)==2 and all(len(vals[i])==3 for i in T),'target rows not genuinely three-level')
    require(c['dimensions']==d and c['inequalities']==6*r and c['K']==2
            and c['multilevel_target_rows']==d,'wrong structural parameters')
    require(c['weighted_bound']==4*r and c['uniform_bound']==8*r,'incorrect row budgets')
    require(p[0]==(Q(0),Q(0))*r and p[-1]==(Q(2),Q(2))*r,'wrong endpoints')
    require(len(p)-1<=c['weighted_bound']<=c['uniform_bound'],'exceeded original bound')
    # The independent local reference checks every possible block pair used.
    pair_data={}
    for a in V:
        for b in V:
            common=old.active(local,a)&old.active(local,b)
            hits={x for x in V if all(g.dot(local[i][:-1],x)==local[i][-1] for i in common)}
            rank=g.rank([local[i][:-1] for i in common])
            pair_data[a,b]=(hits,rank)
    for x in p:
        for j in range(r):
            block=x[2*j:2*j+2]
            require(block in V and all(g.dot(row[:-1],block)<=row[-1] for row in local),'nonvertex block')
    local_target={i for i in T}
    for edge,(a,b) in enumerate(zip(p,p[1:])):
        changes=[];rank=0
        for j in range(r):
            x=a[2*j:2*j+2];y=b[2*j:2*j+2];hits,rr=pair_data[x,y];rank+=rr
            require((old.active(local,x)&local_target)<=(old.active(local,y)&local_target),'target lock lost')
            if x==y:require(hits=={x} and rr==2,'stationary block not singleton support')
            else:
                changes.append(j)
                require(hits=={x,y} and rr==1,'changing block is not a whole original edge')
        require(changes==[c['changed_block'][edge]] and rank==d-1,'not one original product edge')
    return dict(dimension=d,original_rows=6*r,multilevel_target_rows=d,K=2,
                actual_edges=len(p)-1,weighted_bound=4*r,uniform_bound=8*r,
                full_graph_enumerated=False)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True);records=[];report=[]
    for r in (4,8,16,32):
        c=construct(r);s=consume(c);records.append(c);report.append(s);print(json.dumps(s),flush=True)
    frozen=json.loads(json.dumps(g.encoded(records)))
    for c in frozen:consume(c)
    (args.out/'fixtures.json').write_text(json.dumps(g.encoded(records),indent=2)+'\n')
    (args.out/'report.json').write_text(json.dumps({'kind':'exact_product_checks_not_Lean_instances','cases':report},indent=2)+'\n')

if __name__=='__main__':main()
