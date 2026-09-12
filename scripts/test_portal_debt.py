#!/usr/bin/env python3
"""Exact regression suite for portal locality and nested neutral-facet charges."""
from __future__ import annotations
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import random
from portal_debt_router import Model,dot,rank,solve,distances,verify_tree,jsonable,require


def all_vertices(A,b):
    pts=set();d=len(A[0])
    for ids in combinations(range(len(A)),d):
        x=solve([A[i] for i in ids],[b[i] for i in ids])
        if x is not None and all(dot(a,x)<=z for a,z in zip(A,b)):pts.add(x)
    return sorted(pts)


def packing(d,q,seed):
    rng=random.Random(seed)
    upper=[[Q(rng.randrange(1,91),rng.randrange(2,20)) for _ in range(d)] for _ in range(q)]
    A=[[-Q(i==j) for j in range(d)] for i in range(d)]+upper
    b=[Q(0)]*d+[Q(1)]*q
    pts=all_vertices(A,b)
    retained=[]
    for j in range(q):
        row=upper[j];vs=[p for p in pts if dot(row,p)==1]
        if vs and rank([[x-y for x,y in zip(p,vs[0])] for p in vs[1:]])==d-1:retained.append(row)
    A=A[:d]+retained;b=b[:d]+[Q(1)]*len(retained)
    bal=[sum((row[j] for row in retained),Q(0)) for j in range(d)]+[Q(1)]*len(retained)
    t=1/(2*max(sum(row) for row in retained))
    return {'A':A,'b':b,'interior':[t]*d,'positive_balance':bal}


def truncate(d,steps,seed):
    rng=random.Random(seed)
    A=[[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(1)]*d]
    b=[Q(0)]*d+[Q(1)];bal=[Q(1)]*(d+1)
    vs=all_vertices(A,b)
    for _ in range(steps):
        x=rng.choice(vs)
        act=[i for i,(a,z) in enumerate(zip(A,b)) if dot(a,x)==z]
        require(len(act)==d,'chosen vertex nonsimple')
        normal=[sum((A[i][j] for i in act),Q(0)) for j in range(d)]
        top=dot(normal,x);runner=max(dot(normal,p) for p in vs if p!=x)
        bound=(top+runner)/2
        new=[p for p in vs if p!=x]
        for y in vs:
            ay={i for i,(a,z) in enumerate(zip(A,b)) if dot(a,y)==z}
            if y!=x and len(set(act)&ay)==d-1:
                t=(top-bound)/(top-dot(normal,y))
                new.append(tuple((1-t)*xx+t*yy for xx,yy in zip(x,y)))
        eps=min(bal[i] for i in act)/2
        for i in act:bal[i]-=eps
        bal.append(eps);A.append(normal);b.append(bound);vs=sorted(new)
    o=[sum((p[j] for p in vs),Q(0))/len(vs) for j in range(d)]
    return {'A':A,'b':b,'interior':o,'positive_balance':bal}


def cube(d):
    return {'A':[[-int(i==j) for j in range(d)] for i in range(d)]+[[int(i==j) for j in range(d)] for i in range(d)],
            'b':[0]*d+[1]*d,'interior':['1/2']*d,'positive_balance':[1]*(2*d)}


def run_model(data,tag,allpairs=True):
    m=Model(data);N=len(m.vertices);rows=[]
    pairs=list(combinations(range(N),2)) if allpairs else [(0,N-1),(N//3,2*N//3)]
    exacts={u:distances(m.graph,u) for u,_ in pairs}
    for u,v in pairs:
        rs={mode:m.route(u,v,mode) for mode in ['lex','local','recursive','relaxed']}
        row={'model':tag,'u':u,'v':v,'dimension':m.dim(u,v),'ambient_dimension':m.d,'facets':m.n,
             'graph_distance':exacts[u][v]}
        for mode,res in rs.items():
            row[mode]={'length':res['length'],'debt':res['debt'],'local_debt':res['local_debt'],
                       'max_row_charge':max(res['row_charges'].values(),default=0),
                       'nodes':res['internal_nodes'],'depth':res['max_depth']}
        require(rs['recursive']['length']<=min(rs['lex']['length'],rs['local']['length']),'optimizer missed admissible route')
        require(exacts[u][v]<=rs['relaxed']['length']<=rs['recursive']['length'],'relaxed/oracle inequality failed')
        rows.append(row)
    return m,rows


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--explore',action='store_true');args=ap.parse_args()
    root=Path(__file__).resolve().parents[1];allrows=[];models=[];found={}
    specs=[('cube'+str(d),cube(d),d<=4) for d in range(2,7)]
    specs += [('trunc3_'+str(seed),truncate(3,10,seed),True) for seed in range(8 if args.explore else 3)]
    specs += [('trunc4_'+str(seed),truncate(4,5,seed),True) for seed in range(5 if args.explore else 2)]
    specs += [('packing3_'+str(seed),packing(3,9,seed),True) for seed in range(25 if args.explore else 5)]
    specs += [('packing4_'+str(seed),packing(4,8,seed),True) for seed in range(10 if args.explore else 4)]
    for tag,data,allpairs in specs:
        try:m,rows=run_model(data,tag,allpairs)
        except ValueError as e:
            if 'nonsimple' in str(e):continue
            raise
        allrows+=rows;models.append({'model':tag,'dimension':m.d,'facets':m.n,'vertices':len(m.vertices),'pairs':len(rows),'stats':dict(m.stats)})
        tests={
            'repeated_original_row':lambda r:r['lex']['max_row_charge']>=2,
            'descendant_optimization':lambda r:r['recursive']['length']<r['local']['length'],
            'geodesic_barrier':lambda r:r['recursive']['length']>r['graph_distance'],
            'root_zero_debt_nonzero_total':lambda r:r['recursive']['local_debt']==0 and r['recursive']['debt']>0,
            'relaxed_barrier':lambda r:r['relaxed']['length']>r['graph_distance'],
        }
        for name,fn in tests.items():
            candidates=[r for r in rows if fn(r)]
            if candidates and name not in found:
                rec=max(candidates,key=lambda r:r['lex']['length']-r['graph_distance'])
                found[name]=rec
                packet={'input':data,'comparison':rec,'vertices':m.vertices,
                        'certificates':{mode:m.route(rec['u'],rec['v'],mode) for mode in ['lex','local','recursive','relaxed']}}
                (root/'fixtures'/f'{name}.json').write_text(json.dumps(jsonable(packet),indent=2,sort_keys=True)+'\n')
        print(tag,len(m.vertices),len(rows),{k:v['model'] for k,v in found.items()},flush=True)
    summary={'models':models,'comparisons':len(allrows),'route_checks':4*len(allrows),'witnesses':found,
             'maximum_row_charge':max(r['lex']['max_row_charge'] for r in allrows),
             'recursive_improves_lex':sum(r['recursive']['length']<r['lex']['length'] for r in allrows),
             'recursive_improves_local':sum(r['recursive']['length']<r['local']['length'] for r in allrows),
             'recursive_longer_than_graph':sum(r['recursive']['length']>r['graph_distance'] for r in allrows),
             'relaxation_improves_recursive':sum(r['relaxed']['length']<r['recursive']['length'] for r in allrows),
             'relaxed_longer_than_graph':sum(r['relaxed']['length']>r['graph_distance'] for r in allrows)}
    (root/'research/PORTAL_DEBT_EXPLORATION.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary,indent=2))
