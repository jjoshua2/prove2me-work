#!/usr/bin/env python3
"""Reproducible exact regression tests, NOT a Lean kernel proof."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import random
from projective_factor_discovery import *


def interval_tower(d: int,cyclic: bool=False)->dict[str,Any]:
    eps=Q(1,4); a=[]; b=[]; w=[]
    for i in range(d):
        low=[Q(0)]*d;low[i]=-1
        high=[Q(0)]*d;high[i]=1
        if i or cyclic: high[(i-1)%d]=-eps
        a.extend([low,high]);b.extend([Q(0),Q(1)])
        w.extend([1-eps if i<d-1 or cyclic else Q(1),Q(1)])
    return {'A':a,'b':b,'interior_point':[Q(1,2)]*d,'positive_balance':w}


def cube(d: int)->dict[str,Any]:
    a=[];b=[]
    for i in range(d):
        row=[Q(0)]*d;row[i]=-1
        a.extend([row,[-x for x in row]]);b.extend([Q(0),Q(1)])
    return {'A':a,'b':b,'interior_point':[Q(1,2)]*d,'positive_balance':[Q(1)]*(2*d)}


def projectivize(data: dict[str,Any],c: Vector)->dict[str,Any]:
    a,b,z,w=decode(data)
    require(1+dot(c,z)>0,'Center chart')
    target=[[x+rhs*t for x,t in zip(row,c)] for row,rhs in zip(a,b)]
    # Find a negative-c source certificate and transfer its strict positive balance.
    lam=dual_weights(a,b,[-x for x in c]);require(lam is not None,'Source chart crosses infinity')
    W=dot(w,b); t=1-dot(lam,b)
    wt=[t*w[i]+W*lam[i] for i in range(len(a))]
    return {'A':target,'b':b,'interior_point':[x/(1+dot(c,z)) for x in z],'positive_balance':wt}


def transformed(data: dict[str,Any],seed: int)->dict[str,Any]:
    rng=random.Random(seed); a,b,z,w=decode(data);d=len(z)
    T=identity(d)
    for i in range(d-1): T[i][i+1]=Q(rng.choice([-2,-1,1,2]),3)
    inv=inverse(T); offset=[Q(rng.randrange(-3,4),5) for _ in range(d)]
    at=matmul(a,inv);zt=[dot(row,z)+off for row,off in zip(T,offset)]
    bt=[rhs+dot(row,offset) for row,rhs in zip(at,b)]
    order=list(range(len(a)));rng.shuffle(order)
    scales=[Q(rng.randrange(1,5),rng.randrange(1,5)) for _ in order]
    return {'A':[[scales[j]*x for x in at[i]] for j,i in enumerate(order)],
            'b':[scales[j]*bt[i] for j,i in enumerate(order)],
            'interior_point':zt,'positive_balance':[w[i]/scales[j] for j,i in enumerate(order)]}


def vertices(data: dict[str,Any])->list[tuple[Vector,frozenset[int]]]:
    a,b,_,_=decode(data);d=len(a[0]);found={}
    for ids in combinations(range(len(a)),d):
        rows=[a[i] for i in ids]
        if rank(rows)<d:continue
        inv=inverse(rows);v=[dot(row,[b[i] for i in ids]) for row in inv]
        if all(dot(row,v)<=rhs for row,rhs in zip(a,b)):
            active=frozenset(i for i,(row,rhs) in enumerate(zip(a,b)) if dot(row,v)==rhs)
            found[tuple(v)]=active
    return [(list(v),active) for v,active in found.items()]


def graph_check(data: dict[str,Any])->dict[str,int]:
    a,_,_,_=decode(data);d=len(a[0]);vs=vertices(data);G=[[] for _ in vs];edges=0
    for i,(_,acti) in enumerate(vs):
        for j in range(i):
            common=acti&vs[j][1]
            if rank([a[t] for t in common])==d-1:
                G[i].append(j);G[j].append(i);edges+=1
    diameter=0
    for start in range(len(vs)):
        dist={start:0};q=deque([start])
        while q:
            i=q.popleft()
            for j in G[i]:
                if j not in dist:dist[j]=dist[i]+1;q.append(j)
        assert len(dist)==len(vs)
        diameter=max(diameter,max(dist.values()))
    return {'vertices':len(vs),'edges':edges,'ordered_distances':len(vs)**2,'diameter':diameter}


def rejected(data: dict[str,Any],tree: dict[str,Any])->None:
    try:verify(data,tree)
    except (ValueError,KeyError,TypeError,ZeroDivisionError):return
    raise AssertionError('Corrupted certificate was accepted')


def all_leaf_excesses(tree: dict[str,Any])->list[int]:
    if tree['kind'] in ('leaf','unresolved'):return [tree['excess']]
    return [e for ch in tree['children'] for e in all_leaf_excesses(ch)]


def run()->dict[str,Any]:
    total={'positive_certificates':0,'graph_vertices':0,'graph_edges':0,'ordered_graph_distances':0,
           'negative_controls':0,'source_target_vertex_maps':0}
    one_shot=[];records=[]
    for d in range(2,13):
        data=interval_tower(d);tree=discover(data,2);out=verify(data,tree)
        assert out['ordinary_edge_bound']==d
        assert out['nodes']<=d-1 and out['leaves']<=d and out['depth']<=d-1
        assert sum(all_leaf_excesses(tree))==d
        total['positive_certificates']+=1;records.append({'family':'tower','dimension':d,**out})
    # Complete chart searches, not selected examples: there is exactly one
    # admissible one-step chart for this family in dimensions 3 through 7.
    for d in range(3,8):
        data=interval_tower(d);a,b,_,_=centered(data)
        candidates=list(homogeneous_candidates(a,b,None));splits=list(all_splits(data,None))
        assert len(candidates)==1 and len(splits)==1
        ex=[len(ch['A'])-len(ch['interior_point']) for ch in splits[0]['child_inputs']]
        assert sorted(ex)==[1,d-1]
        one_shot.append({'dimension':d,'all_chart_candidates':len(candidates),'factor_excesses':ex})
    for family in (cube,interval_tower):
        for d in range(2,7):
            original=family(d)
            c=[Q(j+1,10*d*d) for j in range(d)]
            for data in (original,projectivize(original,c)):
                data=transformed(data,1000+d)
                tree=discover(data,2);out=verify(data,tree)
                assert out['ordinary_edge_bound']==d
                total['positive_certificates']+=1
    # Changing charts recursively is really necessary, not just nesting a
    # single supplied chart repeatedly.
    data=interval_tower(7);tree=discover(data,2,1);out=verify(data,tree)
    assert out['ordinary_edge_bound']==7 and out['leaves']==7 and out['nodes']==6
    total['positive_certificates']+=1
    # Independent active-set graph enumeration: does not use the decomposition.
    for family in (cube,interval_tower):
        for d in range(2,6):
            data=transformed(projectivize(family(d),[Q(1,20*d)]*d),300+d)
            G=graph_check(data)
            assert G['vertices']==2**d and G['edges']==d*2**(d-1) and G['diameter']==d
            total['graph_vertices']+=G['vertices'];total['graph_edges']+=G['edges']
            total['ordered_graph_distances']+=G['ordered_distances']
    # A cyclicly coupled cube has no rank-one bipartition in these dimensions.
    # Graph remains easy, but the detector must NOT equate that with a product.
    cyclic=[]
    for d in (4,5):
        data=interval_tower(d,True);a,b,_,_=centered(data)
        assert list(homogeneous_candidates(a,b,None))==[]
        tree=discover(data,None);out=verify(data,tree)
        assert tree['kind']=='unresolved' and out['ordinary_edge_bound'] is None
        assert tree['all_bipartitions_searched']
        G=graph_check(data);assert G['vertices']==2**d and G['diameter']==d
        cyclic.append({'dimension':d,'admissible_first_splits':0,'actual_graph_diameter':d})
        total['negative_controls']+=1
    # Small search limit is not a nonexistence certificate.
    partial=discover(interval_tower(5),1)
    assert partial['kind']=='unresolved' and not partial['all_bipartitions_searched']
    total['negative_controls']+=1
    # Verify all mapped source vertices against BOTH row systems and margins.
    data=interval_tower(5);tree=discover(data,2);a,b,z,w=centered(data)
    c=tree['chart_normal'];source=[[x-rhs*t for x,t in zip(row,c)] for row,rhs in zip(a,b)]
    sd={'A':source,'b':b,'interior_point':[Q(0)]*5,'positive_balance':tree['source_balance']}
    targets={tuple(v) for v,_ in vertices(data)}
    for v,_ in vertices(sd):
        den=1+dot(c,v);assert den>0
        mapped=[x/den+t for x,t in zip(v,z)]
        assert tuple(mapped) in targets
        total['source_target_vertex_maps']+=1
    # Certificate corruption controls, independent of discovery.
    for change in range(9):
        bad=deepcopy(tree)
        if change==0:bad['chart_normal'][0]+=1
        if change==1:bad['source_weights'][0]=-1
        if change==2:bad['target_weights']=[Q(0)]*10
        if change==3:bad['source_balance'][0]+=1
        if change==4:bad['blocks']['inverse_basis'][0][0]+=1
        if change==5:bad['blocks']['row_blocks'][0].pop()
        if change==6:bad['blocks']['transformed_rows'][0][0]+=1
        if change==7:bad['children'][0]={'kind':'leaf','dimension':4,'rows':8,'excess':4}
        if change==8:bad['center'][0]+=1
        rejected(data,bad);total['negative_controls']+=1
    # No floats or fake boundedness witnesses.
    for kind in ('float','balance','interior'):
        bad=deepcopy(data)
        if kind=='float':bad['A'][0][0]=-1.0
        elif kind=='balance':bad['positive_balance'][0]=-1
        else:bad['interior_point']=[Q(0)]*5
        try:decode(bad)
        except ValueError:pass
        else:raise AssertionError('Bad input accepted')
        total['negative_controls']+=1
    # Serialize and verify again: parser may not trust the discovery object.
    encoded=json.loads(json.dumps(jsonable({'input':data,'certificate':tree})))
    assert verify(encoded['input'],encoded['certificate'])['ordinary_edge_bound']==5
    root=Path(__file__).resolve().parents[1]
    hashes={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
            for directory in ('scripts','Solutions') for p in sorted((root/directory).glob('*')) if p.suffix in ('.py','.lean')}
    return {'status':'PASS','scope':'Exact rational computational regression only; no new Lean or platform verdict.',
            **total,'one_shot_exhaustive':one_shot,'cyclic_negative_controls':cyclic,
            'tower_certificates':records,'source_sha256':hashes}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
