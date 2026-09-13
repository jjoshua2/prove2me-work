#!/usr/bin/env python3
"""Intrinsic facet counts, nonzonotopal perturbations, and direction obstruction."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random,time
from network_potential_router import Network,UnionFind,construct,rat,serial,require
from network_carrier_normalization import normalize_and_route,verify_normalized,construct_H,verify_H
from test_network_potential_router import vertices,graph,spread,random_network,solve
ROOT=Path(__file__).resolve().parents[1]


def rank(A):
    A=[list(r)for r in A]
    if not A:return 0
    k=0
    for j in range(len(A[0])):
        i=next((i for i in range(k,len(A))if A[i][j]),None)
        if i is None:continue
        A[k],A[i]=A[i],A[k];q=A[k][j];A[k]=[x/q for x in A[k]]
        for i in range(k+1,len(A)):
            q=A[i][j]
            if q:A[i]=[x-q*y for x,y in zip(A[i],A[k])]
        k+=1
    return k


def intrinsic_facets(data,pts,x,y):
    P=Network({**data,'source':x,'target':y});common=P.active(x)&P.active(y)
    face=[p for p in pts if common<=P.active(p)]
    h=rank([[a-b for a,b in zip(z,face[0])]for z in face[1:]])
    faces=set()
    for i,(a,b,c)in enumerate(P.arcs):
        vs=tuple(k for k,z in enumerate(face)if z[b]-z[a]==c)
        if vs and rank([[u-v for u,v in zip(face[k],face[vs[0]])]for k in vs[1:]])==h-1:faces.add(vs)
    return h,len(faces)


def cube_pyramid(d):
    # Node1 is z; the other d-1 variables are leaves y_j. This is the pyramid
    # conv((z=1,y=1), (z=0,y in [0,1]^(d-1))).
    arcs=[[1,0,0]]
    for j in range(2,d+1):arcs.extend([[j,1,0],[0,j,1]])
    return {'nodes':d+1,'arcs':arcs,'source':[0]+[0]*d,'target':[0]+[1]*d}


def main():
    begin=time.monotonic();rows=[];checked=0;removed=0;normalized_edges=0
    for tag,data in [('spread3',spread(3)),('perturbed3',spread(3,77)),('random3',random_network(3,10)),
                     ('random4',random_network(4,11))]:
        pts=vertices(data['nodes'],data['arcs']);pairs=list(combinations(range(len(pts)),2))
        rng=random.Random(11);rng.shuffle(pairs)
        for i,j in pairs[:50]:
            prob={**data,'source':pts[i],'target':pts[j]};out=normalize_and_route(prob);got=out['verified']
            h,M=intrinsic_facets(data,pts,pts[i],pts[j])
            require((h,M)==(got['intrinsic_dimension'],got['intrinsic_facets']),'independent face-facet count disagrees')
            checked+=1;removed+=got['removed_redundant_rows'];normalized_edges+=got['ordinary_edges']
        rows.append({'model':tag,'vertices':len(pts),'checked_pairs':min(len(pairs),50)})
    large=[]
    for tag,data in [('dense24',random_network(24,9,True)),('perturbed16',spread(16,12))]:
        out=normalize_and_route(data);r=out['verified'];large.append({'name':tag,**{k:v for k,v in r.items()if k not in ('route','scope')}})
        (ROOT/'fixtures'/f'{tag}_normalized_input.json').write_text(json.dumps(serial(data),separators=(',',':'))+'\n')
        (ROOT/'fixtures'/f'{tag}_normalized_certificate.json').write_text(json.dumps(out['certificate'],separators=(',',':'))+'\n')
    # Positive diagonal chart discovery: unknown gains, arbitrary positive row
    # rescaling and permutations. The detector reconstructs scale up to one
    # factor per variable-connectivity component, which does not change routes.
    charts=[];saved=None
    for d,seed in [(4,91),(8,92),(16,93)]:
        net=spread(d,seed);rng=random.Random(seed)
        scales=[Q(rng.randrange(1,20),rng.randrange(1,20))for _ in range(d)]
        arcs=net['arcs'][:];rng.shuffle(arcs);A=[];b=[]
        for u,v,c in arcs:
            factor=Q(rng.randrange(1,11),rng.randrange(1,11))
            A.append([factor*(int(i+1==v)-int(i+1==u))/scales[i]for i in range(d)]);b.append(factor*c)
        data={'A':A,'b':b,'source':[0]*d,'target':scales}
        out=construct_H(data);charts.append({'dimension':d,'rows':len(A),'route_edges':out['verified']['ordinary_edges']})
        if d==8:saved=data,out['certificate']
    # Exponentially many REAL edge directions in O(d) H-rows.
    pyramids=[];apex_edges=0;full_counts=[]
    for d in (3,4,8,24):
        net=cube_pyramid(d);P=Network(net);apex=P.target
        signatures=list(product((0,1),repeat=d-1))if d<=8 else []
        if d>8:
            for k in range(40):
                rng=random.Random(k);signatures.append(tuple(rng.randrange(2)for _ in range(d-1)))
        directions=set()
        for bits in signatures:
            base=(Q(0),Q(0))+tuple(map(Q,bits));P.check_point(base);P.tree(P.active(base))
            require(len(set(P.labels(P.active(base)&P.active(apex))))==2,'cube-pyramid apex segment not an edge')
            directions.add(tuple(a-b for a,b in zip(apex,base)));apex_edges+=1
        if d<=8:require(len(directions)==2**(d-1),'distinct apex direction count')
        if d<=4:
            pts=vertices(P.n,P.arcs);require(len(pts)==2**(d-1)+1,'complete cube-pyramid vertex count')
            G,_=graph(P.n,P.arcs,pts);i=pts.index(apex);require(len(G[i])==2**(d-1),'complete apex degree')
            full_counts.append(len(pts))
        r=construct(net)['verified'];require(r['ordinary_edges']==1,'apex edge routing failed')
        pyramids.append({'dimension':d,'facets':2*d-1,'apex_edge_directions_formula':2**(d-1),
                         'sampled_apex_edges':len(signatures),'certified_apex_route':1})
    # New tests target quotient/implication identity and balanced-cycle failures.
    rejected=[]
    def reject(name,f):
        try:f()
        except(ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise AssertionError('negative accepted: '+name)
    prob=random_network(8,5);out=normalize_and_route(prob);cert=out['certificate']
    require(cert['removals'],'missing redundancy controls')
    for name,mut in [('changed_group',lambda c:c['quotient']['groups'].__setitem__(1,999)),
                     ('changed_offset',lambda c:c['quotient']['offsets'].__setitem__(1,'99')),
                     ('empty_implication',lambda c:c['removals'][0].update(path=[])),
                     ('self_implication',lambda c:c['removals'][0].update(path=[c['removals'][0]['row']])),
                     ('omitted_retained_row',lambda c:c['retained_rows'].pop()),
                     ('forged_problem',lambda c:c.update(input_sha256='bad'))]:
        bad=deepcopy(cert);mut(bad);reject(name,lambda bad=bad:verify_normalized(prob,bad))
    data,cert=saved
    bad=deepcopy(cert);bad['diagonal_scale'][0]='99';reject('changed_diagonal_chart',lambda:verify_H(data,bad))
    badH=deepcopy(data)
    k=next(i for i,r in enumerate(badH['A'])if sum(x!=0 for x in r)==2)
    j=next(j for j,x in enumerate(badH['A'][k])if x);badH['A'][k][j]*=2
    reject('inconsistent_gain_cycle',lambda:construct_H(badH))
    badH=deepcopy(data);badH['A'][0]=[Q(1)]*8;reject('dense_nonnetwork_row',lambda:construct_H(badH))
    arithmetic=0
    for e in range(15):
        for H in range(9):
            for ds in product(range(H+1),repeat=3):
                for delta in [ds,tuple(2*x for x in ds)]:
                    if sum(delta)<=3*e:
                        M=[2*x for x in delta]
                        require(sum(h*m for h,m in zip(ds,M))<=6*H*e,'aggregate bound')
                        arithmetic+=1
    summary={'status':'PASS','scope':'Exact H-face quotient, redundancy and routing tests, not Lean/platform verdict.',
             'independent_intrinsic_pairs':checked,'verified_normalized_route_edges':normalized_edges,
             'removed_rows_checked':removed,'small_models':rows,'large_models':large,'diagonal_chart_examples':charts,
             'exponential_direction_examples':pyramids,'apex_edges_checked':apex_edges,
             'complete_small_pyramid_vertices':full_counts,'negative_controls_rejected':len(rejected),'negative_controls':rejected,
             'aggregate_arithmetic_cases':arithmetic,'elapsed_seconds':round(time.monotonic()-begin,3),
             'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                for folder,ext in [('scripts','*.py'),('Solutions','*.lean')]for p in sorted((ROOT/folder).glob(ext))}}
    (ROOT/'research/NETWORK_NORMALIZATION_CHECK_2026-09-12.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
