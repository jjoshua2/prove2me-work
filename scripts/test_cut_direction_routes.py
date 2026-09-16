#!/usr/bin/env python3
"""Exact tests of cut-direction closure and original-edge shadow routes.

Small complete H graphs use independent SymPy elimination. No graph, vertex
list or supplied neighbor is passed to the constructor. Large tests use only
explicit H data, endpoints and the recognized base; they are not BFS claims.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations,permutations
from collections import deque
from copy import deepcopy
from pathlib import Path
import hashlib,json,random,time,argparse
import cut_direction_routes as alg
import exact_farkas_lp as lp

ROOT=Path(__file__).resolve().parents[1]
NAMES=['cut_direction_routes.py','test_cut_direction_routes.py','exact_farkas_lp.py',
       'endpoint_transfer_routes.py','simple_tangent_policy_audit.py']


def dump(path,out):
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(lp.serial(out),sort_keys=True,indent=2)+'\n')


def hashes():return {n:hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in NAMES}


def bind(data):
    A,b,_,_=alg.model(data);data['A']=lp.serial(A);data['b']=lp.serial(b);return data


def box(d,C=(),h=()):
    return bind({'base':{'kind':'box','lower':[0]*d,'upper':[1]*d},'cuts_A':list(C),'cuts_b':list(h)})


def building(n,C=(),h=(),interval=True):
    S=[list(range(i,j)) for i in range(n) for j in range(i+1,n+1)] if interval else [list(I) for j in range(1,n+1) for I in combinations(range(n),j)]
    return bind({'base':{'kind':'building_set','n':n,'subsets':S},'cuts_A':list(C),'cuts_b':list(h)})


def reference(A,b):
    import sympy as sp
    d=len(A[0]);V=set();bases=0
    for I in combinations(range(len(A)),d):
        bases+=1;M=sp.Matrix([A[i] for i in I])
        if M.det()==0:continue
        p=tuple(Q(x) for x in M.inv()*sp.Matrix([b[i] for i in I]))
        if all(lp.dot(a,p)<=t for a,t in zip(A,b)):V.add(p)
    V=sorted(V);alg.require(V,'empty reference model')
    acts=[{i for i,(a,t) in enumerate(zip(A,b)) if lp.dot(a,x)==t} for x in V]
    rank=lambda M:sp.Matrix(M).rank() if M else 0
    dimension=rank([[a-b for a,b in zip(x,V[0])] for x in V[1:]])
    G=[set() for _ in V]
    for i,j in combinations(range(len(V)),2):
        if rank([A[k] for k in acts[i]&acts[j]])==d-1:G[i].add(j);G[j].add(i)
    facets=set()
    for k in range(len(A)):
        I=tuple(i for i in range(len(V)) if k in acts[i])
        if not I:continue
        fdim=rank([[a-b for a,b in zip(V[i],V[I[0]])] for i in I[1:]])
        if dimension>0 and fdim==dimension-1:facets.add(I)
    return V,G,acts,{'square_systems':bases,'vertices':len(V),'graph_edges':sum(map(len,G))//2,
        'intrinsic_dimension':dimension,'reference_genuine_facets':len(facets),
        'nonsimple_vertices':sum(len(G[i])>dimension for i in range(len(V)))}


def dist(G,i):
    D={i:0};todo=deque([i])
    while todo:
        u=todo.popleft()
        for v in G[u]:
            if v not in D:D[v]=D[u]+1;todo.append(v)
    alg.require(len(D)==len(G),'reference graph disconnected');return D


def models():
    out={'box3_one_cut':box(3,[[1,2,3]],[Q(13,4)]),
         'box3_two_cuts_nonsimple':box(3,[[1,1,0],[0,1,1]],[1,1]),
         'box4_two_cuts':box(4,[[1,2,3,5],[4,1,3,2]],[Q(15,2),Q(27,4)]),
         'box3_slice':box(3,[[1,2,3],[-1,-2,-3]],[Q(13,4),-Q(13,4)]),
         'box3_point':box(3,[[1,1,1]],[0]),
         'box1_interval':box(1,[[1],[-1]],[Q(3,4),-Q(1,4)])}
    # Select rational generic thresholds from independent order-induced base
    # vertices. They define the test INPUT; the route gets none of this table.
    for interval in (True,False):
        n=4;base=building(n,interval=interval);A,b,_,_=alg.model(base)
        B=base['base'];S,w=alg.base.presentation(n,B['subsets'],None)
        V={alg.base.point(n,S,w,p)[0][:-1] for p in permutations(range(n))}
        cuts=[[1,3,-2]] if interval else [[2,-1,4],[-1,3,2]]
        rhs=[]
        for a in cuts:
            vals=[lp.dot(a,x) for x in V];rhs.append(max(vals)-(max(vals)-min(vals))/4+Q(1,13))
        out['interval4_cut' if interval else 'permuta4_two_cuts']=building(n,cuts,rhs,interval)
    return out


def small_stage():
    rng=random.Random(271);results=[];totals={k:0 for k in ['routes','original_edges','shortest_edges','nonshortest','LP_calls','LP_pivots','sample_queries','full_direction_chambers','all_edge_direction_checks','new_direction_edges','common_rows_checks','square_systems','vertices','graph_edges']}
    for name,data in models().items():
        A,b,D,C=alg.model(data);cover,s,_=alg.catalogue(D,C);V,G,acts,ref=reference(A,b)
        edgecount=outside=0;highest_face=0
        for i in range(len(V)):
            for j in G[i]:
                if i>=j:continue
                delta=alg.line(tuple(y-x for x,y in zip(V[i],V[j])))
                alg.require(delta in cover,'actual cut edge omitted from direction cover')
                outside+=delta not in D;edgecount+=1
                mid=tuple((x+y)/2 for x,y in zip(V[i],V[j]));baseA=A[:len(A)-len(C)]
                I=[a for a,t in zip(baseA,b) if lp.dot(a,mid)==t]
                import sympy as sp
                f=len(A[0])-(sp.Matrix(I).rank() if I else 0)
                highest_face=max(highest_face,f)
                alg.require(f<=len(C)+1,'base-face dimension bound failed')
        pairs=list(combinations(range(len(V)),2))
        exhaustive=len(pairs)<=36
        if not exhaustive:pairs=rng.sample(pairs,36)
        pairs += [(0,0)]
        local={'routes':0,'route_edges':0,'shortest':0,'nonshortest':0};best=None
        for i,j in pairs:
            inp={**data,'start':lp.serial(V[i]),'target':lp.serial(V[j])};out=alg.construct(inp)
            path=[tuple(map(Q,x)) for x in out['certificate']['path']]
            alg.require(all(y in V and V.index(y) in G[V.index(x)] for x,y in zip(path,path[1:])),'not a reference original edge')
            shortest=dist(G,i)[j];L=len(path)-1
            alg.require(L>=shortest,'route shorter than BFS')
            local['routes']+=1;local['route_edges']+=L;local['shortest']+=shortest;local['nonshortest']+=L>shortest
            totals['routes']+=1;totals['original_edges']+=L;totals['shortest_edges']+=shortest;totals['nonshortest']+=L>shortest
            for k in ['LP_calls','LP_pivots','sample_queries','full_direction_chambers']:totals[k]+=out['discovery'][k]
            totals['common_rows_checks']+=len(path)*out['verified']['common_original_rows_retained']
            if best is None or L>best['verified']['original_edges']:best={'input':inp,**out,'independent_shortest':shortest}
        for k,val in [('all_edge_direction_checks',edgecount),('new_direction_edges',outside),('square_systems',ref['square_systems']),('vertices',ref['vertices']),('graph_edges',ref['graph_edges'])]:totals[k]+=val
        results.append({'name':name,**ref,**s,**local,'all_distinct_endpoint_pairs_tested':exhaustive,
                        'non_base_direction_edges':outside,'maximum_base_face_dimension_for_cut_edges':int(highest_face)})
        dump(ROOT/f'fixtures/cut_direction_{name}.json',best);print(name,results[-1],flush=True)
    # The cube example needs the full k+1: an edge lies inside a 3D base face
    # after two cuts, with direction (1,-1,1), outside every two-axis span.
    data=models()['box3_two_cuts_nonsimple'];A,b,D,C=alg.model(data)
    u=(Q(0),Q(1),Q(0));v=(Q(1),Q(0),Q(1))
    alg.require(all(lp.dot(a,x)<=z for a,z in zip(A,b) for x in [u,v]),'sharpness endpoints')
    common=set(alg.active(A,b,u))&set(alg.active(A,b,v))
    alg.require(len(alg.rref([A[i] for i in common],3)[1])==2,'sharpness pair not an edge')
    return {'totals':totals,'models':results,'k_plus_one_is_necessary_example':{'k':2,'base_face_dimension':3,'direction':[1,-1,1]}}


def large_stage():
    results=[]
    for d,k in [(8,1),(16,1),(32,1),(12,2),(24,2)]:
        C=[list(range(1,d+1))];b=[Q(sum(C[0])*2,3)]
        if k==2:C.append([((i*5)%d)+1 for i in range(d)]);b.append(Q(sum(C[1])*3,5))
        data=box(d,C,b);A,h,_,_=alg.model(data);start=[0]*d
        endpoint_solver=lp.ExactLP(A,h,start)
        target=endpoint_solver.maximize([Q((i+2)**2) for i in range(d)])['point']
        inp={**data,'start':start,'target':target};begin=time.monotonic();out=alg.construct(inp)
        r=out['verified'];results.append({**r,**out['discovery'],'seconds':round(time.monotonic()-begin,3),
                                        'source_base_cube_vertex_count':2**d,'cut_vertex_count_claimed':False})
        if d in (32,24):dump(ROOT/f'fixtures/cut_direction_large_{d}_{k}.json',{'input':inp,**out})
        print('large',d,k,r['original_edges'],r['catalogue_lines'],out['discovery'],flush=True)
    return results


def capped_box(d):
    rng=random.Random(272+d);codes={(1<<d)-(1<<j) for j in range(1,d)}
    while len(codes)<2*d-2:codes.add(rng.randrange(1,(1<<d)-1))
    C=[];h=[];weights={}
    for code in sorted(codes):
        w=[rng.randrange(1,8) for _ in range(d)];weights[code]=w
        C.append([w[i]*(1 if code>>i&1 else -1) for i in range(d)])
        h.append(sum(w[i] for i in range(d) if code>>i&1)-Q(1,5))
    data=box(d,C,h);data.update(max_cut_overlap=1,start=[0]*d,target=[1]*d)
    # Explicit cubical chain with each removed intermediate corner replaced
    # by the edge of its simplex cap. All steps are audited on FINAL H rows.
    cubes=[[Q(i>=d-j) for i in range(d)] for j in range(d+1)]
    path=[tuple(cubes[0])]
    def code(x):return sum((1<<i) for i,z in enumerate(x) if z)
    for a,b in zip(cubes,cubes[1:]):
        i=next(j for j in range(d) if a[j]!=b[j]);delta=[v-u for u,v in zip(a,b)]
        if code(a) in weights:
            t=Q(1,5*weights[code(a)][i]);p=tuple(x+t*y for x,y in zip(a,delta))
            if path[-1]!=p:path.append(p)
        t=Q(1,5*weights[code(b)][i]) if code(b) in weights else Q(0)
        p=tuple(x-t*y for x,y in zip(b,delta))
        if path[-1]!=p:path.append(p)
    A,b,_,_=alg.model(data)
    for x in path:
        alg.require(all(lp.dot(a,x)<=z for a,z in zip(A,b)),'comparison point infeasible')
        alg.check_rank(A,alg.rank_certificate(A,alg.active(A,b,x),d),d)
    for u,v in zip(path,path[1:]):
        J=sorted(set(alg.active(A,b,u))&set(alg.active(A,b,v)))
        alg.check_rank(A,alg.rank_certificate(A,J,d-1),d-1)
    alg.require(len(path)-1==2*d-1,'cubical chain detour count')
    return data,path


def overlap_stage():
    records=[]
    for d in [4,8,16]:
        data,comparison=capped_box(d);t=time.monotonic();out=alg.construct(data);r=out['verified']
        s=len(data['cuts_A'])
        alg.require(len(out['certificate']['overlap']['proofs'])==s*(s-1)//2,'incomplete pair exclusion')
        record={**r,**out['discovery'],'separated_cut_pairs':s*(s-1)//2,
                'genuine_facets_by_truncation_proof':2*d+s,
                'vertices_by_truncation_proof':2**d+s*(d-1),
                'explicit_comparison_edges':len(comparison)-1,
                'comparison_shortest_claimed':False,'seconds':time.monotonic()-t}
        if d==4:
            A,b,D,C=alg.model(data);V,G,_,ref=reference(A,b)
            for path in [comparison,[tuple(map(Q,x)) for x in out['certificate']['path']]]:
                alg.require(all(V.index(y) in G[V.index(x)] for x,y in zip(path,path[1:])),'cap route not an original graph path')
            record['independent_reference']=ref
            record['independent_distance']=dist(G,V.index(tuple(data['start'])))[V.index(tuple(data['target']))]
        dump(ROOT/f'fixtures/cut_direction_overlap_{d}.json',{'input':data,**out,'comparison_path':comparison})
        records.append(record);print('overlap',d,r['original_edges'],r['direction_bound'],r['unrestricted_vandermonde_bound'],flush=True)
    thin=[]
    for power in [20,80,160]:
        eps=Q(1,2**power);data=box(3,[[1,1,1]],[3-eps]);data.update(start=[0,0,0],target=[1,1,1-eps])
        result=alg.construct(data);thin.append({'epsilon_power':power,**result['verified']})
    # The r<=k+1 allowance is sharp in every dimension: path stable-set
    # inequalities have an interior-base edge with alternating full support.
    sharp=[]
    for d in [3,4,6]:
        C=[[Q(j==i or j==i+1) for j in range(d)] for i in range(d-1)]
        data=box(d,C,[1]*(d-1));data.update(start=[i%2 for i in range(d)],target=[1-i%2 for i in range(d)])
        out=alg.construct(data);alg.require(out['verified']['original_edges']==1,'common-face edge should be one step')
        sharp.append({'dimension':d,'cuts':d-1,'full_support_direction':[-1 if i%2 else 1 for i in range(d)],'route_edges':1})
    return {'many_disjoint_cuts':records,'tiny_slack_cases':thin,'dimension_cutoff_sharpness':sharp}


def affine_stage():
    cases=[]
    for name in ['box3_one_cut','box3_two_cuts_nonsimple','interval4_cut','permuta4_two_cuts']:
        data=models()[name];A,b,_,_=alg.model(data);V,G,_,_=reference(A,b);u,v=V[0],V[-1]
        out=alg.construct({**data,'start':u,'target':v});d=len(u)
        # Dense nonsingular affine map, supplied and exactly bound.
        T=[[Q(i==j)+Q((i+1)*(j+1)) for j in range(d)] for i in range(d)]
        inv=alg.inverse(T);shift=[Q(j+1,7) for j in range(d)]
        moved=deepcopy(data);moved.pop('A');moved.pop('b');moved['affine_chart']={'matrix':T,'offset':shift}
        C=[];h=[]
        for a,z in zip(data['cuts_A'],data['cuts_b']):
            a=list(map(Q,a));row=tuple(sum(a[i]*inv[i][j] for i in range(d)) for j in range(d))
            C.append(row);h.append(Q(z)+lp.dot(row,shift))
        moved['cuts_A']=C;moved['cuts_b']=h;bind(moved)
        image=lambda x:tuple(lp.dot(row,x)+t for row,t in zip(T,shift))
        moved['start']=image(u);moved['target']=image(v);got=alg.construct(moved)
        before=[tuple(map(Q,x)) for x in out['certificate']['path']];after=[tuple(map(Q,x)) for x in got['certificate']['path']]
        # Catalogue lex order can change, but exposed endpoint polynomials and
        # unique objective-line optimizers agree under the exact row map.
        alg.require(after==[image(x) for x in before],'affine covariance of path failed')
        cases.append({'name':name,'edges':len(after)-1,'same_affine_mapped_route':True})
    return cases


def negative_stage():
    data=box(3,[[1,1,0],[0,1,1]],[1,1]);data.update(start=[0,1,0],target=[1,0,1]);out=alg.construct(data);c=out['certificate'];bad=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):bad.append(name)
        else:raise AssertionError('accepted invalid '+name)
    def mutation(name,fn):
        z=deepcopy(c);fn(z);reject(name,lambda:alg.verify(data,z))
    mutation('omit_direction',lambda z:z['catalogue'].pop())
    mutation('false_direction_witness',lambda z:z['witnesses'][0]['base_directions'].append(999))
    mutation('omit_edge',lambda z:z['path'].pop())
    mutation('false_inverse',lambda z:z['vertex_rank'][0]['right_inverse'][0].__setitem__(0,'999'))
    mutation('wrong_edge_rows',lambda z:z['edge_rank'][0].update(rows=[0,1]))
    mutation('false_wall',lambda z:z['walls'][0].update(parameter='0'))
    mutation('negative_dual',lambda z:z['walls'][0].update(dual=[[0,'-1']]))
    mutation('wrong_cut_direction_index',lambda z:z['walls'][0].update(catalogue_line=999))
    mutation('dropped_common_face',lambda z:z['locked_rows'].append(0))
    mutation('wrong_exposure_parameter',lambda z:z['generic'].update(source_parameter=0))
    changed=deepcopy(data);changed['b'][0]='-1';reject('changed_original_H',lambda:alg.verify(changed,c))
    unsupported=deepcopy(data);unsupported['base']={'kind':'arbitrary_H','directions':[[1,0,0]]}
    reject('unproved_base_cover',lambda:alg.construct(unsupported))
    reject('catalogue_cap',lambda:alg.construct(data,subset_cap=1))
    changed=deepcopy(data);changed['start']=[2,2,2];reject('infeasible_endpoint',lambda:alg.construct(changed))
    changed=deepcopy(data);changed['cuts_A'][0][0]=1.0;reject('float_cut',lambda:alg.construct(changed))
    changed=box(2);changed.update(start=[Q(1,2),0],target=[1,1]);reject('nonvertex_endpoint',lambda:alg.construct(changed))
    # An uncut square diagonal has two common tight rows only if rows are
    # maliciously unrelated; an arbitrary edge count cannot replace rank.
    square=box(2);square.update(start=[0,0],target=[1,1]);diag=alg.construct(square)['certificate'];fake=deepcopy(diag)
    fake['path']=[fake['path'][0],fake['path'][-1]];fake['vertex_rank']=[fake['vertex_rank'][0],fake['vertex_rank'][-1]]
    fake['edge_rank']=fake['edge_rank'][:1];fake['walls']=fake['walls'][:1]
    reject('diagonal_not_edge',lambda:alg.verify(square,fake))
    overlap_data,comparison=capped_box(4);oc=alg.construct(overlap_data)['certificate']
    z=deepcopy(oc);z['overlap']['proofs'].pop()
    reject('omitted_cut_overlap_exclusion',lambda:alg.verify(overlap_data,z))
    z=deepcopy(oc);z['overlap']['proofs'][0]['dual']=[[0,'-1']]
    reject('false_overlap_separation',lambda:alg.verify(overlap_data,z))
    false_q=deepcopy(data);false_q['max_cut_overlap']=1
    reject('intersecting_cut_faces_not_disjoint',lambda:alg.construct(false_q))
    # Only LP execution is disabled: the bound checker intentionally reruns
    # its finite catalogue elimination and affine chart binding.
    old=lp.ExactLP
    def forbidden(*args,**kwargs):raise AssertionError('LP during verification')
    lp.ExactLP=forbidden
    try:alg.require(alg.verify(data,json.loads(json.dumps(c)))==out['verified'],'serialized LP-free audit')
    finally:lp.ExactLP=old
    # Parallel/opposite cut normals are one line for the catalogue bound.
    dupe=box(3,[[1,2,3],[2,4,6],[-1,-2,-3]],[4,8,0]);A,b,D,C=alg.model(dupe)
    _,report,_=alg.catalogue(D,C);alg.require(report['raw_cut_rows']==3 and report['distinct_cut_normal_lines']==1,'parallel normalization')
    return {'rejected':len(bad),'names':bad,'LP_disabled_serialized_audit':True,'parallel_cut_rows':3,'parallel_cut_normal_lines':1}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','large','overlap','affine','negative','assemble']);args=p.parse_args()
    stages=['small','large','overlap','affine','negative']
    for s in stages if args.stage is None else [args.stage]:
        if s=='assemble':continue
        begin=time.monotonic();r=globals()[s+'_stage']()
        dump(ROOT/f'research/CUT_DIRECTION_STAGE_{s}.json',{'status':'PASS','source_sha256':hashes(),'result':r,'seconds':time.monotonic()-begin})
        print(s,'PASS',flush=True)
    if args.stage in (None,'assemble'):
        data={s:json.loads((ROOT/f'research/CUT_DIRECTION_STAGE_{s}.json').read_text()) for s in stages}
        alg.require(all(x['status']=='PASS' and x['source_sha256']==hashes() for x in data.values()),'stale or failed stages')
        dump(ROOT/'research/CUT_DIRECTION_CHECK.json',{'status':'PASS','source_sha256':hashes(),'stages':data,
             'scope':'Written closure theorem and exact tests; not Lean or platform verification.'})
if __name__=='__main__':main()
