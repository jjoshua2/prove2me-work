#!/usr/bin/env python3
"""Independent cut-level closure and original-H route tests; not Lean evidence."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations,product
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json,random,time
import cut_vertex_levels as algo

ROOT=Path(__file__).resolve().parents[1]
require,dot,serial=algo.require,algo.dot,algo.serial
DEPENDENCIES=['cut_direction_routes.py','exact_farkas_lp.py','endpoint_transfer_routes.py','simple_tangent_policy_audit.py']


def hashes():return {s:hashlib.sha256((ROOT/'scripts'/s).read_bytes()).hexdigest() for s in ['cut_vertex_levels.py','test_cut_vertex_levels.py']+DEPENDENCIES}


def save(path,data):
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(serial(data),sort_keys=True,indent=2)+'\n')


def base(d,edges=None):
    return {'base':{'kind':'box','dimension':d} if edges is None else
            {'kind':'fractional_stable_set','dimension':d,'edges':[list(e) for e in edges]},'cuts_A':[],'cuts_b':[]}


def bind(data):
    A,b,*_=algo.model(data);data.update(A=serial(A),b=serial(b));return data


def reference(A,b):
    import sympy as sp
    d=len(A[0]);V=set();systems=0
    for I in combinations(range(len(A)),d):
        systems+=1;M=sp.Matrix([A[i] for i in I])
        if not M.det():continue
        v=tuple(Q(z) for z in M.inv()*sp.Matrix([b[i] for i in I]))
        if all(dot(a,v)<=t for a,t in zip(A,b)):V.add(v)
    V=sorted(V);act=[set(algo.old.active(A,b,v)) for v in V];G=[set() for v in V]
    for i,j in combinations(range(len(V)),2):
        rows=[A[k] for k in act[i]&act[j]]
        if rows and sp.Matrix(rows).rank()==d-1:G[i].add(j);G[j].add(i)
    dim=sp.Matrix([[a-b for a,b in zip(x,V[0])] for x in V[1:]]).rank() if len(V)>1 else 0
    facets=set()
    for j in range(len(A)):
        I=tuple(i for i in range(len(V)) if j in act[i])
        if not I:continue
        rank=sp.Matrix([[a-b for a,b in zip(V[i],V[I[0]])] for i in I[1:]]).rank() if len(I)>1 else 0
        if dim>0 and rank==dim-1:facets.add(I)
    return V,G,{'genuine_facets':len(facets),'vertices':len(V),'edges':sum(map(len,G))//2,'square_systems':systems,'dimension':int(dim),
                'nonsimple_vertices':sum(len(g)>dim for g in G)}


def distances(G,i):
    D={i:0};todo=deque([i])
    while todo:
        u=todo.popleft()
        for v in G[u]:
            if v not in D:D[v]=D[u]+1;todo.append(v)
    require(len(D)==len(G),'disconnected reference graph');return D


def models():
    data={}
    z=base(3);z.update(cuts_A=[[1,1,1]],cuts_b=[Q(3,2)]);data['cube_one']=bind(z)
    z=base(3);z.update(cuts_A=[[1,2,-1],[2,-1,1]],cuts_b=[Q(9,7),Q(11,7)]);data['cube_two']=bind(z)
    z=base(3);z.update(cuts_A=[[1,1,1],[-1,-1,-1]],cuts_b=[Q(7,5),-Q(7,5)]);data['cube_slice']=bind(z)
    z=base(2);z.update(cuts_A=[[1,1]],cuts_b=[0]);data['cube_point']=bind(z)
    z=base(3,combinations(range(3),2));z.update(cuts_A=[[1,1,1]],cuts_b=[Q(7,5)]);data['triangle_cut']=bind(z)
    z=base(4,combinations(range(4),2));z.update(cuts_A=[[1,1,1,1]],cuts_b=[Q(7,4)]);data['clique4_cut']=bind(z)
    z=base(4,[(0,1),(1,2),(2,3),(0,3)]);z.update(cuts_A=[[1,1,1,1],[1,0,1,0]],cuts_b=[Q(7,4),Q(6,5)]);data['cycle_two']=bind(z)
    z=base(3);e=Q(1,2**80);z.update(cuts_A=[[1,e,0],[e,1,0]],cuts_b=[1+e/2]*2);data['tiny_two']=bind(z)
    # Eight distinct cuts, only two coefficient-column types. All rows bind
    # data even when a reference finds a row redundant; no false facet count.
    z=base(3,[(0,2),(1,2)]);z.update(cuts_A=[[i,8-i,0] for i in range(9)],
        cuts_b=[Q(7,2)+Q((i-4)**2,20) for i in range(9)]);data['many_rank_two']=bind(z)
    return data


def small_stage(selected=None):
    rng=random.Random(276);out=[];tot={k:0 for k in ['routes','route_edges','BFS_edges','nonshortest','coordinate_memberships','base_image_memberships','square_systems','vertices','edges','LP_calls','LP_pivots']}
    for name,data in models().items():
        if selected is not None and name!=selected:continue
        A,b,L,C,h=algo.model(data);levels,report=algo.alphabet(data);V,G,ref=reference(A,b)
        for x in V:require(all(v in levels for v in x),'independent new vertex omitted by alphabet')
        tot['coordinate_memberships']+=len(V)*len(A[0])
        # Independently enumerate the SMALL base graph, checking every grid
        # spectrum used in the general alphabet against actual cut images.
        k=len(C);P,Qbase,*_=algo.model({'base':data['base']});VB,GB,_=reference(P,Qbase)
        for r in report['cut_image_records']:
            I=r['rows'];omega,_=algo.cut_spectrum(C,I,len(A[0]),L,2000000)
            for x in VB:
                require(tuple(dot(C[i],x) for i in I) in omega,'cut image missing');tot['base_image_memberships']+=1
        pairs=list(combinations(range(len(V)),2));exhaustive=len(pairs)<=30
        if not exhaustive:pairs=rng.sample(pairs,30)
        pairs+=[(0,0)];local={'routes':0,'route_edges':0,'BFS_edges':0,'nonshortest':0};saved=None
        for i,j in pairs:
            inp={**data,'start':V[i],'target':V[j]};r=algo.construct(inp)
            path=[tuple(map(Q,v)) for v in r['certificate']['path']]
            require(all(V.index(y) in G[V.index(x)] for x,y in zip(path,path[1:])),'route is not in independent graph')
            length=len(path)-1;best=distances(G,i)[j]
            for key,value in [('routes',1),('route_edges',length),('BFS_edges',best),('nonshortest',int(length>best))]:local[key]+=value;tot[key]+=value
            for key in ['LP_calls','LP_pivots']:tot[key]+=r['discovery'][key]
            if saved is None or length>saved['verified']['original_edges']:saved={'input':inp,**r,'independent_distance':best}
        save(ROOT/f'fixtures/cut_levels_{name}.json',saved)
        for key in ['square_systems','vertices','edges']:tot[key]+=ref[key]
        out.append({'name':name,**ref,**local,'post_cut_levels':len(levels),'cut_rank':report['cut_rank'],
                    'joint_column_types':report['nonzero_joint_column_types'],'all_distinct_pairs':exhaustive})
        print(name,out[-1],flush=True)
    return {'totals':tot,'models':out}


def clique_input(d,power=20):
    e=Q(1,2**power);B=Q(3,2)+e;z=base(d,combinations(range(d),2));z.update(cuts_A=[[1]*d],cuts_b=[B])
    t=(B-1)/(d-2);u=[t]*d;v=u[:];u[0]=1-t;v[-1]=1-t
    z.update(start=u,target=v);return bind(z)


def clique_stage(d):
    inp=clique_input(d,120);start=time.monotonic();r=algo.construct(inp)
    A,b,L,C,h=algo.model(inp);B=h[0];checked=0
    # Each e0--half(S) old edge survives, perhaps shortened by the cut. Their
    # supports certify exponentially many distinct actual original directions.
    samples=[set(range(k)) for k in range(3,d+1)]
    samples += [{0,i,j} for i,j in combinations(range(1,min(d,8)),2)]
    for S in samples:
        x=[Q(0)]*d;x[0]=1
        if len(S)==3:y=[Q(i in S,2) for i in range(d)]
        else:
            t=(B-1)/(len(S)-2);y=[t if i in S else Q(0) for i in range(d)];y[0]=1-t
        algo.vertex_packet(A,b,tuple(x));algo.vertex_packet(A,b,tuple(y));algo.edge_packet(A,b,tuple(x),tuple(y));checked+=1
    out={'dimension':d,'cut_value':str(B),'actual_direction_lower_bound':2**(d-1)-d,
        'sample_directions_checked':checked,**r['verified'],**r['discovery'],
        'complete_final_graph_enumerated':False,
        'genuine_facets_by_explicit_witnesses':d+d*(d-1)//2+1,
        'independent_same_face_distance_formula':2*d-6,
        'shortest_WITHIN_common_face':2*d-6,
        'unrestricted_shortest_distance':3,
        'unrestricted_distance_proof':'Explicit three-edge path; simplicity and the two distinct common-facet release neighbors exclude a two-edge shortcut.',
        'seconds':time.monotonic()-start}
    u=tuple(map(Q,inp['start']));v=tuple(map(Q,inp['target']))
    e0=tuple(Q(i==0) for i in range(d));el=tuple(Q(i==d-1) for i in range(d))
    shortcut=[u,e0,el,v]
    for x in shortcut:algo.vertex_packet(A,b,x)
    for x,y in zip(shortcut,shortcut[1:]):algo.edge_packet(A,b,x,y)
    save(ROOT/f'fixtures/cut_levels_clique{d}.json',{'input':inp,**r,'three_edge_comparison':algo.path_packet(A,b,shortcut)})
    print('clique',d,r['verified']['original_edges'],r['verified']['post_cut_levels'],r['discovery'],flush=True)
    return out


def extra_stage():
    cases=[]
    # Tiny cut magnitudes do not bound discovery by a grid denominator.
    for power in [10,80,160]:
        d=6;e=Q(1,2**power);inp=base(d)
        inp.update(cuts_A=[[1,e,0,0,0,0],[e,1,0,0,0,0]],cuts_b=[1+e/2]*2,
                   start=[0]*d,target=[(1+e/2)/(1+e)]*2+[1]*(d-2));bind(inp)
        out=algo.construct(inp);cases.append({'power':power,**out['verified'],**out['discovery']})
    # More original cuts than aggregate rank. A feasible maximal point is
    # found by a separate LP, not assumed a neighbor or known graph.
    d=8;inp=base(d,[(i,i+1) for i in range(d-1)])
    inp.update(cuts_A=[[Q(i) if j<2 else Q(8-i) if j<4 else Q(0) for j in range(d)] for i in range(9)],
               cuts_b=[Q(7,2)+Q((i-4)**2,20) for i in range(9)])
    A,b,*_=algo.model(inp);solver=algo.lp.ExactLP(A,b,[0]*d);target=solver.maximize([i+1 for i in range(d)])['point']
    inp.update(start=[0]*d,target=target);bind(inp);out=algo.construct(inp,alphabet_cap=4000000)
    cases.append({'case':'nine_cuts_rank_two',**out['verified'],**out['discovery']})
    save(ROOT/'fixtures/cut_levels_many_rank_two_large.json',{'input':inp,**out})
    return cases


def check_clique_face_distance():
    cases=[]
    for d in [4,5,8]:
        data=clique_input(d,20);A,b,*_=algo.model(data);B=Q(data['cuts_b'][0]);rho=B-1;r=d-2
        # Coordinates are (x0,last)=(1-a,a), plus y_1..y_r.
        V=set()
        for q in range(2,r+1):
            for S in combinations(range(r),q):
                ys=[rho/q if i in S else Q(0) for i in range(r)]
                V.add(tuple([1-rho/q]+ys+[rho/q]));V.add(tuple([rho/q]+ys+[1-rho/q]))
        for i in range(r):
            for j in range(r):
                if i==j:continue
                ys=[Q(1,2) if k==i else rho-Q(1,2) if k==j else Q(0) for k in range(r)]
                V.add(tuple([Q(1,2)]+ys+[Q(1,2)]))
        V=sorted(V);acts=[]
        for x in V:
            require(all(dot(a,x)<=z for a,z in zip(A,b)),'invalid classified face vertex')
            algo.vertex_packet(A,b,x);acts.append(set(algo.old.active(A,b,x)))
        G=[set() for _ in V]
        for i,j in combinations(range(len(V)),2):
            common=sorted(acts[i]&acts[j])
            if len(algo.old.rref([A[k] for k in common],d)[1])==d-1:G[i].add(j);G[j].add(i)
        u=tuple(map(Q,data['start']));v=tuple(map(Q,data['target']))
        distance=distances(G,V.index(u))[V.index(v)]
        require(distance==2*d-6,'closed face classification gives wrong distance')
        cases.append({'ambient_dimension':d,'entire_common_face_vertices':len(V),
                      'common_face_edges':sum(map(len,G))//2,'shortest_distance':distance,
                      'full_polytope_graph_enumerated':False})
    return cases



def check_full_clique_distance():
    cases=[]
    for d in [4,5,6]:
        data=clique_input(d,20);A,b,*_=algo.model(data);B=Q(data['cuts_b'][0]);V={(Q(0),)*d}
        V.update(tuple(Q(i==j) for i in range(d)) for j in range(d))
        for S in combinations(range(d),3):V.add(tuple(Q(i in S,2) for i in range(d)))
        for q in range(4,d+1):
            for S in combinations(range(d),q):
                for c in S:
                    t=(B-1)/(q-2);V.add(tuple(1-t if i==c else t if i in S else Q(0) for i in range(d)))
        for S in combinations(range(d),4):
            for c in S:V.add(tuple(B-Q(3,2) if i==c else Q(1,2) if i in S else Q(0) for i in range(d)))
        V=sorted(V);acts=[]
        for x in V:
            require(all(dot(a,x)<=z for a,z in zip(A,b)),'invalid classified clique vertex')
            algo.vertex_packet(A,b,x);acts.append(set(algo.old.active(A,b,x)))
        G=[set() for _ in V]
        for i,j in combinations(range(len(V)),2):
            shared=sorted(acts[i]&acts[j])
            if len(shared)<d-1:continue
            if len(algo.old.rref([A[k] for k in shared],d)[1])==d-1:G[i].add(j);G[j].add(i)
        u,v=tuple(map(Q,data['start'])),tuple(map(Q,data['target']))
        dist=distances(G,V.index(u))[V.index(v)]
        require(dist==(2 if d==4 else 3),'unrestricted distance differs from proof')
        cases.append({'dimension':d,'complete_classified_vertices':len(V),'original_graph_edges':sum(map(len,G))//2,
                      'unrestricted_distance':dist,'within_common_face_distance':2*d-6,
                      'completeness_uses_proved_clique_base_and_one_cut_edge_classification':True})
    return cases

def obstruction_stage():
    rows=[]
    for d in [4,8,12]:
        a=[Q(1)]+[Q(1,2**(j+1)) for j in range(1,d)];B=Q(3,4)
        inp=base(d);inp.update(cuts_A=[a],cuts_b=[B]);A,b,*_=algo.model(inp);values=set()
        for bits in product([0,1],repeat=d-1):
            x=(B-dot(a[1:],bits),)+tuple(map(Q,bits));require(0<x[0]<1,'not a cut-cube vertex')
            # The d-1 binary box rows and the cut form an explicitly triangular
            # independent active system. Test some full inverse packets too.
            require(all(dot(r,x)<=t for r,t in zip(A,b)),'invalid obstruction vertex');values.add(x[0])
        require(len(values)==2**(d-1),'subset-sum levels not distinct')
        x=tuple([B]+[Q(0)]*(d-1));algo.vertex_packet(A,b,x)
        rows.append({'dimension':d,'cuts':1,'distinct_joint_column_types':d,
                     'actual_first_coordinate_levels':len(values),'count_is_exponential':True,
                     'graph_diameter_by_combinatorial_cube_proof':d,'diameter_obstruction':False})
    return {'exponential_level_controls':rows,'same_face_distance_checks':check_clique_face_distance(),'unrestricted_distance_checks':check_full_clique_distance()}


def negative_stage():
    data=clique_input(4,10);out=algo.construct(data);c=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted invalid '+name)
    def mutation(name,fn):
        bad=deepcopy(c);fn(bad);reject(name,lambda:algo.verify(data,bad))
    mutation('omit_level',lambda z:z['alphabet'].pop())
    mutation('alter_spectrum_count',lambda z:z['alphabet_report'].update(post_cut_levels=0))
    mutation('missing_stage',lambda z:z['stages'].pop())
    mutation('wrong_side',lambda z:z['stages'][0].update(sign=-z['stages'][0]['sign']))
    mutation('false_extreme_dual',lambda z:z['stages'][0]['optimum'].update(dual=[[0,'-1']]))
    mutation('false_edge_rank',lambda z:z['stages'][0]['left']['edge_rank'][0]['right_inverse'][0].__setitem__(0,'999'))
    mutation('changed_original_lock',lambda z:z['locked_original_rows'].append(0))
    mutation('diagonal_output',lambda z:z.update(path=[z['path'][0],z['path'][-1]]))
    mutation('missing_endpoint_rank',lambda z:z['endpoint_ranks'].pop())
    changed=deepcopy(data);changed['base']={'kind':'arbitrary','dimension':4}
    reject('unproved_base_levels',lambda:algo.construct(changed))
    changed=deepcopy(data);changed['cuts_A'][0][0]=1.0
    reject('float_coefficient',lambda:algo.construct(changed))
    changed=deepcopy(data);changed['b'][0]='-1'
    reject('changed_original_H',lambda:algo.verify(changed,c))
    reject('alphabet_cap',lambda:algo.construct(data,alphabet_cap=1))
    reject('edge_cap',lambda:algo.construct(data,edge_cap=0))
    changed=deepcopy(data);changed.update(start=[Q(1,4)]*4,target=[Q(1,4)]*4)
    reject('stationary_nonvertex',lambda:algo.construct(changed))
    lpclass=algo.lp.ExactLP;producer=algo.extreme_improving_ray
    def forbidden(*a,**k):raise AssertionError('geometric discovery in consumer')
    algo.lp.ExactLP=forbidden;algo.extreme_improving_ray=forbidden
    try:require(algo.verify(data,json.loads(json.dumps(c)))==out['verified'],'solver-free serialized audit changed')
    finally:algo.lp.ExactLP=lpclass;algo.extreme_improving_ray=producer
    return {'rejected':len(names),'names':names,'LP_and_ray_discovery_disabled':True,
             'alphabet_elimination_intentionally_recomputed':True}


def main():
    p=argparse.ArgumentParser();p.add_argument('--model');p.add_argument('--stage',choices=['small','clique8','clique16','clique24','extra','obstruction','negative','assemble']);a=p.parse_args()
    stages=['small','clique8','clique16','clique24','extra','obstruction','negative']
    if a.stage is None:
        for name in models():
            begin=time.monotonic();record=small_stage(name)
            save(ROOT/f'research/CUT_LEVEL_MODEL_{name}.json',{'status':'PASS','source_sha256':hashes(),'result':record,'seconds':time.monotonic()-begin})
    for s in stages if a.stage is None else [a.stage]:
        if s=='assemble':continue
        start=time.monotonic()
        if s=='small' and a.model is None:
            records=[json.loads((ROOT/f'research/CUT_LEVEL_MODEL_{n}.json').read_text()) for n in models()]
            require(all(z['source_sha256']==hashes() for z in records),'stale model stage')
            result={'totals':{k:sum(z['result']['totals'][k] for z in records) for k in records[0]['result']['totals']},
                    'models':[z['result']['models'][0] for z in records]}
        else:result=small_stage(a.model) if s=='small' else clique_stage(int(s[6:])) if s.startswith('clique') else globals()[s+'_stage']()
        save(ROOT/(f'research/CUT_LEVEL_MODEL_{a.model}.json' if s=='small' and a.model else f'research/CUT_LEVEL_STAGE_{s}.json'),{'status':'PASS','source_sha256':hashes(),'result':result,'seconds':time.monotonic()-start})
        print(s,'PASS',flush=True)
    if a.stage in (None,'assemble'):
        data={s:json.loads((ROOT/f'research/CUT_LEVEL_STAGE_{s}.json').read_text()) for s in stages}
        require(all(z['status']=='PASS' and z['source_sha256']==hashes() for z in data.values()),'stale test stage')
        save(ROOT/'research/CUT_VERTEX_LEVEL_CHECK.json',{'status':'PASS','source_sha256':hashes(),'stages':data,
            'scope':'Exact software and written proofs; not Lean or Prove2Me acceptance.'})
if __name__=='__main__':main()
