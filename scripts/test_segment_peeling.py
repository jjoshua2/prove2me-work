#!/usr/bin/env python3
"""Independent LP/fiber checks, final-H-only recognized routes and forgery tests.

Small fixture generation is deliberately separate: enumerate a known model's
vertices and reconstruct its final H-polytope before giving ONLY H-data and
candidate directions to the recognizer. Large examples have a closed H-form.
No large original, coarse or refined vertex graph is enumerated.
"""
from __future__ import annotations
import argparse, hashlib, json, random, time
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from pathlib import Path
from exact_farkas_lp import (ExactLP, Unbounded, dot, rat, require, serial,
                            feasible_point, parse, verify_optimum)
from hpoly_segment_peeling import (peel, peel_one, verify_one, verify_peeling,
                                  directions, pair_data)
from recognized_segment_routes import (build, verify, inverse, rank, verify_edges,
                                      reconstruct_lift_input)
import implicit_minkowski_lift as lifter
ROOT=Path(__file__).resolve().parents[1]


def vertices(A,b):
    A,b=parse(A,b);d=len(A[0]);out=set()
    for ids in combinations(range(len(A)),d):
        try: inv=inverse([A[i] for i in ids])
        except ValueError: continue
        x=tuple(dot(r,[b[i] for i in ids]) for r in inv)
        if all(dot(a,x)<=t for a,t in zip(A,b)):out.add(x)
    return sorted(out)


def kernel_line(rows,d):
    a=[list(map(rat,r)) for r in rows];k=0;piv=[]
    for j in range(d):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][j]:
                t=a[i][j];a[i]=[x-t*y for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
    if k!=d-1:return None
    j=next(j for j in range(d) if j not in piv);v=[Q(0)]*d;v[j]=1
    for r,i in zip(a,piv):v[i]=-r[j]
    return tuple(v)


def hull(points,d):
    V=sorted(set(points));facets=set()
    for ids in combinations(range(len(V)),d):
        x=V[ids[0]];a=kernel_line([tuple(y-z for y,z in zip(V[j],x)) for j in ids[1:]],d)
        if a is None:continue
        b=dot(a,x);values=[dot(a,y)-b for y in V]
        if all(z<=0 for z in values) and any(z<0 for z in values):pass
        elif all(z>=0 for z in values) and any(z>0 for z in values):a=tuple(-z for z in a);b=-b
        else:continue
        normal=lifter.line(a+(b,))
        if dot(a,normal[:d])<0:normal=tuple(-z for z in normal)
        facets.add(normal)
    H=sorted(facets);A=tuple(tuple(Q(z) for z in row[:d]) for row in H);b=tuple(Q(row[-1]) for row in H)
    vv=[x for x in V if rank([a for a,t in zip(A,b) if dot(a,x)==t])==d]
    require(vv,'independent full-dimensional hull empty')
    require(vertices(A,b)==vv,'independent H/V hull enumeration disagreement')
    return A,b,vv


def graph(A,b,V):
    d=len(A[0]);I=[{i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t} for x in V]
    G=[set() for _ in V]
    for i,j in combinations(range(len(V)),2):
        if rank([A[k] for k in I[i]&I[j]])==d-1:G[i].add(j);G[j].add(i)
    return G


def distances(G,s):
    D={s:0};todo=deque([s])
    while todo:
        x=todo.popleft()
        for y in G[x]:
            if y not in D:D[y]=D[x]+1;todo.append(y)
    return D


def feedback_fixture(F,u,segments):
    d=len(u);core=[]
    for bits in product((0,1),repeat=d):
        M=[[Q(i==j)-bits[i]*F[i][j] for j in range(d)] for i in range(d)]
        inv=inverse(M);rhs=[v*t for v,t in zip(u,bits)];core.append(tuple(dot(r,rhs) for r in inv))
    points=set(core)
    for g in segments:points|={tuple(x+y for x,y in zip(p,g)) for p in list(points)}
    A,b,V=hull(points,d)
    # A negative all-coordinate objective exposes the all-lower core corner.
    c=tuple(-Q(1) for _ in range(d));maximum=max(dot(c,x) for x in V)
    source=next(x for x in V if dot(c,x)==maximum)
    target=max(V,key=lambda x:sum(x))
    return {'A':A,'b':b,'start':source,'end':target,'candidate_directions':segments},V


def star_final(d,power=80):
    require(d>=3,'positive star plus planar factor required')
    p=d-2;eps=Q(1,2**power);l=Q(3,7);m=Q(2,5)
    A=[];b=[]
    for i in range(p):A.append(tuple(-Q(i==j) for j in range(d)));b.append(Q(0))
    for i in range(p):A.append(tuple(Q(i==j)-Q(i>0 and j==0) for j in range(d)));b.append(Q(1))
    gs=[(Q(1),Q(0)),(Q(0),Q(1)),(l,l),(m,m*(1+eps))]
    for g in gs:
        for sign in(-1,1):
            n=(sign*g[1],-sign*g[0]);A.append((Q(0),)*p+n)
            b.append(sum((max(Q(0),dot(n,h)) for h in gs),Q(0)))
    start=(Q(0),)*d;end=(Q(1),)+(Q(2),)*(p-1)+(sum(g[0] for g in gs),sum(g[1] for g in gs))
    return {'A':A,'b':b,'start':start,'end':end,
            'candidate_directions':[(Q(0),)*p+(Q(1),Q(1)),(Q(0),)*p+(Q(1),1+eps)]}


def affine_variant(data,seed,dense=True):
    """Generate hidden coordinates and an unknown translation; nothing about
    this chart, its segment lengths, or its core is passed to the recognizer."""
    rng=random.Random(seed);d=len(data['start'])
    if dense:
        u=[Q(rng.choice((-1,1)),rng.randrange(2,7)) for _ in range(d)]
        v=[Q(rng.choice((-1,1)),rng.randrange(2,7)) for _ in range(d-1)]
        v.append(-sum((a*b for a,b in zip(u,v)),Q(0))/u[-1])
        T=tuple(tuple(Q(i==j)+u[i]*v[j] for j in range(d)) for i in range(d))
    else:T=tuple(tuple(Q(i==j)*Q(rng.randrange(1,7),rng.randrange(1,7)) for j in range(d)) for i in range(d))
    Ti=inverse(T);offset=tuple(Q(rng.randrange(-5,6),7) for _ in range(d))
    A=[];b=[]
    for a,t in zip(data['A'],data['b']):
        r=tuple(sum((a[k]*Ti[k][j] for k in range(d)),Q(0)) for j in range(d))
        z=Q(rng.randrange(1,8),rng.randrange(1,8));A.append(tuple(z*x for x in r));b.append(z*(t+dot(r,offset)))
    ids=list(range(len(A)));rng.shuffle(ids)
    transform=lambda x:tuple(dot(row,x)+t for row,t in zip(T,offset))
    return {'A':[A[i] for i in ids],'b':[b[i] for i in ids],
            'start':transform(data['start']),'end':transform(data['end']),
            'candidate_directions':[tuple(dot(row,g) for row in T) for g in data['candidate_directions']]}


def exact_capacity(A,b,V,g):
    alpha,plus,minus=directions(A,g)
    return min((C-max(dot(v,x) for x in V))/den
               for i in plus for j in minus for v,C,den in [pair_data(A,b,alpha,i,j)])


def unit_stage():
    rng=random.Random(709);lps=0;caps=0;order_cases=0
    Hs=[([[-1,0],[0,-1],[1,0],[0,1],[1,1]],[0,0,2,2,3]),
        ([[-1,0],[0,-1],[1,1]],[0,0,1]),
        ([[-1,0],[1,0],[0,-1],[0,1]],[0,3,0,2]),
        ([[-1,0],[1,0],[0,-1],[0,1]],[0,3,0,0])]
    for raw,rhs in Hs:
        A,b=parse(raw,rhs);V=vertices(A,b);solver=ExactLP(A,b,V[0])
        for _ in range(40):
            c=tuple(Q(rng.randrange(-9,10),rng.randrange(1,7)) for _ in range(2));out=solver.maximize(c)
            require(rat(out['value'])==max(dot(c,x) for x in V),'simplex differs from complete vertex maximum')
            verify_optimum(A,b,c,out);lps+=1
        for g in [(Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(1)),(Q(1),Q(-1)),(Q(2),Q(3))]:
            out=peel_one(A,b,g,V[0]);require(rat(out['certificate']['capacity'])==exact_capacity(A,b,V,g),'fiber LP differs from direct vertex evaluation');caps+=1
    triangle=peel_one(*Hs[1],(1,0),(0,0));require(rat(triangle['certificate']['capacity'])==0,'triangle falsely has horizontal segment summand')
    # Erosion really is nonempty at tau=1/4; equality with the original fails.
    require(all(dot(a,(Q(0),Q(0)))<=Q(t)-Q(1,4)*max(Q(a[0]),Q(0)) for a,t in zip(*Hs[1])), 'nonempty erosion negative example missing')
    require(feasible_point([[1],[-1]],[3,-2])==(Q(2),),'phase I failed')
    unbounded=False
    try:ExactLP([[-1]],[0],[0]).maximize([1])
    except Unbounded as e:
        require(e.direction[0]>0,'wrong unbounded ray');unbounded=True
    require(unbounded,'unbounded objective silently accepted')
    # A fully zonotopal polygon peels to a point. Capacities remain independent
    # of order, even as affine dimension drops along the sequence.
    gens=[(Q(2),Q(0)),(Q(0),Q(3)),(Q(1),Q(1)),(Q(2),Q(-1))]
    points={(Q(0),Q(0))}
    for g in gens:points|={tuple(x+y for x,y in zip(p,g)) for p in list(points)}
    A,b,V=hull(points,2);expected=None
    for order in permutations(gens):
        result=peel(A,b,order,V[0]);verify_peeling(A,b,result)
        vals={tuple(c['direction']):c['capacity'] for c in result['steps']}
        require(all(rat(x)==1 for x in vals.values()),'maximal transverse amount changed')
        rhs=tuple(map(rat,result['core_b']))
        if expected is None:expected=rhs
        require(rhs==expected,'distinct-direction extraction order changed the residual H-set');order_cases+=1
    repeated=peel(A,b,[gens[0],gens[0]],V[0]);require([rat(c['capacity']) for c in repeated['steps']]==[1,0],'parallel repeat not charged honestly')
    return {'independent_vertex_LP_checks':lps,'independent_capacity_checks':caps,
            'four_direction_order_permutations':order_cases,'triangle_capacity':'0',
            'triangle_positive_erosion_nonempty':True,'phase_I_and_unbounded_ray_pass':True,
            'parallel_repeat_capacities':['1','0'],'zonotope_final_affine_dimension':0}


def small_stage():
    specs=[('feedback2',[[Q(0),Q(1,4)],[Q(1,5),Q(0)]],[Q(1),Q(3,2)],[(Q(1,3),Q(2,5))]),
      ('feedback3',[[Q(0),Q(1,8),Q(1,10)],[Q(1,7),Q(0),Q(1,9)],[Q(1,11),Q(1,12),Q(0)]],
       [Q(1),Q(3,2),Q(4,3)],[(Q(1,3),Q(2,5),Q(1,4))]),
      ('cube3_two_segments',[[Q(0)]*3 for _ in range(3)],[Q(1)]*3,[(Q(1,3),Q(2,5),Q(1,7)),(Q(1,8),-Q(1,6),Q(1,9))])]
    records=[];totals={'models':0,'vertices':0,'edges':0,'ordered_graph_distances':0,'routes':0,
                        'edge_occurrences':0,'original_pair_capacity_checks':0,'nonshortest_routes':0,'chart_reused_for_new_endpoints':0}
    for name,F,u,segments in specs:
        data,V=feedback_fixture(F,u,segments);out=build(data);A,b=parse(data['A'],data['b']);G=graph(A,b,V)
        packet=out['certificate'];amounts=[rat(c['capacity']) for c in packet['peeling']['steps']]
        require(all(x==1 for x in amounts),'hidden segment length recovery failed')
        # Check each sequential maximality claim by independent active-basis enumeration.
        rhs=b
        for item in packet['peeling']['steps']:
            vv=vertices(A,rhs);g=tuple(map(rat,item['direction']))
            require(rat(item['capacity'])==exact_capacity(A,rhs,vv,g),'independent sequential capacity failed')
            rhs=tuple(t-rat(item['removed'])*max(dot(a,g),Q(0)) for a,t in zip(A,rhs));totals['original_pair_capacity_checks']+=1
        nr=ne=0
        for i,x in enumerate(V):
            dist=distances(G,i);totals['ordered_graph_distances']+=len(dist)
            for j in range(i+1):
                p=deepcopy(data);p['start']=x;p['end']=V[j]
                lift_data,_=reconstruct_lift_input(p,packet['peeling'],packet['coarse_redundancy'],packet['feedback_chart'])
                c=deepcopy(packet);c['lift']=lifter.build(lift_data)['certificate'];report=verify(p,c)
                route=[tuple(map(rat,v)) for v in c['lift']['route']]
                require(all(y in V for y in route) and all(V.index(y) in G[V.index(z)] for z,y in zip(route,route[1:])), 'independent ORIGINAL graph rejected route')
                require(len(route)-1>=dist[j],'route shorter than graph distance')
                totals['nonshortest_routes']+=int(len(route)-1>dist[j]);nr+=1;ne+=len(route)-1
                totals['chart_reused_for_new_endpoints']+=int(x!=tuple(data['start']))
        totals['models']+=1;totals['vertices']+=len(V);totals['edges']+=sum(map(len,G))//2;totals['routes']+=nr;totals['edge_occurrences']+=ne
        records.append({'name':name,'dimension':len(u),'FINAL_H_rows':len(A),'vertices':len(V),'original_edges':sum(map(len,G))//2,'route_certificates':nr,'segment_parameters':list(map(str,amounts)), 'discovery':out['verified']})
        print(name,records[-1],flush=True)
        (ROOT/f'fixtures/recognized_{name}.json').write_text(json.dumps(serial({'input':data,**out}),indent=2)+'\n')
    return {'totals':totals,'models':records}


def large_stage():
    records=[]
    for d,power,transform in [(12,80,False),(24,120,False),(32,160,False),(8,70,True)]:
        data=star_final(d,power)
        if transform:data=affine_variant(data,801,True)
        begin=time.monotonic();out=build(data);report=out['verified']
        amounts=[c['capacity'] for c in out['certificate']['peeling']['steps']]
        require(amounts==['3/7','2/5'],'wrong exact hidden near-parallel segments')
        name=('dense_affine_' if transform else '')+f'final_H_{d}d'
        record={'name':name,**report,'epsilon_power':power,'recovered_parameters':amounts,
            'full_vertex_count_formula':2**(d+1),'proved_direction_lower_bound':2**(d-3)+d-3,
            'supplied_decomposition':False,'supplied_parent_route':False,'dense_unknown_chart':transform,
            'original_H_is_fully_specified':True,'whole_graph_enumerated':False,'seconds':round(time.monotonic()-begin,3)}
        records.append(record);print(record,flush=True)
        (ROOT/f'fixtures/{name}_peeling.json').write_text(json.dumps(serial({'input':data,**out}),indent=2)+'\n')
    return {'examples':records,'routes':len(records),'ordinary_edges':sum(x['original_ordinary_edges'] for x in records)}


def negative_stage():
    data=star_final(4,20);out=build(data);c=out['certificate'];A,b=parse(data['A'],data['b']);names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forged/unsupported case '+name)
    for field,value in [('capacity','999'),('capacity','1/99'),('removed','-1'),('problem_sha256','bad'),('limiting_pair',[0,0])]:
        x=deepcopy(c['peeling']['steps'][0]);x[field]=value;reject('peel_'+field+'_'+str(value),lambda x=x:verify_one(A,b,x))
    x=deepcopy(c['peeling']['steps'][0]);x['pair_proofs']=x['pair_proofs'][:-1];reject('missing_opposing_pair',lambda:verify_one(A,b,x))
    x=deepcopy(c['peeling']['steps'][0]);x['pair_proofs'][0]['dual']=[[0,'-1']];reject('negative_Farkas_multiplier',lambda:verify_one(A,b,x))
    x=deepcopy(c['peeling']['steps'][0]);x['limiting_point']=[99]*4;reject('infeasible_maximality_point',lambda:verify_one(A,b,x))
    x=deepcopy(c);x['peeling']['segments'][0][0]='1';reject('wrong_extracted_segment',lambda:verify(data,x))
    x=deepcopy(c);x['peeling']['core_b'][0]='-99';reject('wrong_core_rhs',lambda:verify(data,x))
    x=deepcopy(c);x['coarse_redundancy']['deletions'][0]['dual']=[[x['coarse_redundancy']['deletions'][0]['removed_row'],'1']];reject('circular_row_deletion',lambda:verify(data,x))
    x=deepcopy(c);x['coarse_redundancy']['kept']=x['coarse_redundancy']['kept'][:-1];reject('unproved_row_drop',lambda:verify(data,x))
    x=deepcopy(c);x['feedback_chart']['positive_vector']=['0']*4;reject('zero_contraction_witness',lambda:verify(data,x))
    x=deepcopy(c);x['feedback_chart']['anchor']=['99']*4;reject('false_affine_anchor',lambda:verify(data,x))
    x=deepcopy(c);x['lift']['route']=[x['lift']['route'][0],x['lift']['route'][-1]];reject('final_diagonal_as_edge',lambda:verify(data,x))
    x=deepcopy(data);x['end']=[99]*4;reject('changed_endpoint',lambda:verify(x,c))
    x=deepcopy(data);x['candidate_directions']=x['candidate_directions'][::-1];reject('changed_candidates',lambda:verify(x,c))
    x=deepcopy(data);x['A'][0]=[0.0]*4;reject('float_input',lambda:build(x))
    reject('zero_direction',lambda:peel_one(A,b,[0]*4,data['start']))
    reject('oversized_removal',lambda:peel_one(A,b,data['candidate_directions'][0],data['start'],amount=99))
    reject('positive_triangle_segment',lambda:peel_one([[-1,0],[0,-1],[1,1]],[0,0,1],[1,0],amount='1/4'))
    reject('infeasible_phase_I',lambda:feasible_point([[1],[-1]],[1,-2]))
    reject('pivot_cap',lambda:build(data,pivot_cap=1))
    # A missing direction is an unsupported core, not a successful smaller representation.
    x=deepcopy(data);x['candidate_directions']=x['candidate_directions'][:1];reject('incomplete_direction_set_core_not_recognized',lambda:build(x))
    # Redundant/zero original rows and a repeated candidate stay explicitly
    # accounted. The repeated parallel direction has zero remaining capacity.
    boundary=star_final(4,30)
    boundary['A'] += [(Q(0),)*4,boundary['A'][0],tuple(2*x for x in boundary['A'][1])]
    boundary['b'] += [Q(1),boundary['b'][0]+1,2*boundary['b'][1]]
    boundary['candidate_directions'].append(boundary['candidate_directions'][0])
    out=build(boundary)
    require([x['capacity'] for x in out['certificate']['peeling']['steps']]==['3/7','2/5','0'],
            'parallel duplicate acquired phantom segment capacity')
    return {'rejected':len(names),'names':names,'boundary_route':out['verified']}


def source_hashes():
    names=['exact_farkas_lp.py','hpoly_segment_peeling.py','recognized_segment_routes.py','test_segment_peeling.py']
    files=[ROOT/'scripts'/n for n in names]+sorted((ROOT/'Solutions').glob('*.lean'))
    return {str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['unit','small','large','negative','assemble']);args=ap.parse_args()
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    stages=['unit','small','large','negative'] if args.stage is None else [args.stage]
    for stage in stages:
        if stage=='assemble':continue
        begin=time.monotonic();result={'unit':unit_stage,'small':small_stage,'large':large_stage,'negative':negative_stage}[stage]()
        packet={'stage':stage,'status':'PASS','seconds':round(time.monotonic()-begin,3),'source_sha256':source_hashes(),'result':result}
        (ROOT/f'research/SEGMENT_PEEL_STAGE_{stage}.json').write_text(json.dumps(serial(packet),indent=2,sort_keys=True)+'\n');print(stage,'PASS',packet['seconds'],flush=True)
    if args.stage is None or args.stage=='assemble':
        data={}
        for stage in ['unit','small','large','negative']:
            packet=json.loads((ROOT/f'research/SEGMENT_PEEL_STAGE_{stage}.json').read_text());require(packet['source_sha256']==source_hashes() and packet['status']=='PASS','stale/failed stage');data[stage]=packet
        out={'status':'PASS','scope':'Exact final-H decomposition, maximality and ordinary-edge checks; not Lean/platform acceptance or universal recognition.',
             'source_sha256':source_hashes(),'unchanged_lifter_sha256':hashlib.sha256((ROOT/'scripts/implicit_minkowski_lift.py').read_bytes()).hexdigest(),
             'stages':data,'route_certificates':data['small']['result']['totals']['routes']+data['large']['result']['routes']+1,
             'ordinary_edge_occurrences':data['small']['result']['totals']['edge_occurrences']+data['large']['result']['ordinary_edges']+data['negative']['result']['boundary_route']['original_ordinary_edges']}
        (ROOT/'research/SEGMENT_PEELING_CHECK_2026-09-13.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print('ASSEMBLED',out['route_certificates'],out['ordinary_edge_occurrences'],flush=True)
if __name__=='__main__':main()
