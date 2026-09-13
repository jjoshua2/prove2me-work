#!/usr/bin/env python3
"""Independent finite-circuit, exact equality, joint-region and original-edge tests.
Large examples use final closed H-data, not generated whole vertex graphs.
"""
from __future__ import annotations
import argparse,hashlib,json,random,time
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
from exact_farkas_lp import parse,rat,serial,dot,require,feasible_point
from finite_summand_capacity import Data,discover,verify,enumerate_circuits
from recognized_finite_summand_routes import build,verify as verify_route,lift_input
from joint_summand_region import discover_region,verify_region,verify_scales,optimize_scales
from antipodal_segment_catalogue import catalogue,verify_catalogue
from hpoly_segment_peeling import peel_one
from recognized_segment_routes import inverse,rank,erase_redundancy,verify_redundancy
from test_segment_peeling import hull,vertices,graph,distances,affine_variant
import implicit_minkowski_lift as lifter
ROOT=Path(__file__).resolve().parents[1]
NEW=['finite_summand_capacity.py','joint_summand_region.py','recognized_finite_summand_routes.py','test_finite_summand_capacity.py']
LEAN=['PolynomialFiniteSummandObstructions.lean','PolynomialJointExtractionGeometry.lean']


def hashes():
    paths=[ROOT/'scripts'/n for n in NEW]+[ROOT/'Solutions'/n for n in LEAN]
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths if p.exists()}


def finite_feasible(C,b,k):
    # Independent intersection enumeration; boxes in the test ensure boundedness.
    for I in combinations(range(len(C)),k):
        try:iv=inverse([C[i] for i in I])
        except ValueError:continue
        x=tuple(dot(r,[b[i] for i in I]) for r in iv)
        if all(dot(a,x)<=t for a,t in zip(C,b)):return True
    return False


def unit_stage():
    rng=random.Random(271);alternatives=0;infeasible=0
    for k in (1,2,3):
        for trial in range(35):
            C=tuple(tuple(Q(rng.randrange(-3,4)) for j in range(k)) for _ in range(3))+\
                tuple(tuple(Q(sg)*Q(i==j) for j in range(k)) for sg in (-1,1) for i in range(k))
            b=tuple(Q(rng.randrange(-3,4)) for _ in range(3))+(Q(2),)*(2*k)
            circuits,_=enumerate_circuits(C)
            ok=all(sum((w*b[i] for i,w in zip(I,weights)),Q(0))>=0 for I,weights in circuits)
            brute=finite_feasible(C,b,k);require(ok==brute,'positive-circuit alternative disagrees with independent vertex feasibility')
            alternatives+=1;infeasible+=not brute
    T=[(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))]
    A=[[1,0],[0,1],[-1,-1]];b=[0,0,1];out=discover(A,b,T,[0,0]);P=Data(A,b,T)
    require(out['verified']['capacity']=='0' and out['verified']['sharp_circuit_size']==3,'missing three-way obstruction')
    rhs=P.allocation_rhs((Q(0),Q(0)),Q(1,4));pairs=0
    for I in combinations(range(len(P.C)),2):
        feasible_point([P.C[i] for i in I],[rhs[i] for i in I]);pairs+=1
    require(all(dot(a,(-Q(1,4),-Q(1,4)))<=t for a,t in zip(P.A,P.rhs(Q(1,4)))),
            'nonempty erosion control missing')
    segment_tests=0
    AA=[[-1,0],[0,-1],[1,0],[0,1],[1,1]];bb=[0,0,2,2,3]
    for g in [(Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(1)),(Q(1),Q(-1))]:
        old=peel_one(AA,bb,g,[0,0]);new=discover(AA,bb,[(Q(0),Q(0)),g],[0,0])
        require(rat(old['certificate']['capacity'])==rat(new['certificate']['capacity']),'segment specialization differs')
        segment_tests+=1
    col=discover([[-1,0],[1,0],[0,-1],[0,1]],[0,2,0,1],[[0,0],[1,0],[2,0],[1,0]],[0,0])
    require(col['verified']['capacity']=='1','affine-dependent candidate handled incorrectly')
    return {'independent_circuit_alternatives':alternatives,'infeasible_cases':infeasible,
        'triangle_pairwise_feasible_subsystems':pairs,'triangle_global_capacity':'0','triangle_erosion_at_quarter_nonempty':True,
        'segment_specialization_checks':segment_tests,'affine_dependent_candidate_capacity':'1'}


def joint_stage():
    T=[(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))];S=T+[(Q(1),Q(1))]
    A,b,V=hull([tuple(a-c for a,c in zip(x,y)) for x in T for y in T],2)
    reg=discover_region(A,b,[T,S],V[0]);c=reg['certificate']
    M=[tuple(map(rat,r['coefficients'])) for r in c['rows']]+[(-Q(1),Q(0)),(Q(0),-Q(1))]
    rhs=[rat(r['rhs']) for r in c['rows']]+[Q(0),Q(0)]
    red=erase_redundancy(M,rhs,[0,0]);K=verify_redundancy(M,rhs,red)
    norm=set()
    for i in K:
        m=max(map(abs,M[i]));norm.add((tuple(x/m for x in M[i]),rhs[i]/m))
    require(norm=={((-Q(1),Q(0)),Q(0)),((Q(0),-Q(1)),Q(0)),((Q(1),Q(1)),Q(1))},'joint region is not the expected triangle')
    caps=[];residualcaps=[]
    for first,second in [(T,S),(S,T)]:
        one=discover(A,b,first,V[0]);two=discover(A,one['core_b'],second,one['certificate']['core_seed'])
        caps.append(one['verified']['capacity']);residualcaps.append(two['verified']['capacity'])
    require(caps==['1','1'] and residualcaps==['0','0'],'order obstruction missing')
    H1=Data(A,b,T).H;H2=Data(A,b,S).H;grid=0
    for t,u in product([Q(i,4) for i in range(5)],repeat=2):
        target=t+u<=1
        algebra=all(dot(tuple(map(rat,r['coefficients'])),(t,u))<=rat(r['rhs']) for r in c['rows'])
        eroded=[z-t*h-u*k for z,h,k in zip(b,H1,H2)];E=vertices(A,eroded)
        actual=False
        if E:
            pts={tuple(p[i]+t*q[i]+u*s[i] for i in range(2)) for p in E for q in T for s in S}
            if rank([tuple(a-b for a,b in zip(p,next(iter(pts)))) for p in pts])==2:
                _,_,sumV=hull(pts,2);actual=set(sumV)==set(V)
        require(algebra==actual==target,'joint circuit region disagrees with independent polygon reconstruction');grid+=1
    opt=optimize_scales(A,b,[T,S],c,[1,1]);require(opt['optimum_certificate']['value']=='1','wrong joint scale optimum')
    (ROOT/'fixtures/joint_triangle_square.json').write_text(json.dumps(serial({'A':A,'b':b,'shapes':[T,S],**reg,'redundancy':red,'optimization':opt}),indent=2)+'\n')
    return {'joint_region':reg['verified'],'separate_capacities':caps,'capacity_after_other_maximal_removal':residualcaps,
        'exact_joint_condition':'s>=0, t>=0, s+t<=1','independent_coefficient_grid_checks':grid,
        'linear_extraction_objective_maximum':'1'}


def pyramid_input(d,t=Q(3,7)):
    require(d>=4,'fixture uses an unaffected coordinate')
    A=[(-Q(1),)+(Q(0),)*(d-1)];b=[Q(0)]
    for i in range(1,d):
        for sg in (-1,1):
            A.append(tuple(Q(j==0)+sg*Q(j==i) for j in range(d)))
            b.append(1+(t if sg==1 and i in (1,2) else 0))
    A.append(tuple(2*Q(j==0)+Q(j in (1,2)) for j in range(d)));b.append(2+t)
    shape=[(Q(0),)*d]+[tuple(Q(i==j) for j in range(d)) for i in (1,2)]
    return {'A':A,'b':b,'candidate_vertices':shape,'start':(Q(0),)+(-Q(1),)*(d-1),
        'end':(Q(0),1+t)+(Q(1),)*(d-2)}


def small_stage():
    T=[(Q(0),Q(0),Q(0)),(Q(1,3),Q(2,5),-Q(1,4)),(-Q(1,5),Q(1,7),Q(2,3))]
    core=[(Q(0),)*3]+[tuple(Q(i==j) for j in range(3)) for i in range(3)]
    A,b,V=hull([tuple(x+y for x,y in zip(p,q)) for p in core for q in T],3)
    cases=[('tetrahedron_plus_triangle',{'A':A,'b':b,'candidate_vertices':T,'start':V[0],'end':V[-1]})]
    shapes=[[(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))],
            [(Q(0),Q(0)),(Q(2),Q(1)),(-Q(1),Q(2))]]
    AA,bb,VV=hull([tuple(x+y for x,y in zip(p,q)) for p in shapes[0] for q in shapes[1]],2)
    cases.append(('two_nonparallel_triangles',{'A':AA,'b':bb,'candidate_vertices':shapes[1],'start':VV[0],'end':VV[-1]}))
    QT=[(Q(0),)*3,(Q(2),Q(0),Q(0)),(Q(0),Q(3),Q(0)),(Q(0),Q(0),Q(5))]
    AA,bb,VV=hull([tuple(x+y for x,y in zip(p,q)) for p in core for q in QT],3)
    cases.append(('nonhomothetic_tetrahedra',{'A':AA,'b':bb,'candidate_vertices':QT,'start':VV[0],'end':VV[-1]}))
    cases.append(('triangle_product',{'A':[[-1,0,0,0],[0,-1,0,0],[1,1,0,0],[0,0,-1,0],[0,0,0,-1],[0,0,1,1]],
        'b':[0,0,1,0,0,1],'candidate_vertices':[[0,0,0,0],[1,0,0,0],[0,1,0,0]],'start':[0,0,0,0],'end':[1,0,1,0]}))
    cases.append(('pyramid_plus_triangle',pyramid_input(4)))
    totals={'models':0,'original_vertices':0,'original_edges':0,'ordered_distances':0,'route_certificates':0,'edge_occurrences':0,
        'segment_free_catalogues':0,'nonshortest_routes':0};examples=[]
    for name,data in cases:
        A,b=parse(data['A'],data['b']);V=vertices(A,b);G=graph(A,b,V);out=build(data);c=out['certificate']
        cat=catalogue(A,b,V[0]);require(cat['verified']['positive_segment_directions']==0,'example was not actually segment-free');totals['segment_free_catalogues']+=1
        tau=rat(c['capacity_certificate']['removed']);resrhs=Data(A,b,data['candidate_vertices']).rhs(tau);EV=vertices(A,resrhs)
        P=Data(A,b,data['candidate_vertices']);candidateV=[(Q(0),)*P.d]+[tuple(tau*z for z in q) for q in P.G]
        pts={tuple(x+y for x,y in zip(p,q)) for p in EV for q in candidateV}
        _,_,checkV=hull(pts,P.d);require(set(checkV)==set(V),'independent whole Minkowski reconstruction failed')
        count=edgecount=largest=0
        for i,u in enumerate(V):
            D=distances(G,i);totals['ordered_distances']+=len(D)
            for j in range(i+1):
                p=deepcopy(data);p['start']=u;p['end']=V[j];cc=deepcopy(c)
                inp,_=lift_input(p,cc);cc['lift']=lifter.build(inp)['certificate'];r=verify_route(p,cc)
                route=[tuple(map(rat,x)) for x in cc['lift']['route']]
                require(all(x in V for x in route) and all(V.index(y) in G[V.index(x)] for x,y in zip(route,route[1:])),
                        'independent original graph rejects returned edge')
                require(D[j]<=r['original_ordinary_edges'],'route beats independent distance')
                totals['nonshortest_routes']+=D[j]<r['original_ordinary_edges'];count+=1;edgecount+=r['original_ordinary_edges'];largest=max(largest,r['original_ordinary_edges'])
        totals['models']+=1;totals['original_vertices']+=len(V);totals['original_edges']+=sum(map(len,G))//2
        totals['route_certificates']+=count;totals['edge_occurrences']+=edgecount
        rec={'name':name,'vertices':len(V),'facets_in_input':len(A),'segment_free':True,'routes':count,'max_returned_route':largest,**out['verified']}
        examples.append(rec);print(name,len(V),count,edgecount,flush=True)
        (ROOT/f'fixtures/finite_summand_{name}.json').write_text(json.dumps(serial({'input':data,**out,'complete_segment_free_catalogue':cat}),indent=2)+'\n')
    return {'totals':totals,'examples':examples}


def large_stage():
    examples=[]
    for d,dense in [(12,False),(24,False),(32,False),(8,True)]:
        data=pyramid_input(d)
        if dense:
            p={**data,'candidate_directions':data['candidate_vertices'][1:]};p.pop('candidate_vertices')
            p=affine_variant(p,734,True);p['candidate_vertices']=[(Q(0),)*d]+p.pop('candidate_directions');data=p
        t=time.monotonic();out=build(data);cat=catalogue(data['A'],data['b'],data['start'])
        require(out['verified']['capacity']=='3/7' and cat['verified']['positive_segment_directions']==0,'large segment-free extraction failure')
        rec={'name':('dense_' if dense else '')+f'pyramid_triangle_{d}d',**out['verified'],
            'complete_segment_free':True,'diagnostic_edges':cat['verified']['walk_edges'],
            'proved_vertex_count':5*2**(d-3)+3,'proved_direction_lower_bound':2**(d-3),
            'full_graph_enumerated':False,'seconds':round(time.monotonic()-t,3)}
        examples.append(rec);print(rec['name'],rec['original_ordinary_edges'],rec['seconds'],flush=True)
        (ROOT/f"fixtures/{rec['name']}.json").write_text(json.dumps(serial({'input':data,**out,'segment_catalogue':cat}),indent=2)+'\n')
    return {'examples':examples,'route_certificates':len(examples),'edge_occurrences':sum(x['original_ordinary_edges'] for x in examples)}


def negative_stage():
    data=pyramid_input(4);out=build(data);c=out['certificate'];A,b=parse(data['A'],data['b']);V=data['candidate_vertices'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forged or unsupported '+name)
    for key,val in [('problem_sha256','bad'),('capacity','99'),('capacity','1/100'),('removed','-1'),('positive_circuits',0),('enumerated_supports',0)]:
        x=deepcopy(c['capacity_certificate']);x[key]=val;reject(key,lambda x=x:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['proofs']=x['proofs'][:-1];reject('missing_positive_circuit',lambda:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['proofs'].append(x['proofs'][0]);reject('duplicate_circuit',lambda:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['proofs'][0]['circuit_weights'][0]='-1';reject('negative_dependence',lambda:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['proofs'][0]['dual']=[[0,'-1']];reject('negative_Farkas_weights',lambda:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['sharp_point']=['99']*4;reject('infeasible_sharpness',lambda:verify(A,b,V,x))
    x=deepcopy(c['capacity_certificate']);x['core_seed']=['99']*4;reject('false_residual_point',lambda:verify(A,b,V,x))
    reject('different_shape',lambda:verify(A,b,[[0]*4,[1,0,0,0],[0,1,0,0]],c['capacity_certificate']))
    reject('singleton_shape',lambda:discover(A,b,[[0]*4]))
    reject('float_shape',lambda:discover(A,b,[[0]*4,[0.1,0,0,0]]))
    reject('circuit_cap',lambda:discover(A,b,V,subset_cap=1))
    reject('oversized_removal',lambda:discover(A,b,V,amount=10))
    x=deepcopy(c);x['lift']['route']=[x['lift']['route'][0],x['lift']['route'][-1]];reject('diagonal_as_edge',lambda:verify_route(data,x))
    x=deepcopy(c);x['core']['apex']=['99']*4;reject('false_core_apex',lambda:verify_route(data,x))
    x=deepcopy(c);x['boundedness']=[];reject('missing_original_boundedness',lambda:verify_route(data,x))
    x=deepcopy(c);x['redundancy']['kept']=x['redundancy']['kept'][:-1];reject('unproved_row_drop',lambda:verify_route(data,x))
    T=[(0,0),(1,0),(0,1)];S=T+[(1,1)];AA,bb,_=hull([tuple(Q(x)-Q(y) for x,y in zip(t,u)) for t in T for u in T],2)
    reg=discover_region(AA,bb,[T,S]);r=reg['certificate']
    x=deepcopy(r);x['rows']=x['rows'][:-1];reject('incomplete_joint_region',lambda:verify_region(AA,bb,[T,S],x))
    x=deepcopy(r);x['rows'][0]['rhs']='99';reject('loosened_joint_bound',lambda:verify_region(AA,bb,[T,S],x))
    x=deepcopy(r);x['rows'][0]['coefficients'][0]='99';reject('false_scale_coefficient',lambda:verify_region(AA,bb,[T,S],x))
    reject('incompatible_individual_maxima',lambda:verify_scales(AA,bb,[T,S],r,[1,1]))
    return {'rejected':len(names),'names':names}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['unit','joint','small','large','negative','assemble']);a=p.parse_args()
    (ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True)
    for stage in ['unit','joint','small','large','negative'] if a.stage is None else [a.stage]:
        if stage=='assemble':continue
        t=time.monotonic();r=globals()[stage+'_stage']();o={'status':'PASS','source_sha256':hashes(),'result':r,'seconds':round(time.monotonic()-t,3)}
        (ROOT/f'research/FINITE_SUMMAND_STAGE_{stage}.json').write_text(json.dumps(serial(o),indent=2,sort_keys=True)+'\n');print(stage,'PASS',o['seconds'],flush=True)
    if a.stage is None or a.stage=='assemble':
        stages={n:json.loads((ROOT/f'research/FINITE_SUMMAND_STAGE_{n}.json').read_text()) for n in ['unit','joint','small','large','negative']}
        require(all(o['status']=='PASS' and o['source_sha256']==hashes() for o in stages.values()),'stale or failed stage')
        deps=['exact_farkas_lp.py','hpoly_segment_peeling.py','recognized_segment_routes.py','implicit_minkowski_lift.py',
              'automatic_segment_routes.py','antipodal_segment_catalogue.py','test_segment_peeling.py']
        total=stages['small']['result']['totals'];big=stages['large']['result']
        out={'status':'PASS','scope':'Exact finite-shape summand capacity, joint coefficient region and original-H routes. New Lean candidates uncompiled.',
             'source_sha256':hashes(),'dependencies_sha256':{n:hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in deps},
             'route_certificates':total['route_certificates']+big['route_certificates'],
             'ordinary_edge_occurrences':total['edge_occurrences']+big['edge_occurrences'],'stages':stages}
        (ROOT/'research/FINITE_SUMMAND_CHECK_2026-09-13.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n');print('TOTAL',out['route_certificates'],out['ordinary_edge_occurrences'])
if __name__=='__main__':main()
