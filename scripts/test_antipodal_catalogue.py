#!/usr/bin/env python3
"""Independent completeness, maximality, original-edge and shortestness checks.
Small reference graphs come from complete H-basis enumeration, never discovery.
Large inputs are final H-systems only; supplied candidate directions are removed.
"""
from __future__ import annotations
import argparse,json,hashlib,random,time
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
from copy import deepcopy
from antipodal_segment_catalogue import catalogue,verify_catalogue,canonical,discover_walk,verify_walk
from automatic_segment_routes import build,verify,make_lift,lower_bound_witness
from exact_farkas_lp import parse,rat,serial,dot,require
from hpoly_segment_peeling import peel_one
from test_segment_peeling import vertices,graph,distances,hull,feedback_fixture,star_final,affine_variant
import implicit_minkowski_lift as lifter
ROOT=Path(__file__).resolve().parents[1]


def sources():
    names=['antipodal_segment_catalogue.py','automatic_segment_routes.py','test_antipodal_catalogue.py']
    paths=[ROOT/'scripts'/n for n in names]+sorted((ROOT/'Solutions').glob('*.lean'))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def small_stage():
    F=[[Q(0),Q(1,4)],[Q(1,5),Q(0)]]
    fb,_=feedback_fixture(F,[Q(1),Q(3,2)],[(Q(1,3),Q(2,5))]);fb.pop('candidate_directions')
    models=[('square',{'A':[[-1,0],[0,-1],[1,0],[0,1]],'b':[0,0,1,1],'start':[0,0],'end':[1,1]}),
       ('triangle',{'A':[[-1,0],[0,-1],[1,1]],'b':[0,0,1],'start':[0,0],'end':[1,0]}),
       ('tetrahedron',{'A':[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],'b':[0,0,0,1],'start':[0,0,0],'end':[1,0,0]}),
       ('square_pyramid',{'A':[[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],'b':[0,1,1,1,1],'start':[0,0,1],'end':[1,1,0]}),
       ('triangular_prism',{'A':[[-1,0,0],[0,-1,0],[1,1,0],[0,0,-1],[0,0,1]],'b':[0,0,1,0,1],'start':[0,0,0],'end':[1,0,1]}),
       ('implicit_line',{'A':[[1,0],[-1,0],[0,1],[0,-1]],'b':[2,0,0,0],'start':[0,0],'end':[2,0]}),
       ('hidden_feedback',fb)]
    # Five-generator 3D zonotope recovered from final inequalities only.
    V={(Q(0),)*3}
    gens=[(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1)),(Q(1),Q(1),Q(0)),(Q(1),Q(-1),Q(1))]
    for g in gens:V|={tuple(x+y for x,y in zip(v,g)) for v in list(V)}
    A,b,V=hull(V,3);models.append(('zonotope5',{'A':A,'b':b,'start':min(V),'end':max(V)}))
    p=star_final(4,12);p.pop('candidate_directions');models.append(('star_plus_thin_zonogon',p))
    counts={'models':0,'vertices':0,'edges':0,'ordered_distances':0,'complete_catalogues':0,'independent_all_edge_capacity_tests':0,
            'route_certificates':0,'route_edges':0,'proved_shortest_routes':0,'not_shortest':0,'stationary_diagnostic_pivots':0}
    recs=[]
    for name,data in models:
        A,b=parse(data['A'],data['b']);V=vertices(A,b);G=graph(A,b,V)
        edge_dirs=sorted({canonical(tuple(y-x for x,y in zip(V[i],V[j]))) for i,ns in enumerate(G) for j in ns})
        positive={g:rat(peel_one(A,b,g,V[0])['certificate']['capacity']) for g in edge_dirs}
        positive={g:t for g,t in positive.items() if t>0};counts['independent_all_edge_capacity_tests']+=len(edge_dirs)
        # Repeat discovery from every source in small models, sampled sources in the larger small graphs.
        indices=range(len(V)) if len(V)<=8 else sorted(set([0,len(V)//3,len(V)//2,len(V)-1]))
        residual=None
        for i in indices:
            cat=catalogue(A,b,V[i]);c=cat['certificate'];counts['complete_catalogues']+=1
            counts['stationary_diagnostic_pivots']+=c['walk']['discovery']['stationary_pivots']
            found={tuple(map(rat,s['direction'])):rat(s['capacity']) for s in c['peeling']['steps'] if rat(s['capacity'])>0}
            require(found==positive,'antipodal catalogue missed a true segment direction or maximal amount')
            rhs=tuple(map(rat,c['peeling']['core_b']))
            if residual is None:residual=rhs
            require(rhs==residual,'maximal residual depends on diagnostic start/objective')
            for g in found:
                path=[tuple(map(rat,x)) for x in c['walk']['route']]
                hits=sum(canonical(tuple(v-u for u,v in zip(x,y)))==g for x,y in zip(path,path[1:]))
                require(hits==1,'a global summand direction was not crossed exactly once monotonically')
        packet=build(data)['certificate'];nr=ne=short=0
        for i,u in enumerate(V):
            D=distances(G,i);counts['ordered_distances']+=len(D)
            for j in range(i+1):
                p=deepcopy(data);p['start']=u;p['end']=V[j];c=deepcopy(packet)
                inp,_=make_lift(p,c);c['lift']=lifter.build(inp)['certificate']
                c['lower_bound']=lower_bound_witness(A,b,u,V[j],c['catalogue']['peeling']['segments'])
                got=verify(p,c);path=[tuple(map(rat,x)) for x in c['lift']['route']]
                require(all(x in V for x in path) and all(V.index(y) in G[V.index(x)] for x,y in zip(path,path[1:])),'independent original H-graph rejected route')
                require(got['certified_distance_lower_bound']<=D[j]<=got['actual_original_route_edges'],'false lower or upper bound')
                if got['shortest_certified']:require(got['actual_original_route_edges']==D[j],'false shortestness certificate')
                if c['core']['kind']=='point':require(got['shortest_certified'],'recognized zonotope path not shortest')
                nr+=1;ne+=got['actual_original_route_edges'];short+=got['shortest_certified']
                counts['not_shortest']+=int(got['actual_original_route_edges']>D[j])
        counts['models']+=1;counts['vertices']+=len(V);counts['edges']+=sum(map(len,G))//2
        counts['route_certificates']+=nr;counts['route_edges']+=ne;counts['proved_shortest_routes']+=short
        rec={'name':name,'dimension':len(A[0]),'rows':len(A),'vertices':len(V),'edge_directions':len(edge_dirs),
             'true_segment_directions':len(positive),'core':packet['core']['kind'],'all_pair_routes':nr,'certified_shortest':short}
        recs.append(rec);print(rec,flush=True)
        (ROOT/f'fixtures/automatic_{name}.json').write_text(json.dumps(serial({'input':data,'certificate':packet}),indent=2)+'\n')
    return {'counts':counts,'examples':recs}


def large_stage():
    out=[]
    for d,power,dense in [(12,80,False),(24,120,False),(32,160,False),(8,70,True)]:
        data=star_final(d,power)
        if dense:data=affine_variant(data,1121,True)
        data.pop('candidate_directions');begin=time.monotonic();r=build(data)
        require(r['verified']['shortest_certified'] and r['verified']['actual_original_route_edges']==d+2,'large shortestness certificate changed')
        require(r['verified']['positive_segment_directions']==d+1,'complete factor count changed')
        name=('dense_' if dense else '')+f'blind_H_{d}d'
        rec={'name':name,**r['verified'],'epsilon_power':power,'genuine_original_facets':2*d+4,
             'known_full_vertex_count':2**(d+1),'known_full_direction_lower_bound':2**(d-3)+d-3,'seconds':round(time.monotonic()-begin,3)}
        out.append(rec);print({k:rec[k] for k in ['name','diagnostic_walk_edges','tested_candidate_directions','positive_segment_directions','actual_original_route_edges','shortest_certified','seconds']},flush=True)
        (ROOT/f'fixtures/{name}.json').write_text(json.dumps(serial({'input':data,**r}),indent=2)+'\n')
    return {'examples':out,'route_certificates':len(out),'ordinary_edges':sum(r['actual_original_route_edges'] for r in out)}


def negative_stage():
    data=star_final(4,20);data.pop('candidate_directions');out=build(data);c=out['certificate'];names=[]
    def reject(name,call):
        try:call()
        except (ValueError,KeyError,TypeError,ZeroDivisionError,IndexError):names.append(name)
        else:raise AssertionError('forgery accepted '+name)
    for field,value in [('candidate_directions',[]),('normal',['0']*4),('source_weights',['0']*4),('target_weights',['0']*4),('boundedness',[])]:
        x=deepcopy(c);x['catalogue']['walk'][field]=value;reject('cover_'+field,lambda x=x:verify(data,x))
    x=deepcopy(c);x['catalogue']['walk']['target_basis']=x['catalogue']['walk']['source_basis'];reject('not_opposite_exposed',lambda:verify(data,x))
    x=deepcopy(c);x['catalogue']['walk']['route']=[x['catalogue']['walk']['route'][0],x['catalogue']['walk']['route'][-1]];reject('cover_diagonal',lambda:verify(data,x))
    x=deepcopy(c);x['catalogue']['peeling']['steps']=x['catalogue']['peeling']['steps'][:-1];reject('untested_cover_direction',lambda:verify(data,x))
    x=deepcopy(c);next(s for s in x['catalogue']['peeling']['steps'] if rat(s['capacity'])>0)['removed']='0';reject('partial_peeling_not_complete',lambda:verify(data,x))
    x=deepcopy(c);x['core']['apex']=['99']*4;reject('false_pyramid_apex',lambda:verify(data,x))
    x=deepcopy(c);x['core']={'kind':'point','point':data['start']};reject('false_point_residual',lambda:verify(data,x))
    x=deepcopy(c);x['lower_bound']['segment_bit_changes']=999;reject('false_bit_lower_bound',lambda:verify(data,x))
    x=deepcopy(c);x['lower_bound']['quotient_separator']=['0']*4;reject('false_quotient_separator',lambda:verify(data,x))
    x=deepcopy(c);x['lift']['route']=[x['lift']['route'][0],x['lift']['route'][-1]];reject('refined_diagonal',lambda:verify(data,x))
    x=deepcopy(data);x['end']=[99]*4;reject('changed_endpoint',lambda:verify(x,c))
    x=deepcopy(data);x['A'][0]=[0.0]*4;reject('float',lambda:build(x))
    reject('walk_pivot_cap',lambda:catalogue(data['A'],data['b'],data['start'],pivot_cap=1))
    reject('nonvertex_diagnostic_source',lambda:catalogue([[-1,0],[0,-1],[1,0],[0,1]],[0,0,1,1],['1/2','1/2']))
    reject('unbounded_input',lambda:catalogue([[-1,0],[0,-1]],[0,0],[0,0]))
    # Complete catalogue can succeed while routing recognition correctly fails.
    octa={'A':[list(s) for s in product((-1,1),repeat=3)],'b':[1]*8,'start':[1,0,0],'end':[-1,0,0]}
    cat=catalogue(octa['A'],octa['b'],octa['start'])
    require(cat['verified']['positive_segment_directions']==0,'octahedron false segment')
    reject('segment_free_unsupported_core',lambda:build(octa))
    # Segment-free does not mean Minkowski indecomposable: triangle times triangle.
    productA=[[-1,0,0,0],[0,-1,0,0],[1,1,0,0],[0,0,-1,0],[0,0,0,-1],[0,0,1,1]]
    productB=[0,0,1,0,0,1]
    product_cat=catalogue(productA,productB,[0,0,0,0])
    require(product_cat['verified']['positive_segment_directions']==0,'product of triangles acquired a segment factor')
    # A single vertex's incident edges do not give a complete direction list.
    pts={(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))}
    g=(Q(1),Q(-2));pts|={tuple(x+y for x,y in zip(p,g)) for p in list(pts)}
    A,b,V=hull(pts,2);G=graph(A,b,V)
    witness=next((i for i in range(len(V)) if canonical(g) not in {canonical(tuple(v-u for u,v in zip(V[i],V[j]))) for j in G[i]}),None)
    require(witness is not None,'local incidence negative example missing')
    full=catalogue(A,b,V[witness]);require(full['verified']['positive_segment_directions']>=1,'antipodal walk did not repair local omission')
    # Extra constant and duplicate rows survive discovery and are separately certified.
    p=star_final(4,30);p.pop('candidate_directions');p['A'] += [(Q(0),)*4,p['A'][0]];p['b'] += [1,p['b'][0]]
    rr=build(p)['verified'];require(rr['shortest_certified'],'duplicate boundary failed')
    return {'rejected':len(names),'names':names,'segment_free_octahedron_catalogue':cat['verified'],
            'segment_free_but_decomposable_product':product_cat['verified'],
            'local_star_misses_global_factor':{'vertices':len(V),'source':serial(V[witness]),'missing_direction':serial(canonical(g)),'complete_walk_edges':full['verified']['walk_edges']},
            'duplicate_constant_boundary_route':rr}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','large','negative','assemble']);a=p.parse_args()
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    for stage in ['small','large','negative'] if a.stage is None else [a.stage]:
        if stage=='assemble':continue
        t=time.monotonic();result={'small':small_stage,'large':large_stage,'negative':negative_stage}[stage]()
        packet={'status':'PASS','stage':stage,'source_sha256':sources(),'seconds':round(time.monotonic()-t,3),'result':result}
        (ROOT/f'research/ANTIPODAL_STAGE_{stage}.json').write_text(json.dumps(serial(packet),indent=2,sort_keys=True)+'\n');print(stage,'PASS',packet['seconds'],flush=True)
    if a.stage is None or a.stage=='assemble':
        stages={s:json.loads((ROOT/f'research/ANTIPODAL_STAGE_{s}.json').read_text()) for s in ['small','large','negative']}
        require(all(s['status']=='PASS' and s['source_sha256']==sources() for s in stages.values()),'stale/failed stage')
        deps=['exact_farkas_lp.py','hpoly_segment_peeling.py','recognized_segment_routes.py','implicit_minkowski_lift.py','test_segment_peeling.py']
        out={'status':'PASS','scope':'Exact antipodal cover, complete extraction and original-H route checks, not Lean/platform verification or a polynomial pivot theorem.',
             'source_sha256':sources(),'dependency_sha256':{n:hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in deps},'stages':stages}
        out['route_certificates']=stages['small']['result']['counts']['route_certificates']+stages['large']['result']['route_certificates']+1
        out['route_edges']=stages['small']['result']['counts']['route_edges']+stages['large']['result']['ordinary_edges']+stages['negative']['result']['duplicate_constant_boundary_route']['actual_original_route_edges']
        (ROOT/'research/ANTIPODAL_DISCOVERY_CHECK_2026-09-13.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n');print('ASSEMBLED',out['route_certificates'],out['route_edges'],flush=True)
if __name__=='__main__':main()
