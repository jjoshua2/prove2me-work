#!/usr/bin/env python3
"""Exact original-H, whole-support and Fano-barrier regression.

Complete nestohedron graphs are enumerated ONLY in the small reference tests.
No reference graph is passed to the route constructor. The higher-rank binary
Steiner checks use the induced clutter; their huge full building sets are not
claimed enumerated. Python and these certificates are not Lean-extracted.
"""
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from collections import defaultdict,deque
from copy import deepcopy
from pathlib import Path
import argparse,hashlib,json,random,time
import endpoint_transfer_routes as route
import steiner_nestohedron_barrier as barrier
import stellar_defect_budget as stellar

ROOT=Path(__file__).resolve().parents[1]
require=route.require
SOURCES=['endpoint_transfer_routes.py','steiner_nestohedron_barrier.py',
         'test_endpoint_transfer_routes.py','stellar_defect_budget.py','simple_tangent_policy_audit.py']


def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(route.serial(data),indent=2,sort_keys=True)+'\n')


def hashes():
    return {f'scripts/{s}':hashlib.sha256((ROOT/'scripts'/s).read_bytes()).hexdigest() for s in SOURCES}


def intervals(n): return [list(range(i,j)) for i in range(n) for j in range(i+1,n+1)]


def power_building(n):
    return [list(S) for k in range(1,n+1) for S in combinations(range(n),k)]


def distances(G,s):
    D={s:0};q=deque([s])
    while q:
        x=q.popleft()
        for y in G[x]:
            if y not in D: D[y]=D[x]+1; q.append(y)
    require(len(D) == len(G), 'reference graph not connected')
    return D


def reference(n,B,w=None,brute=False):
    S,w=route.presentation(n,B,w); A,b,total,labels=route.building_H(n,B,w)
    # Exhaustive coordinate orders cover all vertices by the support theorem.
    # Reconstruct edges independently from ORIGINAL-H active ridges, not swaps.
    images={p:route.point(n,S,w,p)[0][:-1] for p in permutations(range(n))}
    vertices=sorted(set(images.values())); bases={}; ridges=defaultdict(list)
    for x in vertices:
        bs=route.original.basis_packet(A,b,x); route.original.audit_basis(A,b,bs); bases[x]=bs
        for r in combinations(bs['active'],n-2): ridges[r].append(x)
    require(all(len(v) == 2 for v in ridges.values()), 'original ridge did not have exactly two vertices')
    G={v:set() for v in vertices}
    for u,v in ridges.values(): G[u].add(v);G[v].add(u)
    # All adjacent-order contractions must agree with the independently built H graph.
    swap_edges=set()
    for p,x in images.items():
        for j in range(n-1):
            q=list(p);q[j],q[j+1]=q[j+1],q[j]; y=images[tuple(q)]
            if x!=y: swap_edges.add(tuple(sorted((x,y))))
    require(swap_edges == {tuple(sorted((u,v))) for u in G for v in G[u]}, 'braid and original ridge graphs differ')
    facet_checks=0
    for j,(row,rhs) in enumerate(zip(A,b)):
        vs=[x for x in vertices if route.original.dot(row,x) == rhs]
        require(vs, 'missing genuine facet')
        z=tuple(sum((x[i] for x in vs),Q(0))/len(vs) for i in range(n-1))
        require(route.original.active_rows(A,b,z) == [j] and route.original.feasible(A,b,z), 'bad genuine-facet witness')
        facet_checks+=1
    tested=0
    if brute:
        found=set()
        for I in combinations(range(len(A)),n-1):
            tested+=1
            try: inv=route.original.invert([A[i] for i in I])
            except ValueError: continue
            x=tuple(route.original.dot(r,[b[i] for i in I]) for r in inv)
            if route.original.feasible(A,b,x): found.add(x)
        require(found == set(vertices), 'independent exhaustive H-bases disagree')
    return A,b,vertices,G,{'vertices':len(vertices),'edges':sum(map(len,G.values()))//2,
        'enumerated_coordinate_orders':len(images),'genuine_facet_witnesses':facet_checks,
        'independent_square_H_systems':tested,'all_original_vertex_inverses_checked':True}


def support_stage():
    rng=random.Random(268); cases=edges=stationary=tuple_checks=0
    for case in range(90):
        n=rng.randrange(2,5) if case<20 else rng.randrange(2,9)
        candidates=[tuple(S) for k in range(1,n+1) for S in combinations(range(n),k)]
        S=rng.sample(candidates,min(len(candidates),4 if case<20 else rng.randrange(2,22)))
        w=[Q(rng.randrange(1,8),rng.randrange(1,6)) for _ in S]
        source=list(range(n));target=source[:];rng.shuffle(source);rng.shuffle(target)
        result=route.build(n,S,w,source,target); report=result['verified']
        cases+=1;edges+=report['original_edges'];stationary+=report['stationary_swaps']
        if n<=4 and len(S)<=5:
            # Independent full raw tuple set, not the producer's support decomposition.
            points=set()
            for choices in product(*S):
                p=[Q(0)]*n
                for i,t in zip(choices,w):p[i]+=t
                points.add(tuple(p))
            for step in result['certificate']['steps']:
                r=step['transfer'];c=list(map(Q,r['normal']));x=list(map(Q,r['from']));y=list(map(Q,r['to']))
                maximum=max(sum(a*b for a,b in zip(c,p)) for p in points)
                face=[p for p in points if sum(a*b for a,b in zip(c,p)) == maximum]
                u,v=r['pair'];mu=Q(r['mass'])
                require(tuple(x) in face and tuple(y) in face, 'wall endpoint not in raw sum')
                for p in face:
                    t=(p[v]-x[v])/mu
                    require(0<=t<=1 and all(p[i]==x[i]+t*(y[i]-x[i]) for i in range(n)), 'whole raw face is not the reported edge')
                    tuple_checks+=1
    # Exact zero case and duplicate representations of the same endpoint.
    z=route.build(4,intervals(4),None,[0,1,2,3],[0,1,2,3])
    require(z['verified']['original_edges']==0,'stationary endpoint')
    return {'random_positive_presentations':cases,'exposed_edges':edges,'stationary_swaps':stationary,
            'raw_support_tuple_checks':tuple_checks,'zero_endpoint_case':True}


def geometry_stage():
    n,H=barrier.steiner_triples(3); fano=barrier.upward_building(n,H)
    models=[('interval4',4,intervals(4),True),('permuta4',4,power_building(4),True),
            ('Fano',7,fano,False)]
    results=[];totals={'routes':0,'original_edges':0,'shortest_edges':0,'nonshortest':0,'common_facet_checks':0}
    for name,n,B,brute in models:
        begin=time.monotonic(); A,b,V,G,meta=reference(n,B,brute=brute)
        pairs=list(combinations(V,2)) if n<=4 else random.Random(268).sample(list(combinations(V,2)),80)
        S,w=route.presentation(n,B);sx=route.point(n,S,w,list(range(n)))[0][:-1];tx=route.point(n,S,w,list(reversed(range(n))))[0][:-1]
        if (sx,tx) not in pairs: pairs.append((sx,tx))
        sum_edges=sum_short=nonshort=shared=0;cache={}; selected=None
        for u,v in pairs:
            data={'n':n,'subsets':B,'A':A,'b':b,'start':u,'target':v}
            out=route.build_H(data);path=[tuple(map(Q,p[:-1])) for p in out['certificate']['route']['path']]
            require(all(y in G[x] for x,y in zip(path,path[1:])), 'reference original graph rejects route')
            if u not in cache: cache[u]=distances(G,u)
            shortest=cache[u][v];L=out['verified']['original_edges']
            require(shortest<=L,'claimed route shorter than reference distance')
            sum_edges+=L;sum_short+=shortest;nonshort+=L>shortest;shared+=out['verified']['common_original_facets_retained']
            if (u,v)==(sx,tx):
                selected={'input':data,**out,'independent_graph_distance':shortest}
        require(selected is not None,'missing selected pair')
        diameter=max(max(distances(G,u).values()) for u in V) if name=='Fano' else None
        results.append({'name':name,'dimension':n-1,'facets':len(A),**meta,'routes':len(pairs),
                        'route_edges':sum_edges,'shortest_sum':sum_short,'nonshortest_routes':nonshort,
                        'selected_edges':selected['verified']['original_edges'],
                        'selected_shortest':selected['independent_graph_distance'],
                        'all_pairs_reference_diameter':diameter,'seconds':round(time.monotonic()-begin,3)})
        totals['routes']+=len(pairs);totals['original_edges']+=sum_edges;totals['shortest_edges']+=sum_short
        totals['nonshortest']+=nonshort;totals['common_facet_checks']+=shared
        dump(ROOT/f'fixtures/endpoint_transfer_{name}.json',selected)
        print(name,results[-1],flush=True)
    return {'cases':results,'totals':totals}


def barrier_stage():
    n,H=barrier.steiner_triples(3); B=barrier.upward_building(n,H);K,labels=barrier.nested_complex(n,H,B)
    rng=random.Random(269);comparisons=0
    for S in [set(T) for k in range(8) for T in combinations(range(n),k)]+[set(rng.sample(range(K.n),rng.randrange(0,9))) for _ in range(700)]:
        require(K.face(S)==barrier.nested_test(labels,B,S),'higher catalogue disagrees with nested definition');comparisons+=1
    first=[]
    for E in combinations(range(n),2):
        J,record=barrier.first_original_pair_bound(K,n,H,E)
        require(J.weight()==10,'first original pair did not give exact Fano barrier');first.append(record)
    end,completion=barrier.fano_completion(K)
    # Preserve the source complex and replay the supplied word with exact #262 accounting.
    replay=K
    for proof in completion['steps']:
        replay,actual=stellar.account(replay,proof['edge']);require(actual==proof,'forged completion word')
    require(replay==end,'replay state mismatch')
    auxiliary=0
    for _ in range(6):
        current=K
        for _ in range(2):
            candidates=[E for E in combinations(range(current.n),2) if max(E)>=n and current.face(E)]
            current,_=stellar.account(current,list(rng.choice(candidates)))
        for E in combinations(range(n),2):
            barrier.first_original_pair_bound(current,n,H,E);auxiliary+=1
    family=[]
    for rank in [3,4,5,6]:
        size,triples=barrier.steiner_triples(rank);abstract=stellar.Complex.create(size,triples)
        for E in [(0,1),(0,size-1),(size-2,size-1)]:
            J,r=barrier.first_original_pair_bound(abstract,size,triples,E)
            require(J.weight()==len(triples)+size-4,'binary family first-pair count')
        family.append({'ground_size':size,'triple_roots':len(triples),'required_peak_at_least':len(triples)+size-4,
                       'compulsory_energy_increase':size-4,'full_nestohedron_enumerated':size==7})
    result={'ground_size':n,'dimension':n-1,'genuine_nestohedron_facets':K.n,
            'higher_nonfaces':len(H),'minimal_nonfaces_including_pairs':len(K.missing),
            'nested_definition_checks':comparisons,'all_original_pair_tests':len(first),
            'auxiliary_prefix_first_pair_tests':auxiliary,'completion':completion,
            'binary_Steiner_controls':family,'edge_stellar_only':True,'diameter_lower_bound_claimed':False}
    dump(ROOT/'fixtures/fano_positive_barrier.json',{'building_set':B,'initial_complex':K.payload(),
         'first_pair_records':first,'completion':completion,'terminal_complex':end.payload()})
    return result


def shortcut(n):
    total=Q(n*(n+1),2);path=[]
    for k in range(n):
        pivot=n-1-k
        x=[Q(i+1) for i in range(pivot)]+[Q((k+1)*(n-k))]+[Q(i) for i in range(k,0,-1)]
        require(sum(x)==total,'shortcut mass');path.append(tuple(x))
    return path


def large_stage():
    results=[]
    for n in [8,12,16]:
        B=intervals(n);A,b,total,_=route.building_H(n,B)
        path=shortcut(n);data={'n':n,'subsets':B,'A':A,'b':b,'start':path[0][:-1],'target':path[-1][:-1]}
        out=route.build_H(data);L=out['verified']['original_edges']
        require(L==n*(n-1)//2,'endpoint-only interval worst case changed')
        intrinsic=[x[:-1] for x in path];packets=[route.original.basis_packet(A,b,x) for x in intrinsic]
        route.original_audit(A,b,intrinsic,packets)
        require(not(set(packets[0]['active']) & set(packets[-1]['active'])),'source/target lower bound lost')
        results.append({'ground_size':n,'dimension':n-1,'genuine_original_facets':len(A),
                        'endpoint_transfer_edges':L,'independent_explicit_shortest_edges':n-1,
                        'full_graph_enumerated':False,'comparison_source_facet_lower_bound':n-1})
        if n==16: dump(ROOT/'fixtures/endpoint_transfer_interval16.json',{'input':data,**out,
                    'shortest_comparison':{'path':intrinsic,'bases':packets,'edges':n-1}})
        print('large',results[-1],flush=True)
    return {'cases':results,'known_asymptotic_shortening_not_claimed_as_new':True}


def negative_stage():
    B=intervals(4);A,b,total,_=route.building_H(4,B);S,w=route.presentation(4,B)
    x=route.point(4,S,w,[0,1,2,3])[0][:-1];y=route.point(4,S,w,[3,2,1,0])[0][:-1]
    data={'n':4,'subsets':B,'A':A,'b':b,'start':x,'target':y};out=route.build_H(data);c=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted invalid '+name)
    edits=[('missing_edge',lambda z:z['route']['steps'].pop()),
           ('fake_mass',lambda z:z['route']['steps'][0]['transfer'].update(mass='999')),
           ('false_wall',lambda z:z['route']['steps'][0]['transfer']['normal'].__setitem__(0,'-99')),
           ('omitted_summand',lambda z:z['route']['steps'][0]['transfer']['summands'].pop()),
           ('float_wall_position',lambda z:z['route']['steps'][0].update(position=1.0)),
           ('false_stationary',lambda z:z['route'].update(stationary_swaps=999)),
           ('wrong_endpoint_order',lambda z:z['route'].update(target_order=[0,1,2,3])),
           ('false_original_inverse',lambda z:z['bases'][0]['directions'][0].__setitem__(0,'999')),
           ('omitted_original_basis',lambda z:z['bases'].pop()),
           ('diagonal_path',lambda z:z['route'].update(path=[z['route']['path'][0],z['route']['path'][-1]]))]
    for name,edit in edits:
        z=deepcopy(c);edit(z);reject(name,lambda z=z:route.verify_H(data,z))
    changed=deepcopy(data);changed['b']=list(changed['b']);changed['b'][0]+=1
    reject('changed_H',lambda:route.verify_H(changed,c))
    reject('negative_weight',lambda:route.build(3,[[0,1],[1,2]],[-1,1],[0,1,2],[2,1,0]))
    reject('float_weight',lambda:route.build(3,[[0,1],[1,2]],[0.5,1],[0,1,2],[2,1,0]))
    reject('invalid_building_set',lambda:route.building_H(4,[[0],[1],[2],[3],[0,1],[1,2],[0,1,2,3]]))
    reject('upward_enumeration_cap',lambda:barrier.upward_building(7,barrier.steiner_triples(3)[1],10))
    K=stellar.Complex.create(7,barrier.steiner_triples(3)[1]);J,_=stellar.account(K,[0,1])
    reject('not_first_original_pair',lambda:barrier.first_original_pair_bound(J,7,barrier.steiner_triples(3)[1],(0,2)))
    inv=route.original.invert; producer=route.original.basis_packet
    def forbidden(*a,**k):raise AssertionError('geometric discovery inside verification')
    route.original.invert=forbidden;route.original.basis_packet=forbidden
    try:require(route.verify_H(data,json.loads(json.dumps(c)))==out['verified'],'discovery-disabled JSON audit differs')
    finally:route.original.invert=inv;route.original.basis_packet=producer
    return {'rejected':len(names),'names':names,'original_inverse_and_basis_production_disabled':True,
            'exact_serialized_packet_replayed':True}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['support','geometry','barrier','large','negative','assemble']);a=p.parse_args()
    stages=['support','geometry','barrier','large','negative']
    for stage in stages if a.stage is None else [a.stage]:
        if stage=='assemble':continue
        begin=time.monotonic();result=globals()[stage+'_stage']()
        dump(ROOT/f'research/ENDPOINT_TRANSFER_STAGE_{stage}.json',{'status':'PASS','source_sha256':hashes(),
             'result':result,'seconds':round(time.monotonic()-begin,3)})
        print(stage,'PASS',flush=True)
    if a.stage is None or a.stage=='assemble':
        data={s:json.loads((ROOT/f'research/ENDPOINT_TRANSFER_STAGE_{s}.json').read_text()) for s in stages}
        require(all(d['status']=='PASS' and d['source_sha256']==hashes() for d in data.values()),'stale or failed test stage')
        dump(ROOT/'research/ENDPOINT_TRANSFER_CHECK.json',{'status':'PASS','source_sha256':hashes(),'stages':data,
             'scope':'Written mathematics and exact code, not Lean/Prove2Me. Models supplied; no arbitrary-H recognition.'})
if __name__=='__main__':main()
