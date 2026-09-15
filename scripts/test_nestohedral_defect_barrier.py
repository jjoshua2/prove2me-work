#!/usr/bin/env python3
"""Independent exact realization, first-pair barriers and peak-optimal escape.

Full geometry is constructed only for the seven-point/Fano case. Larger binary
design cases check finite incidence certificates, NOT exponentially large
nestohedron graphs. Classical building-set geometry and written arguments are
not replaced by finite test claims or a new Lean/platform verdict.
"""
from __future__ import annotations
from itertools import combinations, permutations
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from copy import deepcopy
import hashlib,json,random,time,argparse
import nestohedral_defect_barrier as N
S,H=N.S,N.H
ROOT=Path(__file__).resolve().parents[1]
DEPS={'stellar_defect_budget.py':'b51e2c3edec2c85026344566978561eb430050ec',
      'simple_tangent_policy_audit.py':'73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976'}


def source_hashes():
    return {f'scripts/{f}':hashlib.sha256((ROOT/'scripts'/f).read_bytes()).hexdigest()
            for f in ['nestohedral_defect_barrier.py','test_nestohedral_defect_barrier.py']+list(DEPS)}


def dump(path,obj):
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(H.serial(obj),indent=2,sort_keys=True)+'\n')


def relative_barycentric(K,model):
    """Literal face stellar subdivisions, independent of the Minkowski coordinates.
    These are the INPUT's polytopality construction, not counted escape moves.
    """
    facets=[frozenset(set(range(K.n))-{i}) for i in range(K.n)]
    operations=[]
    for j,T in sorted(enumerate(model['facet_labels']),key=lambda z:(-len(z[1]),z[1])):
        if len(T)==1:continue
        E=frozenset(T)
        S.require(any(E<=F for F in facets),'relative stellar face missing')
        facets=S.ordered([U for F in facets for U in
            ([F] if not E<=F else [(F-{v})|{j} for v in E])])
        operations.append({'face':sorted(E),'new_label':j})
    return facets,operations


def graph(facets,d):
    buckets={};G={F:set() for F in facets}
    for F in facets:
        S.require(len(F)==d,'impure simplicial boundary')
        for i in F:buckets.setdefault(F-{i},[]).append(F)
    for L in buckets.values():
        S.require(len(L)==2,'ridge not incident to exactly two facets')
        u,v=L;G[u].add(v);G[v].add(u)
    return G


def shortest(G,u,v=None,locked=frozenset()):
    D={u:0};parent={u:None};Q=deque([u])
    while Q:
        F=Q.popleft()
        if F==v:break
        for T in sorted(G[F],key=lambda z:tuple(sorted(z))):
            if T not in D and locked<=T:D[T]=D[F]+1;parent[T]=F;Q.append(T)
    if v is None:return D
    S.require(v in D,'reference route disconnected');P=[]
    while v is not None:P.append(v);v=parent[v]
    return P[::-1]


def maximal_cliques(G):
    """Direct graph clique enumeration, not the stellar nonface update."""
    out=[]
    def visit(R,P,X):
        if not P and not X:out.append(frozenset(R));return
        u=max(P|X,key=lambda v:len(P&G[v]))
        for v in sorted(P-G[u]):
            visit(R|{v},P&G[v],X&G[v]);P.remove(v);X.add(v)
    visit(set(),set(G),set());return S.ordered(out)


def catalogue_facets(K):
    pairs={M for M in K.missing if len(M)==2}
    G={i:{j for j in range(K.n) if i!=j and frozenset([i,j]) not in pairs} for i in range(K.n)}
    final=set();visited=set()
    def split(F):
        if F in visited:return
        visited.add(F)
        M=next((M for M in K.higher() if M<=F),None)
        if M is None:final.add(F);return
        for v in M:split(F-{v})
    for F in maximal_cliques(G):split(F)
    ordered=sorted(final,key=lambda F:(-len(F),tuple(sorted(F))));out=[]
    for F in ordered:
        if not any(F<=T for T in out):out.append(F)
    return set(out)


def algebra_stage():
    rng=random.Random(265);models=[]
    for n in (3,4):
        triples=list(combinations(range(n),3))
        for mask in range(1,1<<len(triples)):
            models.append(S.Complex.create(n,[T for i,T in enumerate(triples) if mask>>i&1]))
    for n in (4,5):
        universe=[frozenset(T) for k in range(2,n+1) for T in combinations(range(n),k)]
        for _ in range(16):models.append(S.Complex.create(n,S.lists(S.minimal(rng.sample(universe,rng.randrange(1,8))))))
    counts={'complexes':len(models),'relative_face_subdivisions':0,'generic_orders':0,'distinct_vertices':0,
            'exact_original_inequality_checks':0,'nested_facet_comparisons':0}
    for K in models:
        P=N.realize(K);literal,ops=relative_barycentric(K,P);V=N.ordered_vertices(P)
        observed=set()
        for x,order in V.items():
            slacks=[b-sum(a*y for a,y in zip(row,x)) for row,b in zip(P['A'],P['b'])]
            S.require(min(slacks)>=0,'Minkowski vertex outside original H-set')
            F=frozenset(i for i,s in enumerate(slacks) if s==0)
            S.require(F==N.expected_facet(P,order),'nested prefix mismatch')
            observed.add(F);counts['exact_original_inequality_checks']+=len(slacks)
        S.require(observed==set(literal),'literal relative subdivision and complete H-vertex table differ')
        counts['relative_face_subdivisions']+=len(ops);counts['generic_orders']+=__import__('math').factorial(K.n)
        counts['distinct_vertices']+=len(V);counts['nested_facet_comparisons']+=len(V)
    # Adversarial arbitrary auxiliary subdivisions before the first old pair.
    seed=N.steiner_binary(3);trials=0;increases=0
    for _ in range(32):
        K=S.Complex.create(9,S.lists(seed.missing))
        for step in range(rng.randrange(1,6)):
            edges=[E for E in combinations(range(K.n),2) if max(E)>=7 and K.face(E)]
            K,p=S.account(K,rng.choice(edges));increases+=p['weight_after']>p['weight_before']
            S.require([M for M in K.missing if max(M)<7]==seed.missing or
                      tuple(M for M in K.missing if max(M)<7)==seed.missing,'original induced complex changed')
        for E in rng.sample(list(combinations(range(7),2)),3):
            J,p=S.account(K,E)
            S.require(J.weight()>=10,'auxiliary prefix defeated first-pair barrier')
            original=set(range(7));new=p['new_label']
            forced={frozenset({new})|(M-set(E)) for M in seed.missing if len(M&set(E))==1}
            S.require(forced<=set(J.missing),'a mandatory descendant disappeared')
            trials+=1
    counts.update(auxiliary_prefix_first_pair_checks=trials,weight_increasing_auxiliary_prefix_steps=increases)
    return counts


def family_stage():
    cases=[]
    for r in (3,4,5):
        K=N.steiner_binary(r);c=N.barrier_certificate(K);v=N.verify_barrier(K,c)
        # Independent XOR/pair check is finite even when the realization is huge.
        row={'binary_rank':r,'ground_labels':K.n,'polytope_dimension_formula':K.n-1,
             'higher_triples':len(K.missing),**v,'full_polytope_geometry_constructed':r==3}
        if r<=4:
            faces=sum(K.face([i for i in range(K.n) if mask>>i&1]) for mask in range(2**K.n))
            row['exact_original_facet_count']=K.n+(2**K.n-faces)-1
            row['ground_subset_membership_checks']=2**K.n
        cases.append(row)
    return cases


def geometry_stage():
    t0=time.monotonic();K=N.steiner_binary(3);P=N.realize(K);A,b=P['A'],P['b'];d=6
    literal,construction=relative_barycentric(K,P);orders=N.ordered_vertices(P)
    points={};facets=[];perms={};basis={};slack_checks=0
    for x,order in orders.items():
        slacks=[z-sum(a*v for a,v in zip(row,x)) for row,z in zip(A,b)]
        S.require(min(slacks)>=0,'vertex infeasible');F=frozenset(i for i,z in enumerate(slacks) if z==0)
        S.require(len(F)==d and F==N.expected_facet(P,order),'nonsimple or wrong exact active basis')
        S.require(F not in points,'different points share one active basis')
        points[F]=x;perms[F]=order;facets.append(F);slack_checks+=len(A)
        basis[x]=H.basis_packet(A,b,x)
    S.require(set(facets)==set(literal),'relative subdivision does not match full geometry')
    dual=S.Complex.create(P['dual']['vertices'],P['dual']['minimal_nonfaces'])
    S.require(catalogue_facets(dual)==set(facets),'incomplete original nonface catalogue')
    for M in dual.missing:
        S.require(not any(M<=F for F in facets) and all(any(M-{i}<=F for F in facets) for i in M),
                  'listed nonface not minimal in original geometric boundary')
    # Equality of complete facet lists proves no omitted nonfaces; every listed
    # candidate is additionally checked directly at all geometric vertices.
    anchors=[]
    for row in range(len(A)):
        xs=[x for F,x in points.items() if row in F]
        a=[sum(Q(x[j]) for x in xs)/len(xs) for j in range(d)]
        S.require(H.feasible(A,b,a) and H.active_rows(A,b,a)==[row],'nongenuine original facet')
        anchors.append(a)
    center=[sum(Q(x[j]) for x in points.values())/len(points) for j in range(d)]
    S.require(all(H.dot(a,center)<z for a,z in zip(A,b)),'no strict original interior')
    refinement=N.fano_refinement(dual);fine=facets;stages=[set(facets)]
    for p in refinement['steps']:
        fine=S.subdivide_facets(fine,p['edge'],p['new_label']);stages.append(set(fine))
    final=S.Complex.create(refinement['terminal']['vertices'],refinement['terminal']['minimal_nonfaces'])
    missing=set(final.missing);compat={i:{j for j in range(final.n) if i!=j and frozenset([i,j]) not in missing}
                                      for i in range(final.n)}
    S.require(set(maximal_cliques(compat))==set(fine),'terminal literal complex is not flag')
    G=graph(facets,d);GG=graph(fine,d)
    # Audit EVERY refined adjacency through EVERY earlier subdivision.
    original_fine=fine[:];edge_ids=[(i,j) for i,F in enumerate(fine) for j,T in enumerate(fine)
                                  if i<j and T in GG[F]]
    transported=fine[:];carrier_checks=0
    for level in reversed(range(len(refinement['steps']))):
        p=refinement['steps'][level];E=frozenset(p['edge']);z=p['new_label']
        transported=[(F-{z})|E if z in F else F for F in transported]
        S.require(set(transported)<=stages[level],'carrier not an earlier maximal simplex')
        S.require(all(transported[i]==transported[j] or len(transported[i]&transported[j])==d-1
                      for i,j in edge_ids),'carrier maps a refined edge to a chord')
        carrier_checks+=len(edge_ids)
    diameter=0;ordered_distances=0
    for F in facets:
        D=shortest(G,F);S.require(len(D)==len(facets),'original graph disconnected')
        diameter=max(diameter,max(D.values()));ordered_distances+=len(D)
    rng=random.Random(265);pairs=rng.sample(list(combinations(facets,2)),32)
    results=[];counts={'routes':0,'refined_edges':0,'transported_original_edges':0,'sorting_edges':0,
                     'shortest_edges':0,'transported_nonshortest':0,'sorting_nonshortest':0,'stationary_carriers':0}
    # Stage replay is already verified above; route transport now uses those
    # exact finite facets rather than rerunning the expensive residue compiler.
    for F,T in pairs:
        X,Y=S.lift_pair(F,T,refinement['steps']);fp=shortest(GG,X,Y,X&Y);p=fp[:]
        for s in reversed(refinement['steps']):
            E=frozenset(s['edge']);z=s['new_label'];p=[(Qq-{z})|E if z in Qq else Qq for Qq in p]
        route=[p[0]]
        for Z in p[1:]:
            if Z!=route[-1]:route.append(Z)
        S.require(route[0]==F and route[-1]==T and all(F&T<=Z for Z in route),'wrong endpoints/common face')
        for U,V in zip(route,route[1:]):N.audit_original_edge(A,b,basis[points[U]],basis[points[V]])
        direct=N.sorting_route(P,perms[F],perms[T]);N.audit_sorting(P,direct,basis)
        optimal=len(shortest(G,F,T))-1
        counts['routes']+=1;counts['refined_edges']+=len(fp)-1
        counts['transported_original_edges']+=len(route)-1;counts['sorting_edges']+=len(direct['path'])-1
        counts['shortest_edges']+=optimal;counts['transported_nonshortest']+=len(route)-1>optimal
        counts['sorting_nonshortest']+=len(direct['path'])-1>optimal
        counts['stationary_carriers']+=len(fp)-len(route)
        S.require(len(fp)-1<=final.n-d and len(direct['path'])-1<=21,'structural bound violation')
        if len(results)<2:
            results.append({'start':points[F],'target':points[T],'ordered_refined_path':[sorted(Z) for Z in fp],
                            'original_path':[sorted(Z) for Z in route],'sorting':direct,'BFS_distance':optimal})
    # One original carrier replay uses the unchanged full accounting routine.
    sample=results[0];coarse=S.transport(dual,refinement['steps'],sample['ordered_refined_path'],d)
    S.require([sorted(Z) for Z in coarse]==sample['original_path'],'unchanged carrier auditor disagreement')
    saved=H.invert
    def forbidden(*a,**kw):raise AssertionError('route audit invoked inverse discovery')
    H.invert=forbidden
    try:
        for r in results:
            N.audit_sorting(P,r['sorting'],basis)
            for F,T in zip(r['original_path'],r['original_path'][1:]):
                N.audit_original_edge(A,b,basis[points[frozenset(F)]],basis[points[frozenset(T)]])
    finally:H.invert=saved
    result={'dimension':d,'original_facets':len(A),'coordinate_simplices':len(P['building_set']),
            'input_realizing_face_subdivisions':len(construction),'all_objective_orders':5040,
            'original_vertices':len(facets),'original_graph_edges':sum(map(len,G.values()))//2,
            'original_vertex_slack_checks':slack_checks,'genuine_facet_anchors':len(anchors),
            'original_missing_pairs':len(dual.missing)-len(dual.higher()),'original_higher_triples':len(dual.higher()),
            'minimum_energy_peak':10,'minimum_peak_excess':3,'escape_steps':len(refinement['steps']),
            'escape_weights':refinement['weights'],'refined_vertices':final.n,'refined_facets':len(fine),
            'refined_graph_edges':sum(map(len,GG.values()))//2,'complete_carrier_adjacency_checks':carrier_checks,
            'entire_original_graph_diameter':diameter,'all_ordered_distances_computed':ordered_distances,
            'all_pair_sorting_upper_bound':21,'flag_refinement_upper_bound':final.n-d,
            'route_counts':counts,'saved_audits_with_inverse_disabled':len(results)*2,
            'seconds':round(time.monotonic()-t0,3),
            'scope':'Full ORIGINAL and refined graphs explicitly enumerated for this one six-dimensional case.'}
    dump(ROOT/'fixtures/fano_nestohedron_input.json',{'A':A,'b':b,'dimension':d,
        'genuine_facets':len(A),'ground_kernel':K.payload(),
        'construction':'Singletons plus every nonface as building set; eliminate last coordinate.',
        'source':list(next(iter(orders))),'target':list(N.greedy(P,list(reversed(range(K.n)))))})
    dump(ROOT/'fixtures/fano_nestohedron_energy_barrier.json',{'model':P,'barrier':N.barrier_certificate(K),
        'refinement':refinement,'genuine_facet_points':anchors,'strict_interior_point':center,
        'route_examples':results,'route_vertex_bases':[basis[x] for x in sorted(
            {tuple(x) for r in results for x in r['sorting']['path']} |
            {points[frozenset(F)] for r in results for F in r['original_path']})],
        'summary':{k:v for k,v in result.items() if k!='seconds'}})
    result['standalone_saved_audit']=N.audit_saved(json.loads((ROOT/'fixtures/fano_nestohedron_energy_barrier.json').read_text()))
    return result


def negative_stage():
    K=N.steiner_binary(3);bar=N.barrier_certificate(K);P=N.realize(K)
    dual=S.Complex.create(P['dual']['vertices'],P['dual']['minimal_nonfaces']);c=N.fano_refinement(dual);names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('invalid certificate accepted: '+name)
    for field,value in [('required_peak',9),('required_excess',0),('input_sha256','bad')]:
        x=deepcopy(bar);x[field]=value;reject(field,lambda x=x:N.verify_barrier(K,x))
    x=deepcopy(bar);x['first_edge_cases'].pop();reject('omitted_first_pair',lambda:N.verify_barrier(K,x))
    x=deepcopy(bar);x['first_edge_cases'][0]['forced_residues'].pop();reject('omitted_forced_birth',lambda:N.verify_barrier(K,x))
    reject('incomplete_triple_design',lambda:N.barrier_certificate(S.Complex.create(7,S.lists(K.missing[:-1]))))
    reject('realization_subset_cap',lambda:N.realize(K,16))
    reject('full_simplex_not_connected_building_set',lambda:N.realize(S.Complex.create(3,[])))
    for field,value in [('peak',9),('weights',[7,0]),('input_sha256','bad')]:
        x=deepcopy(c);x[field]=value;reject('trace_'+field,lambda x=x:N.verify_refinement(dual,x))
    x=deepcopy(c);x['steps'].pop();reject('incomplete_flag_trace',lambda:N.verify_refinement(dual,x))
    x=deepcopy(c);x['steps'][0]['created_higher_weight']=0;reject('unaccounted_births',lambda:N.verify_refinement(dual,x))
    reject('invalid_order',lambda:N.greedy(P,[0,1,2,3,4,5,5]))
    reject('float_labels',lambda:S.Complex.create(3,[[0,1,2.0]]))
    reject('bool_order',lambda:N.greedy(P,[False,1,2,3,4,5,6]))
    reject('facet_pair_cap',lambda:N.realize(K,facet_pair_cap=10))
    path=ROOT/'fixtures/fano_nestohedron_energy_barrier.json'
    require_fixture=path.exists();S.require(require_fixture,'run geometry before negative saved-packet checks')
    fixture=json.loads(path.read_text())
    for tag,edit in [('changed_original_H',lambda z:z['model']['b'].__setitem__(0,999)),
                     ('false_facet_witness',lambda z:z['genuine_facet_points'].__setitem__(0,[0]*6)),
                     ('omitted_saved_basis',lambda z:z['route_vertex_bases'].pop()),
                     ('false_carrier_vertex',lambda z:z['route_examples'][0]['original_path'][0].pop()),
                     ('false_original_inverse',lambda z:z['route_vertex_bases'][0]['directions'][0].__setitem__(0,'999'))]:
        z=deepcopy(fixture);edit(z);reject(tag,lambda z=z:N.audit_saved(z))
    saved=[(H,'invert'),(N,'ordered_vertices')];old=[]
    def forbidden(*a,**kw):raise AssertionError('saved replay invoked discovery')
    try:
        for module,name in saved:old.append((module,name,getattr(module,name)));setattr(module,name,forbidden)
        audited=N.audit_saved(fixture)
    finally:
        for module,name,fn in old:setattr(module,name,fn)
    return {'rejected':len(names),'names':names,'saved_replay_with_discovery_disabled':audited}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['algebra','family','geometry','negative','assemble']);args=p.parse_args()
    for file,sha in DEPS.items():
        raw=(ROOT/'scripts'/file).read_bytes()
        S.require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==sha,'changed frozen dependency')
    for stage in ['algebra','family','geometry','negative'] if args.stage is None else [args.stage]:
        if stage=='assemble':continue
        t=time.monotonic();r=globals()[stage+'_stage']()
        dump(ROOT/f'research/NESTO_BARRIER_STAGE_{stage}.json',{'status':'PASS','source_sha256':source_hashes(),
             'result':r,'seconds':round(time.monotonic()-t,3)})
        print(stage, 'PASS', r if stage!='geometry' else r['route_counts'],flush=True)
    if args.stage is None or args.stage=='assemble':
        stages={s:json.loads((ROOT/f'research/NESTO_BARRIER_STAGE_{s}.json').read_text()) for s in ['algebra','family','geometry','negative']}
        S.require(all(x['source_sha256']==source_hashes() for x in stages.values()),'stale stage')
        out={'status':'PASS','source_sha256':source_hashes(),'stages':stages,
             'no_new_Lean_or_platform_verdict':True,
             'scope':'Unavoidable uphill refinement weight, not a diameter obstruction; general written proof and finite exact evidence kept distinct.'}
        dump(ROOT/'research/NESTOHEDRAL_BARRIER_CHECK.json',out);print('ASSEMBLED',flush=True)
if __name__=='__main__':main()
