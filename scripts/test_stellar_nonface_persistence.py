#!/usr/bin/env python3
"""Independent literal subdivision, moment certificates, and original routes.
All tests are exact. Large face counts use the written all-k construction;
large graphs and exponentially long subdivision sequences are NOT enumerated.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from collections import deque
from pathlib import Path
from copy import deepcopy
from math import comb
import hashlib,json,random,time
import stellar_nonface_persistence as S
import graphical_flag_refinement as G

ROOT=Path(__file__).resolve().parents[1]


def subsets(n):
    return [frozenset(T) for r in range(n+1) for T in combinations(range(n),r)]


def literal_faces(K):return {T for T in subsets(K.n) if K.ask(T)}


def literal_subdivide(faces,E,z):
    # Operate on maximal simplices, not the minimal-nonface formula under test.
    maximal=[F for F in faces if not any(F<T for T in faces)]
    result=set()
    for F in maximal:
        pieces=[(F-{e})|{z} for e in E] if E<=F else [F]
        for P in pieces:
            for n in range(len(P)+1):
                result.update(frozenset(A) for A in combinations(P,n))
    return result


def min_nonfaces(faces,n):
    return S.base.ordered(T for T in subsets(n) if T not in faces
                         and all(T-{i} in faces for i in T))


def all_four_complexes():
    cand=[T for T in subsets(4) if len(T)>=2]
    for mask in range(1<<len(cand)):
        N=[T for j,T in enumerate(cand) if mask>>j&1]
        if S.base.minimal(N)==S.base.ordered(N):yield S.base.Complex(4,N)


def abstract_tests():
    counts={'complexes':0,'literal_stellar_checks':0,'nonedge_face_checks':0,
            'minimal_descendants_checked':0,'graphical_pairs':0,'passing_graphical_pairs':0,
            'random_sequences':0,'random_subdivision_steps':0,'completed_flag_sequences':0}
    packets=[]
    for K in all_four_complexes():
        counts['complexes']+=1;F=literal_faces(K)
        for E in sorted(F,key=lambda T:(len(T),sorted(T))):
            if len(E)<2:continue
            J=S.stellar_face(K,E);S.audit_step(K,E,J)
            exact=literal_subdivide(F,E,K.n)
            S.require(J.missing==min_nonfaces(exact,J.n),'formula disagrees with literal faces')
            S.require(literal_faces(J)==exact,'full stellar face table differs')
            counts['literal_stellar_checks']+=1;counts['nonedge_face_checks']+=len(E)>2
            counts['minimal_descendants_checked']+=len(K.missing)
        for mask in range(64):
            edges=[list(E) for j,E in enumerate(combinations(range(4),2)) if mask>>j&1]
            counts['graphical_pairs']+=1
            if not G.check_criterion(K,G.graph(4,edges)):
                R=G.GraphicalRefinement(K,edges);M=len(R.vertices)
                S.require(M>=S.lower_bound_vertices(K.n,len(K.missing)),
                          'graphical full-refinement count violates ancestry bound')
                counts['passing_graphical_pairs']+=1
    # Longer sequences can contain neutral/increasing higher-defect weights.
    rng=random.Random(267)
    initial=list(all_four_complexes())
    for i in range(160):
        K=initial[rng.randrange(len(initial))];original=K;steps=[]
        for _ in range(6):
            eligible=[E for E in subsets(K.n) if 2<=len(E)<=4 and K.ask(E)]
            if not eligible:break
            E=rng.choice(eligible);steps.append(sorted(E));K=S.stellar_face(K,E)
        report=S.ancestry(original,steps)
        packet={'format':'stellar-nonface-ancestry-v1','n':original.n,
                'minimal_nonfaces':[sorted(N) for N in original.missing],
                'subdivide_faces':steps,'report':report}
        S.verify_ancestry(json.loads(json.dumps(packet)))
        counts['random_sequences']+=1;counts['random_subdivision_steps']+=len(steps)
        counts['completed_flag_sequences']+=report['flag']
        if i<4:packets.append(packet)
    # Complete simplex schedules and an explicit product, not alleged random polytopes.
    for n in (4,5,8,12):
        K=S.base.Complex(n,[list(range(n))]);steps=[];work=K
        while work.high():
            E=sorted(work.high()[0])[:2];steps.append(E);work=S.stellar_face(work,E)
        rep=S.ancestry(K,steps);S.require(rep['flag'],'simplex schedule not flag')
        packets.append({'format':'stellar-nonface-ancestry-v1','n':n,
            'minimal_nonfaces':[list(range(n))],'subdivide_faces':steps,'report':rep})
    return counts,packets


def moment_tests():
    report=[];samples=[];proper_total=nonface_total=0
    for k in (2,3,4,5):
        A=S.moment_rows(k);U=list(range(1,4*k,2))
        supports=[S.support_certificate(k,T) for T in combinations(U,k)]
        nonfaces=[S.nonface_certificate(k,N) for N in combinations(U,k+1)]
        for c in supports:S.verify_support(c,A)
        for c in nonfaces:S.verify_nonface(c,A)
        # Every listed minimal nonface has ALL immediate proper subsets in the
        # independently exposed face table, so none is merely a nonminimal nonface.
        allowed={tuple(c['labels']) for c in supports}
        for c in nonfaces:
            N=c['nonface'];S.require(all(tuple(x for x in N if x!=i) in allowed for i in N),
                                    'missing proper-face support witness')
        # All original facets genuine: each moment label is strictly exposed
        # by (t-i)^2; the full augmented moment matrix has Vandermonde rank.
        for i in range(4*k+1):S.verify_support(S.support_certificate(k,[i]),A)
        row={'k':k,'dimension':2*k,'original_facets':4*k+1,
             'proper_face_witnesses':len(supports),'minimal_nonface_witnesses':len(nonfaces),
             'all_original_rows_exposed':4*k+1,'original_H_relations_checked':True}
        report.append(row);proper_total+=len(supports);nonface_total+=len(nonfaces)
        samples.append({'k':k,'support':supports[0],'nonface':nonfaces[0]})
    large=[]
    for k in (8,16,32):
        A=S.moment_rows(k);U=list(range(1,4*k,2));rng=random.Random(k)
        for j in range(3):
            N=sorted(rng.sample(U,k+1));nc=S.nonface_certificate(k,N)
            S.verify_nonface(nc,A)
            pc=S.support_certificate(k,N[:-1]);S.verify_support(pc,A)
            samples.append({'k':k,'support':pc,'nonface':nc})
        large.append({**S.family_bound(k),'nonfaces_individually_checked':3,
                      'proper_supports_individually_checked':3,
                      'whole_exponential_catalogue_enumerated':False})
    return {'full_small':report,'small_nonfaces':nonface_total,'small_proper_faces':proper_total,
            'large_sampled':large,'numeric_lower_bounds':[S.family_bound(k) for k in (2,4,8,16,32,64)]},samples


def all_moment_facets(k):
    # Independent finite reference: check every degree-d root polynomial over
    # every original label, not a proposed domino structure or route.
    m=4*k+1;d=2*k;facets=[];examined=0
    for F in combinations(range(m),d):
        p=S.polynomial(F);values=[S.evaluate(p,t) for t in range(m)];examined+=1
        if all(v>=0 for v in values) or all(v<=0 for v in values):facets.append(frozenset(F))
    adj={F:[] for F in facets}
    for F,H in combinations(facets,2):
        if len(F&H)==d-1:adj[F].append(H);adj[H].append(F)
    S.require(all(len(x)==d for x in adj.values()),'reference graph is not simple d-regular')
    return facets,adj,examined


def distances(adj,F):
    q=deque([F]);D={F:0}
    while q:
        N=q.popleft()
        for T in adj[N]:
            if T not in D:D[T]=D[N]+1;q.append(T)
    S.require(len(D)==len(adj),'disconnected reference graph')
    return D


def route_tests():
    reports=[];saved=[]
    for k in (2,3):
        fs,adj,systems=all_moment_facets(k);diam=0;dist={}
        for F in fs:dist[F]=distances(adj,F);diam=max(diam,max(dist[F].values()))
        S.require(diam==2*k,'published cyclic diameter comparison failed on small graph')
        pairs=list(combinations(fs,2))
        if k==3:random.Random(267).shuffle(pairs);pairs=pairs[:120]
        edges=shortest=nonshort=0
        A=S.moment_rows(k);points={}
        for F in fs:
            c=S.facet_certificate(k,F);x=list(map(Q,c['point']))
            # Original matrices evaluated here independently of the polynomial
            # identity used to verify the larger examples.
            vals=[sum(a*b for a,b in zip(row,x)) for row in A]
            S.require(all(v<=1 and (v==1)==(i in F) for i,v in enumerate(vals)),
                      'literal original H vertex invalid')
            points[F]=x
        for i,(F,H) in enumerate(pairs):
            c=S.domino_route(k,F,H);S.verify_domino_route(c)
            path=list(map(frozenset,c['active_path']))
            S.require(all(T in adj[N] for N,T in zip(path,path[1:])), 'original path not in independent graph')
            edges+=c['edges'];shortest+=dist[F][H];nonshort+=c['edges']>dist[F][H]
            if i==0:saved.append(c)
        reports.append({'k':k,'original_facets':4*k+1,'vertices':len(fs),'edges_in_graph':sum(map(len,adj.values()))//2,
            'all_active_sets_examined':systems,'exact_graph_diameter':diam,
            'pairs_tested':len(pairs),'all_unordered_pairs':comb(len(fs),2),
            'delivered_edges':edges,'shortest_total':shortest,'nonshortest_paths':nonshort})
    large=[]
    for k in (8,16,32):
        c=S.domino_route(k,list(range(1,2*k+1)),list(range(2*k+1,4*k+1)))
        r=S.verify_domino_route(c);saved.append(c)
        large.append({**S.family_bound(k),**r,'shortest_by_disjoint_facet_drop':c['edges']==2*k,
                      'all_source_target_facets_disjoint':not set(c['start'])&set(c['target'])})
    return {'small_graphs':reports,'large_direct_routes':large},saved


def negative_tests(packets,samples,routes):
    failures=[]
    def reject(name,f):
        try:f()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):failures.append(name)
        else:raise AssertionError('accepted invalid certificate: '+name)
    p=deepcopy(packets[-1]);p['report']['final_tracked_descendants'][0]=[0,1]
    reject('false_descendant',lambda:S.verify_ancestry(p))
    p2=deepcopy(packets[-1]);p2['subdivide_faces'][0]=[0,0]
    reject('duplicate_subdivision_label',lambda:S.verify_ancestry(p2))
    reject('subdivide_nonface',lambda:S.stellar_face(S.base.Complex(4,[[0,1,2]]),[0,1,2]))
    reject('vertex_relabel_as_new_birth',lambda:S.stellar_face(S.base.Complex(4,[]),[0]))
    reject('boolean_label',lambda:S.stellar_face(S.base.Complex(4,[]),[False,1]))
    c=deepcopy(samples[0]['nonface']);c['weights'][0]='1'
    reject('false_affine_circuit',lambda:S.verify_nonface(c))
    c2=deepcopy(samples[0]['nonface']);c2['nonface'][0]=0
    reject('noninterleaved_nonface',lambda:S.verify_nonface(c2))
    c3=deepcopy(samples[0]['support']);c3['point'][0]='0'
    reject('false_original_support_point',lambda:S.verify_support(c3))
    c4=deepcopy(routes[-1]);c4['active_path'][1]=c4['target']
    reject('projected_chord_or_jump',lambda:S.verify_domino_route(c4))
    c5=deepcopy(routes[-1]);c5['edges']-=1
    reject('wrong_route_count',lambda:S.verify_domino_route(c5))
    c6=deepcopy(routes[-1]);c6['block_moves'][0]['direction']*=-1
    reject('forged_block_move',lambda:S.verify_domino_route(c6))
    c7=deepcopy(routes[-1]);c7['initial_domino_distance']+=1
    reject('false_initial_progress',lambda:S.verify_domino_route(c7))
    c8=deepcopy(routes[-1]);c8['k']=True
    reject('boolean_dimension',lambda:S.verify_domino_route(c8))
    reject('false_completion_size',lambda:S.require(comb(1000,2)>=comb(32,17)+(1000-65),
                                                  '1000 vertices cannot flagify this 65-facet input'))
    # Consumers do not select subdivision schedules, routes, LP bases, or inverses.
    old=S.domino_route
    def forbidden(*a,**kw):raise AssertionError('verifier called route search')
    S.domino_route=forbidden
    try:
        for c in routes:S.verify_domino_route(c)
        for p in packets:S.verify_ancestry(p)
    finally:S.domino_route=old
    return {'negative_controls':failures,'negative_count':len(failures),
            'route_search_disabled_replays':len(routes),'ancestry_replays':len(packets)}


def main():
    start=time.monotonic();ab,packets=abstract_tests();print('abstract',ab,flush=True)
    moment,samples=moment_tests();print('moment',moment['small_nonfaces'],flush=True)
    routes,paths=route_tests();print('routes',routes,flush=True)
    controls=negative_tests(packets,samples,paths)
    for k in range(2,81):
        r=S.family_bound(k);M=r['required_final_flag_vertices'];q=r['certified_minimal_nonface_subfamily'];m=r['original_facets']
        S.require(comb(M,2)>=q+M-m and (M==m or comb(M-1,2)<q+M-1-m),'rounded lower bound not minimal')
        S.require(q*2*(2*k+1)>=4**k,'elementary exponential binomial bound failed')
    report={'status':'PASS','scope':'Written original-nonface persistence and exact checks, not Lean or Prove2Me',
            'abstract':ab,'moment':moment,'routes':routes,'controls':controls,
            'integer_bound_cases_checked':79,'seconds':round(time.monotonic()-start,4),
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/'research/STELLAR_PERSISTENCE_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    fixture={'ancestry_packets':packets,'moment_witnesses':samples,'direct_original_routes':paths}
    (ROOT/'fixtures/stellar_persistence_examples.json').write_text(json.dumps(fixture,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
