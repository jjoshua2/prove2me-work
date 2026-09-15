#!/usr/bin/env python3
"""Independent stellar membership, rational polar geometry and carrier checks.

All finite input complexes are specified explicitly. This harness enumerates
small original face lattices and refined graphs; it does NOT claim efficient
H-classification or avoid those enumerations. The production certificate
checker does not solve LPs, invert matrices, or search for a refined route.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json, random, time
import stellar_defect_budget as S
import simple_tangent_policy_audit as H

ROOT=Path(__file__).resolve().parents[1]
DEPENDENCY_BLOB='73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976'


def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in [Path(__file__),ROOT/'scripts/stellar_defect_budget.py',
                      ROOT/'scripts/simple_tangent_policy_audit.py']}


def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(H.serial(data),indent=2,sort_keys=True)+'\n')


def all_faces(facets):
    return {frozenset(T) for F in facets for size in range(len(F)+1)
            for T in combinations(sorted(F),size)}


def missing_from_facets(n,facets):
    faces=all_faces(facets);d=max(map(len,facets),default=0);missing=[]
    for size in range(2,min(n,d+1)+1):
        for T in combinations(range(n),size):
            T=frozenset(T)
            if T not in faces and all(T-{i} in faces for i in T):missing.append(T)
    return S.Complex.create(n,S.lists(missing))


def facets_from_missing(K):
    good=[frozenset(T) for size in range(K.n+1) for T in combinations(range(K.n),size) if K.face(T)]
    return S.ordered([F for F in good if not any(F<G for G in good)])


def cyclic_facets(n,d):
    # Gale evenness; sorted complement pairs are essential for the interval test.
    return [frozenset(T) for T in combinations(range(n),d)
            if all(sum(a<v<b for v in T)%2==0
                   for a,b in combinations(sorted(set(range(n))-set(T)),2))]


def cyclic_complex(n,d):
    return missing_from_facets(n,cyclic_facets(n,d))


def adjacency(facets,d):
    buckets={};G={F:set() for F in facets}
    for F in facets:
        S.require(len(F)==d,'impure reference complex')
        for v in F:buckets.setdefault(F-{v},[]).append(F)
    for members in buckets.values():
        S.require(len(members)==2,'closed pseudomanifold ridge must have two carriers')
        F,Hh=members;G[F].add(Hh);G[Hh].add(F)
    return G


def path(G,start,end,locked=frozenset()):
    prev={start:None};queue=deque([start])
    while queue:
        F=queue.popleft()
        if F==end:break
        for N in S.ordered(G[F]):
            if N not in prev and locked<=N:prev[N]=F;queue.append(N)
    S.require(end in prev,'reference common-face graph disconnected')
    out=[];F=end
    while F is not None:out.append(F);F=prev[F]
    return out[::-1]


def algebra_stage():
    rng=random.Random(262);tested=[]
    triples=list(combinations(range(5),3))
    for mask in range(1<<len(triples)):
        tested.append(S.Complex.create(5,[T for j,T in enumerate(triples) if mask>>j&1]))
    for n in (5,6,7):
        subsets=[frozenset(T) for size in range(2,min(n,5)+1) for T in combinations(range(n),size)]
        for _ in range(32):
            chosen=rng.sample(subsets,rng.randrange(1,min(16,len(subsets))))
            tested.append(S.Complex.create(n,S.lists(S.minimal(chosen))))
    counts={'complexes':len(tested),'all_face_edge_updates':0,'independent_membership_tests':0,
            'shielded_updates':0,'unequal_incidence_shielded_updates':0,
            'unshielded_decreasing_updates':0,'weight_increasing_updates':0}
    for K in tested:
        facets=facets_from_missing(K)
        for E in combinations(range(K.n),2):
            if not K.face(E):continue
            J,r=S.account(K,E);ff=S.subdivide_facets(facets,E,K.n)
            reference=missing_from_facets(K.n+1,ff)
            S.require(J==reference,'residue update differs from literal stellar facets')
            faces=all_faces(ff)
            for size in range(K.n+2):
                for U in combinations(range(K.n+1),size):
                    S.require(J.face(U)==(frozenset(U) in faces),'whole membership mismatch')
                    counts['independent_membership_tests']+=1
            counts['all_face_edge_updates']+=1;counts['shielded_updates']+=r['shielded']
            twins=all((E[0] in N)==(E[1] in N) for N in K.higher())
            counts['unequal_incidence_shielded_updates']+=r['shielded'] and not twins
            counts['unshielded_decreasing_updates']+=not r['shielded'] and J.weight()<K.weight()
            counts['weight_increasing_updates']+=J.weight()>K.weight()
    K=cyclic_complex(7,4);J,r=S.account(K,(0,3))
    S.require(K.weight()==7 and J.weight()==8 and r['consumed_higher_nonfaces']==1 and r['created_higher_weight']==2,
              'productive edge need not decrease total higher weight')
    return {'counts':counts,'productive_edge_increase_control':{'input':K.payload(),'step':r,'output':J.payload()}}


def family_stage():
    results = []
    for n in [6,7,8,9,10,12,16,20]:
        original, packet, result = S.cyclic_four_schedule(n)
        if n <= 12:
            S.require(original == cyclic_complex(n,4), 'stable triples differ from full Gale boundary')
        result['independent_full_Gale_nonface_comparison'] = n <= 12
        result['initial_twins'] = len(S.choices(original,'twins'))
        results.append(result)
    return {'cases':results, 'refined_graph_enumerated':False,
            'all_dimension_statement':'For the dimension-four cyclic family only, M <= n*(n-1)/2.'}


def moment_points(n,d):
    raw=[tuple(Q(t)**j for j in range(1,d+1)) for t in range(1,n+1)]
    center=tuple(sum(x[j] for x in raw)/n for j in range(d))
    return [tuple(x[j]-center[j] for j in range(d)) for x in raw]


def supporting_normals(points,facets):
    d=len(points[0]);normals={}
    for F in facets:
        inv=H.invert([points[i] for i in sorted(F)])
        a=tuple(sum(row,Q(0)) for row in inv)
        S.require(all(H.dot(a,p)==1 if i in F else H.dot(a,p)<1 for i,p in enumerate(points)),
                  'dual facet not an exact strict original support')
        normals[F]=a
    return normals


def realize_stellar(points,facets,edge):
    normals=supporting_normals(points,facets);E=frozenset(edge)
    S.require(any(E<=F for F in facets),'realization edge absent')
    mid=tuple((points[edge[0]][j]+points[edge[1]][j])/2 for j in range(len(points[0])))
    cap=[Q(1)]
    for F,a in normals.items():
        v=H.dot(a,mid)
        if not E<=F and v>0:cap.append((1-v)/v)
    eps=min(cap)/2
    S.require(eps>0,'positive stellar realization radius')
    y=tuple((1+eps)*x for x in mid)
    S.require(all(H.dot(a,y)>1 if E<=F else H.dot(a,y)<1 for F,a in normals.items()),
              'visible facets differ from the edge star')
    ff=S.subdivide_facets(facets,edge,len(points));pp=points+[y]
    supporting_normals(pp,ff)
    return pp,ff,{'edge':list(edge),'new_point':y,'epsilon':eps,'visible_facets':S.lists([F for F in facets if E<=F])}


def reference_bases(points,facets):
    # The primal is the polar P={x: point_i.x<=1}. Independent origin-interior
    # and stellar visibility arguments ensure this COMPLETE dual boundary.
    normals=supporting_normals(points,facets)
    A=[list(x) for x in points];b=[Q(1)]*len(points)
    packets={F:H.basis_packet(A,b,list(normals[F])) for F in facets}
    for F,p in packets.items():
        _,J,_=H.audit_basis(A,b,p);S.require(frozenset(J)==F,'dual/primal incidence mismatch')
    return A,b,packets


def audit_original_edge(A,b,packets,F,T):
    x,J,D=H.audit_basis(A,b,packets[F]);y,_,_=H.audit_basis(A,b,packets[T])
    S.require(len(F-T)==len(T-F)==1,'not a single original facet exchange')
    i=J.index(next(iter(F-T)));length,blocker=H.maximal_step(A,b,x,D[i])
    S.require(length>0 and [u+length*v for u,v in zip(x,D[i])]==y,'carrier is not full original edge')
    return {'from':sorted(F),'to':sorted(T),'length':length,'blocker':blocker}


def geometry_case(n,d,preedges=(),pair_limit=30):
    begin=time.monotonic();points=moment_points(n,d);facets=cyclic_facets(n,d)
    # Initial facets from exact Gale evenness; every support is checked rationally.
    supporting_normals(points,facets)
    independent=[]; initial_bases=0
    for F in combinations(range(n),d):
        initial_bases+=1
        try: inverse=H.invert([points[i] for i in F])
        except ValueError:continue
        a=tuple(sum(row,Q(0)) for row in inverse)
        if all(H.dot(a,p)<=1 for p in points):independent.append(frozenset(F))
    S.require(S.ordered(independent)==S.ordered(facets), 'independent supporting-plane enumeration differs from Gale')
    realization=[]
    for E in preedges:
        points,facets,step=realize_stellar(points,facets,E);realization.append(step)
    K=missing_from_facets(len(points),facets)
    allrefinements={policy:S.refine(K,policy) for policy in ('twins','shielded','budget')}
    summaries={policy:S.verify(K,c) for policy,c in allrefinements.items()}
    cert=allrefinements['budget'];S.require(cert['status']=='flag','benchmark must complete budget refinement')
    fine=facets
    for step in cert['steps']:fine=S.subdivide_facets(fine,step['edge'],step['new_label'])
    S.require(all(len(F)==d for F in fine),'stellar dimension changed')
    GG=adjacency(fine,d);G=adjacency(facets,d)
    A,b,bases=reference_bases(points,facets);M=cert['terminal']['vertices']
    anchors=[]
    for row in range(len(points)):
        incident=[p['point'] for F,p in bases.items() if row in F]
        a=[sum(x[j] for x in incident)/len(incident) for j in range(d)]
        S.require(H.feasible(A,b,a) and H.active_rows(A,b,a)==[row], 'original facet not genuine')
        anchors.append(a)
    pairs=list(combinations(facets,2))
    if pair_limit<len(pairs):
        random.Random(n*100+d+len(preedges)).shuffle(pairs);pairs=pairs[:pair_limit]
    counts={'routes':0,'refined_edges':0,'original_edges':0,'shortest_original_edges':0,
            'nonshortest_routes':0,'stationary_carrier_steps':0,'preserved_common_facets':0}
    examples=[]
    for F,T in pairs:
        X,Y=S.lift_pair(F,T,cert['steps']);finepath=path(GG,X,Y,X&Y)
        coarse=S.transport(K,cert['steps'],finepath,d)
        S.require(coarse[0]==F and coarse[-1]==T and all(F&T<=U for U in coarse),'common original face lost')
        S.require(len(finepath)-1<=M-d,'flag normal diameter bound failure')
        for U,V in zip(coarse,coarse[1:]):audit_original_edge(A,b,bases,U,V)
        distance=len(path(G,F,T))-1
        S.require(distance<=len(coarse)-1<=len(finepath)-1,'false original route count')
        counts['routes']+=1;counts['refined_edges']+=len(finepath)-1
        counts['original_edges']+=len(coarse)-1;counts['shortest_original_edges']+=distance
        counts['nonshortest_routes']+=len(coarse)-1>distance
        counts['stationary_carrier_steps']+=len(finepath)-len(coarse)
        counts['preserved_common_facets']+=len(F&T)
        if len(examples)<2:examples.append({'refined_path':[sorted(U) for U in finepath],
                 'original_path':[sorted(U) for U in coarse],'reference_distance':distance})
    # Recheck a complete stored geometric certificate without any inversion or search.
    original_invert=H.invert
    def forbidden(*args,**kwargs):raise AssertionError('audit invoked inverse discovery')
    H.invert=forbidden
    try:
        S.verify(K,cert)
        for ex in examples:
            coarse=S.transport(K,cert['steps'],ex['refined_path'],d)
            for F,T in zip(coarse,coarse[1:]):audit_original_edge(A,b,bases,F,T)
    finally:H.invert=original_invert
    result={'name':f'C{n}_{d}'+('_four_stellar' if preedges else ''),'dimension':d,
        'original_facets':len(points),'original_vertices':len(facets),'original_graph_edges':sum(map(len,G.values()))//2,
        'initial_higher_nonfaces':len(K.higher()),'initial_weight':K.weight(),
        'independent_initial_supporting_plane_bases':initial_bases,'genuine_original_facet_anchors':len(anchors),
        'policies':summaries,'final_refined_vertices':M,'final_refined_facets':len(fine),
        'all_pair_bound_from_refinement':M-d,'counts':counts,
        'supplied_complete_finite_face_data':True,'reference_and_refined_graphs_enumerated':True,
        'audit_with_inverse_disabled':True,'seconds':round(time.monotonic()-begin,3)}
    if preedges or (n,d)==(7,4):
        dump(ROOT/f'fixtures/{result["name"]}.json',{'original_A':A,'original_b':b,
            'original_dual_facets':S.lists(facets),'original_minimal_nonfaces':K.payload(),
            'polytopal_realization':realization,'original_facet_anchors':anchors,'refinements':allrefinements,
            'original_basis_packets':[bases[F] for F in S.ordered(bases)],'route_examples':examples,'summary':result})
    return result


def geometry_stage():
    specs=[(6,4,(),1000),(7,4,(),1000),(8,4,(),1000),(8,6,(),20),(9,6,(),20),
           (10,6,(),20),(10,6,((3,6),(2,7),(0,3),(5,8)),20)]
    results=[]
    for args in specs:
        out=geometry_case(*args);results.append(out)
        print(out['name'],out['initial_weight'],out['policies']['budget']['stellar_steps'],
              out['final_refined_facets'],out['counts'],flush=True)
    stall=results[-1]
    S.require(stall['policies']['shielded']['completion']=='stalled' and
              stall['policies']['budget']['mixed_steps_creating_higher_nonfaces']>0,
              'genuine geometric no-splitting stall not demonstrated')
    totals={k:sum(r['counts'][k] for r in results) for k in results[0]['counts']}
    return {'cases':results,'totals':totals,'new_Lean_or_platform_verdict':False}


def negative_stage():
    K=cyclic_complex(7,4);packet=S.refine(K);names=[]
    def reject(name,call):
        try:call()
        except (ValueError,KeyError,IndexError,TypeError):names.append(name)
        else:raise AssertionError('accepted invalid '+name)
    for key,value in [('input_sha256','bad'),('policy','unknown'),('format','bad')]:
        c=deepcopy(packet);c[key]=value;reject(key,lambda c=c:S.verify(K,c))
    for key,value in [('weight_after',0),('consumed_higher_nonfaces',999),('created_higher_weight',0),('new_label',0)]:
        c=deepcopy(packet);c['steps'][0][key]=value
        if c['steps'][0]==packet['steps'][0]:c['steps'][0][key]=999
        reject('step_'+key,lambda c=c:S.verify(K,c))
    c=deepcopy(packet);c['steps'].pop();reject('omitted_step',lambda:S.verify(K,c))
    c=S.refine(K,step_cap=0);c['status']='flag';reject('partial_called_flag',lambda:S.verify(K,c))
    c=S.refine(K,step_cap=0);c['status']='stalled';reject('false_local_stall',lambda:S.verify(K,c))
    c=deepcopy(packet);c['terminal']['minimal_nonfaces'].pop();reject('omitted_terminal_nonface',lambda:S.verify(K,c))
    reject('missing_pair_not_face_edge',lambda:S.account(S.Complex.create(3,[[0,1]]),[0,1]))
    reject('duplicate_labels',lambda:S.Complex.create(3,[[0,0,1]]))
    reject('nonminimal_catalogue',lambda:S.Complex.create(3,[[0,1],[0,1,2]]))
    reject('float_label',lambda:S.Complex.create(3,[[0.0,1]]))
    reject('negative_cap',lambda:S.refine(K,step_cap=-1))
    step=S.account(K,[0,3])[1]
    bad={'format':packet['format'],'input_sha256':S.fingerprint(K),'policy':'budget','steps':[step],
         'status':'partial','terminal':S.account(K,[0,3])[0].payload()}
    reject('positive_defect_debt',lambda:S.verify(K,bad))
    capped=S.refine(K,candidate_cap=0);S.verify(K,capped)
    S.require(capped['status']=='candidate_cap' and capped['steps']==[],'cap handling')
    abstract=S.Complex.create(6,[[0,1,4],[0,3,5],[1,2,5],[2,3,4],[0,2,4,5],[1,3,4,5]])
    stall=S.refine(abstract); S.require(stall['status']=='stalled','abstract local stall missing')
    values=[{'edge':list(E),'weight_change':S.account(abstract,E)[0].weight()-abstract.weight()}
            for E in S.productive_edges(abstract)]
    S.require(min(v['weight_change'] for v in values)==0,'abstract stall value changed')
    return {'rejected':len(names),'names':names,'capped_packet_not_complete':True,
            'abstract_budget_stall':{'input':abstract.payload(),'all_productive_edge_changes':values,
                                    'pure':False,'polytopal_claimed':False}}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['algebra','geometry','family','negative','assemble']);a=p.parse_args()
    blob=(ROOT/'scripts/simple_tangent_policy_audit.py').read_bytes()
    S.require(hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()==DEPENDENCY_BLOB,'changed old auditor')
    stages=['algebra','geometry','family','negative'] if a.stage is None else [a.stage]
    for stage in stages:
        if stage=='assemble':continue
        begin=time.monotonic();result=globals()[stage+'_stage']()
        dump(ROOT/f'research/STELLAR_BUDGET_STAGE_{stage}.json',{'source_sha256':hashes(),'result':result,
             'seconds':round(time.monotonic()-begin,3)})
        print(stage,'PASS',round(time.monotonic()-begin,3),flush=True)
    if a.stage is None or a.stage=='assemble':
        stages={name:json.loads((ROOT/f'research/STELLAR_BUDGET_STAGE_{name}.json').read_text()) for name in ['algebra','geometry','family','negative']}
        S.require(all(s['source_sha256']==hashes() for s in stages.values()),'stale staged tests')
        result={'status':'PASS','scope':'Exact finite-complex identities and rational original-polar edges; no Lean or platform verdict.',
                'source_sha256':hashes(),'stages':stages}
        dump(ROOT/'research/STELLAR_DEFECT_BUDGET_CHECK.json',result)
        print('ASSEMBLED',stages['geometry']['result']['totals'],flush=True)
if __name__=='__main__':main()
