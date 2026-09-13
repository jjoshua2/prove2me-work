#!/usr/bin/env python3
"""Executed exact checks for the cyclic transport obstruction and adaptive routes.

Independent H-basis enumeration checks the matching model in small cases.
Independent label-walk enumeration checks selected optimizer minima. Large
route certificates use explicit slack polynomials, not an enumerated graph.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random
import time
from cyclic_slack_obstruction import (
    CyclicPortalModel, ExactSimplePolytope, adaptive_block_certificate, all_supports,
    cycle_distance, extend_matching, matching_for, moment_description,
    obstruction_parameters, verify_adaptive_certificate, vertex_from_roots,
    verify_vertex, jsonable, require, two_heavy_upper_witness,
)
from portal_detour_optimizer import distances
from additive_allowance_solver import verify_allowance

ROOT=Path(__file__).resolve().parents[1]


def direct_additive_tree(P,n,d,allowance=2):
    m=n//2; ids=[P.active.index(frozenset(range(j,j+d))) for j in range(m+1)]
    leaves=[{'kind':'small','start':ids[j],'end':ids[j+1],
             'dimension':1,'excess':1,'allowance':allowance,'cost':1,
             'route':[ids[j],ids[j+1]]} for j in range(1,m)]
    cert={'kind':'node','start':ids[0],'end':ids[-1], 'dimension':d,
          'excess':n-d,'allowance':allowance,'cost':m,
          'plan':{'old_vertex':ids[1],
                  'legs':[[j+d-1,ids[j],ids[j+1]] for j in range(1,m)],
                  'slack_limit':m-3,'objective':'recursive','objective_value':m-1,
                  'policy':'additive_allowance'},'children':leaves}
    return ids[0],ids[-1],cert


def main():
    begin=time.monotonic(); stats={}; rng=random.Random(209)
    (ROOT/'fixtures').mkdir(exist_ok=True); (ROOT/'research').mkdir(exist_ok=True)
    augmentations=0; partials=0
    for n in range(5,15):
        for size in range(2,min(6,n-3)+1,2):
            # Covers every partial matching support at these sizes.
            for S in combinations(range(n),size):
                try: M=matching_for(n,S)
                except ValueError: continue
                partials+=1
                for row in range(n):
                    out=extend_matching(n,M,row)
                    T={x for edge in out for x in edge}
                    require(set(S)<=T and row in T and len(T)==size+2,'augmentation failed')
                    matching_for(n,T); augmentations+=1
    stats.update(partial_matching_supports=partials,requested_row_augmentations=augmentations)
    realized=[]; basis_count=0; matched_vertices=0; matched_edges=0
    for n,d in [(10,4),(12,4),(12,6),(12,8)]:
        A=ExactSimplePolytope(moment_description(n,d))
        C=CyclicPortalModel(n,d)
        require(set(A.active)==set(C.active),'independent H enumeration disagrees with matching criterion')
        ai={S:i for i,S in enumerate(A.active)}
        for v,S in enumerate(C.active):
            p,cert=vertex_from_roots(n,d,S);verify_vertex(n,d,p,cert)
            require(p==A.points[ai[S]],'slack-polynomial vertex differs from linear solve')
            neighA={A.active[j] for j in A.graph[ai[S]]}
            require(neighA=={C.active[j] for j in C.graph[v]},'ordinary-edge graphs disagree')
        basis_count+=A.enumerated_bases;matched_vertices+=A.N;matched_edges+=sum(map(len,A.graph))//2
        realized.append({'n':n,'dimension':d,'vertices':A.N,'edges':sum(map(len,A.graph))//2})
    stats.update(independent_active_bases=basis_count,matched_rational_vertices=matched_vertices,
                 matched_ordinary_edges=matched_edges,independent_realizations=realized)
    paircases=0; carrier_witnesses=0; lightcases=0; fullcases=0
    for n,d in [(10,4),(14,4),(18,4),(12,6),(16,6),(14,8)]:
        P=CyclicPortalModel(n,d)
        pairs=list(combinations(range(P.N),2))
        if len(pairs)>3000: pairs=rng.sample(pairs,3000)
        for u,v in pairs:
            carrier_witnesses+=P.audit_pair(u,v);paircases+=1
            if P.carrier(u,v)['excess']<n-d: lightcases+=1
            else: fullcases+=1
    stats.update(carrier_pair_checks=paircases,light_transport_pairs=lightcases,
                 full_excess_pairs=fullcases,explicit_full_carrier_row_witnesses=carrier_witnesses)
    profiles=[]; independentwalks=0; minima=0
    for n in (14,16,18,20,24):
        P=CyclicPortalModel(n,4);s,t=P.block_endpoints();rows=[]
        for k in range(min(5,n//2-2)):
            plan=P.optimize(s,t,k,'excess');value=plan['objective_value'];minima+=1
            if n//2-4+1>k+3: require(value==2*(n-4),'infinite-family exact minimum failed')
            if n<=16 and k<=1:
                independent,count=P.exhaustive_optimum(s,t,k,'excess')
                require(independent==value,'independent label-walk optimum disagrees')
                independentwalks+=count
            rows.append({'slack':k,'minimum_child_excess':value})
        s,t,tree=direct_additive_tree(P,n,4)
        got=verify_allowance(P,s,t,tree,2)
        require(got['cost']==n//2 and got['leaf_mass']==n//2-1 and got['internal_nodes']==1,
                'old #208 verifier rejected adaptive exact conservation')
        profiles.append({'n':n,'dimension':4,'vertices':P.N,'parent_excess':n-4,
                         'fixed_slack_profile':rows,'adaptive':got,
                         'actual_endpoint_distance':distances(P.graph,[t])[s]})
        if n==24:
            (ROOT/'fixtures/cyclic_24_additive_tree.json').write_text(json.dumps(tree,indent=2)+'\n')
    stats.update(optimized_root_minima=minima,independently_audited_label_walks=independentwalks,
                 profiles=profiles,old_verifier_adaptive_trees=len(profiles))
    # Certified routes in high dimension and at large facet counts. NO complete
    # incidence/vertex enumeration occurs inside this loop.
    routes=[]; points=edges=row_checks=0
    for n,d,k in [(40,4,8),(32,6,5),(40,8,4),(60,10,12),(80,12,20),(200,8,40)]:
        params=obstruction_parameters(n,d,k,2)
        cert=adaptive_block_certificate(n,d);got=verify_adaptive_certificate(cert)
        verify_adaptive_certificate(json.loads(json.dumps(jsonable(cert))))
        upper=two_heavy_upper_witness(n,d)
        require(upper['total_child_excess']==params['minimum_child_excess'], 'upper witness did not attain lower bound')
        require(params['minimum_child_excess']>params['parent_excess']+2,'not a bounded-spill obstruction')
        points+=len(cert['points']);edges+=cert['actual_edge_count'];row_checks+=n*len(cert['points'])
        routes.append({'parameters':params,'verified':got,'vertex_enumeration':False,
                       'complete_polytope_vertices':n*__import__('math').comb(n-d//2,d//2)//(n-d//2),
                       'heavy_child_dimensions':[leg['carrier_dimension'] for leg in upper['legs']]})
        if (n,d)==(40,8):
            (ROOT/'fixtures/cyclic_40d8_adaptive.json').write_text(json.dumps(jsonable(cert),indent=2)+'\n')
    stats.update(non_enumerating_adaptive_examples=routes,explicit_slack_vertices=points,
                 explicit_certified_edges=edges,exact_original_inequality_checks=row_checks)
    # Boundary: a light carrier can move a row by exactly one.
    P=CyclicPortalModel(14,4)
    A=frozenset([0,1,6,7]);B=frozenset([1,2,7,8])
    u=P.index[A];v=P.index[B]
    require(P.carrier(u,v)['excess']==2,'quadrilateral control changed')
    require(max(min(cycle_distance(14,i,j) for j in B) for i in A)==1,'light transport should be sharp')
    # One heavy step DOES jump arbitrarily far while retaining a row.
    C=frozenset([0,1,2,3]);D=frozenset([0,1,8,9])
    require(P.carrier(P.index[C],P.index[D])['excess']==10,'heavy jump witness failed')
    # Negative controls: independently reject corrupted finite route witnesses.
    rejected=[]
    def reject(name,fn):
        try: fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError): rejected.append(name)
        else: raise AssertionError('accepted invalid control: '+name)
    reject('odd_dimension',lambda:moment_description(20,5))
    reject('too_few_rows',lambda:moment_description(8,8))
    reject('incomplete_incidence_cap',lambda:CyclicPortalModel(24,8,10))
    reject('nonmatching_active_set',lambda:matching_for(14,[0,2,4,6]))
    reject('overlapping_partial_edges',lambda:extend_matching(14,[(0,1),(1,2)],8))
    reject('noncycle_partial_edge',lambda:extend_matching(14,[(0,2)],8))
    reject('unproved_separation_parameters',lambda:obstruction_parameters(14,4,8,2))
    good=adaptive_block_certificate(24,4)
    for name,mut in [
        ('changed_source',lambda x:x.update(source_active=[1,2,3,4])),
        ('changed_target',lambda x:x.update(target_active=[0,1,2,3])),
        ('false_cost',lambda x:x.update(actual_edge_count=1)),
        ('false_mass',lambda x:x.update(total_child_excess=0)),
        ('false_slack',lambda x:x.update(region_slack=0)),
        ('deleted_portal_leg',lambda x:x['legs'].pop()),
        ('changed_coordinate',lambda x:x['points'].__setitem__(1,x['points'][0])),
        ('false_slack_polynomial',lambda x:x['vertex_certificates'][0]['polynomial_coefficients'].__setitem__(0,5)),
        ('bad_normalizing_mean',lambda x:x['vertex_certificates'][0].update(mean_polynomial_value=-1)),
        ('false_active_rows',lambda x:x['vertex_certificates'][0].update(active=[0,2,4,6])),
        ('floating_coordinate',lambda x:x['points'].__setitem__(0,[float(v) for v in x['points'][0]])),
        ('boolean_mass_tag',lambda x:x['legs'][0].update(excess=True)),
    ]:
        bad=deepcopy(good);mut(bad)
        reject(name,lambda bad=bad:verify_adaptive_certificate(bad))
    stats.update(negative_controls_rejected=len(rejected),negative_control_names=rejected)
    new_sources=[ROOT/'scripts/cyclic_slack_obstruction.py',ROOT/'scripts/test_cyclic_slack_obstruction.py',
                 ROOT/'Solutions/PolynomialTransportHeavyJumps.lean',
                 ROOT/'Solutions/PolynomialSupportingSlackCertificates.lean']
    receipt={'status':'PASS','scope':'Exact finite and rational checks; full infinite statements are proved in the note, not inferred from testing. New Lean source is uncompiled.',
             **stats,'new_source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in new_sources},
             'reused_source_sha256':{name:hashlib.sha256((ROOT/'scripts'/name).read_bytes()).hexdigest()
                                     for name in ('portal_detour_optimizer.py','additive_allowance_solver.py')},
             'elapsed_seconds':round(time.monotonic()-begin,3)}
    (ROOT/'research/CYCLIC_SLACK_CHECK_2026-09-12.json').write_text(json.dumps(jsonable(receipt),indent=2,sort_keys=True)+'\n')
    print(json.dumps(jsonable(receipt),indent=2,sort_keys=True))

if __name__=='__main__': main()
