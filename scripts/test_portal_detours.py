#!/usr/bin/env python3
"""Exact regressions, independently checked optimality, and forged-proof controls.

This script generates the fixtures and a source-hashed execution receipt.
No result is a Lean or platform acceptance verdict or a universal conjecture.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import random
import time

from portal_detour_optimizer import (
    ExactSimplePolytope, NoCertificate, cyclic_input, distances, dot, jsonable, rank, require,
)

from additive_allowance_solver import AllowanceSolver, verify_allowance, polynomial_budget

ROOT = Path(__file__).resolve().parents[1]


def graph_window_tests():
    graphs = walks = windows = repeated = 0
    for n in range(1, 5):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            G = [set() for _ in range(n)]
            for bit, (i, j) in enumerate(edges):
                if mask >> bit & 1:
                    G[i].add(j); G[j].add(i)
            D = [distances(G, [i]) for i in range(n)]
            graphs += 1
            def visit(path):
                nonlocal walks, windows, repeated
                L = len(path)-1
                slack = L-D[path[0]][path[-1]]
                require(slack >= 0, 'negative graph slack')
                walks += 1; repeated += int(len(set(path)) < len(path))
                total = 0
                for z in range(n):
                    hit = [i for i, v in enumerate(path) if v == z or v in G[z]]
                    require(len(hit) <= slack+3, 'position contact cardinality failed')
                    require(not hit or max(hit)-min(hit) <= slack+2, 'position span failed')
                    total += len(hit); windows += 1
                require(total <= (slack+3)*n, 'occurrence double count failed')
                if L < 5:
                    for v in sorted(G[path[-1]]):
                        visit(path+[v])
            for start in range(n):
                visit([start])
    # All k+3 contacts are attained, including repeated-label walks.
    G = [{1, 3}, {0, 2, 3}, {1, 3}, {0, 1, 2}]
    sharp = []
    for k in range(13):
        p = [0]+[1 if i % 2 == 0 else 3 for i in range(k+1)]+[2]
        require(len(p)-1-distances(G, [2])[0] == k, 'sharp witness slack')
        require(all(v == 3 or v in G[3] for v in p), 'sharp witness contacts')
        require(len(p) == k+3, 'sharp witness cardinality')
        sharp.append({'slack': k, 'contact_count': len(p), 'walk': p})
    return {'graphs': graphs, 'walks': walks, 'windows': windows,
            'walks_with_repeated_labels': repeated, 'sharp_slack_examples': sharp}


def affine_variant(data, seed):
    rng = random.Random(seed); A = [[Q(x) for x in row] for row in data['A']]
    n, d = len(A), len(A[0]); b = [Q(x) for x in data['b']]
    # x = T*y + t, with a rational upper-triangular invertible T.
    T = [[Q(int(i == j)) if j <= i else Q(rng.randrange(-2, 3), 3)
          for j in range(d)] for i in range(d)]
    t = [Q(0)]*d  # nonorthogonal coordinate changes suffice; source has strict zero
    order = list(range(n)); rng.shuffle(order)
    scales = [Q(rng.randrange(1, 8), rng.randrange(1, 8)) for _ in range(n)]
    newA = [[scales[k]*sum((A[i][j]*T[j][l] for j in range(d)), Q(0))
             for l in range(d)] for k, i in enumerate(order)]
    newb = [scales[k]*(b[i]-dot(A[i], t)) for k, i in enumerate(order)]
    balance = [Q(data['positive_balance'][i])/scales[k] for k, i in enumerate(order)]
    return {'A': newA, 'b': newb, 'strict_point': [0]*d, 'positive_balance': balance,
            'start_active': [order.index(i) for i in data['start_active']],
            'end_active': [order.index(i) for i in data['end_active']]}


def cube(d):
    return {'A': [[Q(sign*int(i == j)) for j in range(d)]
                  for sign in (-1, 1) for i in range(d)],
            'b': [1]*(2*d), 'strict_point': [0]*d, 'positive_balance': [1]*(2*d)}


def hexagon_product():
    hexrows = [(1,0), (0,1), (-1,1), (-1,0), (0,-1), (1,-1)]
    return {'A': [list(r)+( [0,0]) for r in hexrows]+[[0,0]+list(r) for r in hexrows],
            'b': [1]*12, 'strict_point': [0]*4, 'positive_balance': [1]*12}


def permutahedron():
    A = []; b = []
    for mask in range(1, 15):
        A.append([Q(int(mask >> j & 1)-int(mask >> 3 & 1)) for j in range(3)])
        k = mask.bit_count(); b.append(k*(4-k))
    return {'A': A, 'b': b, 'strict_point': [0]*3, 'positive_balance': [1]*14}


def random_spherical(seed, d=4, extra=4):
    rng = random.Random(seed)
    points = [[Q(sign*int(i == j)) for j in range(d)] for sign in (-1, 1) for i in range(d)]
    for _ in range(extra):
        t = [Q(rng.randrange(-13, 14), 7) for _ in range(d-1)]
        s = sum(x*x for x in t)
        points.append([2*x/(1+s) for x in t]+[(s-1)/(1+s)])
    center = [sum(p[j] for p in points)/len(points) for j in range(d)]
    return {'A': [[p[j]-center[j] for j in range(d)] for p in points],
            'b': [1]*len(points), 'strict_point': [0]*d, 'positive_balance': [1]*len(points)}


def check_routes(P, pairs, slack, mode='conservative'):
    out = []; failures = 0
    for s, t in pairs:
        try:
            cert = P.repair(s, t, slack, mode)
        except NoCertificate:
            failures += 1
            continue
        got = P.verify_repair(s, t, cert)
        shortest = distances(P.graph, [t])[s]
        require(got['cost'] >= shortest, 'constructed route shorter than exact graph distance')
        if mode == 'conservative':
            require(got['charge'] == 0, 'positive charge in conservative search')
        out.append({'start': s, 'end': t, 'slack': slack, 'mode': mode,
                    'cost': got['cost'], 'charge': got['charge'], 'nodes': got['nodes'],
                    'leaves': got['leaves'], 'shortest_distance': shortest,
                    'dimension': P.carrier(s, t)['dimension'],
                    'excess': P.carrier(s, t)['excess']})
    return out, failures


def shifted_excess_tests():
    tuples = budgets = 0
    for e in range(11):
        for b in range(5):
            for n in range(5):
                for masses in product(range(e+1), repeat=n):
                    if sum(masses)>e+b:continue
                    shifted=sum(max(x-b,0) for x in masses)
                    require(shifted<=max(e-b,0),'shifted mass conservation failed')
                    tuples+=1
                    if e>b:
                        for h in (1,3,7):
                            for C in (0,1,2,8):
                                A=1+b*C
                                lhs=1+sum(C*x+A*(h-1)*max(x-b,0) for x in masses)
                                rhs=C*e+A*h*(e-b)
                                require(lhs<=rhs,'additive node polynomial recurrence failed')
                                budgets+=1
    require(max(5-2,0)>max(3-2,0),'monotonicity negative control failed')
    require(2*max(7-2,0)>max(8-2,0),'sibling sum negative control failed')
    return {'shifted_mass_cases':tuples,'polynomial_node_cases':budgets,
            'assumption_negative_controls':2}


def main():
    begin = time.monotonic(); (ROOT/'fixtures').mkdir(exist_ok=True)
    stats = graph_window_tests(); shifted = shifted_excess_tests()
    examples = []; all_routes = []; exact_walks = 0
    total_bases = total_vertices = total_edges = total_pairs = 0
    built = []
    for n, start_rows, end_rows in [(10,[4,5,6,7],[0,1,2,9]), (12,[7,8,9,10],[1,2,3,4])]:
        data = cyclic_input(n, 4); data.update(start_active=start_rows, end_active=end_rows)
        P = ExactSimplePolytope(data); s, t = P.endpoints(data)
        built.append((f'cyclic_polar_{n}', P, data))
        table = []
        for k in range(3):
            for objective in ('excess', 'potential'):
                plan = P.optimize(s, t, k, objective)
                value, count = P.exhaustive_optimum(s, t, k, objective)
                exact_walks += count
                require(value == plan['objective_value'], 'independent optimality audit disagrees')
                table.append({'slack': k, 'objective': objective, 'minimum': value,
                              'exhaustive_label_walks': count, 'plan': plan,
                              'metrics': P.verify_plan(s, t, plan)})
            for mode in ('potential', 'lookahead', 'conservative'):
                results, failed = check_routes(P, [(s,t)], k, mode)
                all_routes += results
                require(failed == int(n == 12 and k == 0 and mode == 'conservative'),
                        'unexpected focused certificate result')
        mins = {(r['slack'], r['objective']): r['minimum'] for r in table}
        require([mins[k,'excess'] for k in range(3)] == ([7,5,4] if n == 10 else [16,10,7]),
                'focused mass minima changed')
        require([mins[k,'potential'] for k in range(3)] == ([19,9,4] if n == 10 else [32,26,13]),
                'focused potential minima changed')
        chosen = P.repair(s,t,1 if n == 12 else 2,'conservative')
        entry = {'name':f'cyclic_polar_{n}', 'rows':n, 'dimension':4, 'vertices':P.N,
                 'start_rows':start_rows, 'end_rows':end_rows,
                 'graph_distance':distances(P.graph,[t])[s], 'optimality_table':table,
                 'conservative_route':P.verify_repair(s,t,chosen)}
        examples.append(entry)
        (ROOT/f'fixtures/cyclic_polar_{n}_input.json').write_text(json.dumps(jsonable(data),indent=2)+'\n')
        (ROOT/f'fixtures/cyclic_polar_{n}_certificate.json').write_text(json.dumps(chosen,indent=2)+'\n')
        (ROOT/f'fixtures/cyclic_polar_{n}_optimality.json').write_text(json.dumps(entry,indent=2)+'\n')
    # Coordinate/row invariance, exact arithmetic throughout.
    base_data = built[1][2]
    for seed in (13,29):
        data = affine_variant(base_data,seed); P=ExactSimplePolytope(data); s,t=P.endpoints(data)
        for objective, expected in [('excess',16),('potential',32)]:
            plan=P.optimize(s,t,0,objective)
            require(plan['objective_value']==expected,'affine/row relabeling changed the optimum')
        res,fail=check_routes(P,[(s,t)],1)
        require(fail==0,'transformed conservative fixture failed')
        all_routes+=res;built.append((f'affine_{seed}',P,data))
    # Diverse exact simple polytopes; neither low rank nor product structure is required.
    other = [('cube4',cube(4)),('hexagon_product',hexagon_product()),('permutahedron3',permutahedron()),
             ('cyclic6_12',cyclic_input(12,6)), ('spherical11',random_spherical(11)),
             ('spherical19',random_spherical(19))]
    for name,data in other:
        P=ExactSimplePolytope(data);built.append((name,P,data))
        pair_list=[(i,j) for i in range(P.N) for j in range(i)]
        rng=random.Random(207);rng.shuffle(pair_list)
        # Include farthest pairs, not just pairs sharing tiny faces.
        best=max((distances(P.graph,[j])[i],i,j) for i,j in pair_list)
        chosen=[(best[1],best[2])]+pair_list[:9]
        results,failed=check_routes(P,chosen,1)
        all_routes+=results
        examples.append({'name':name,'rows':P.n,'dimension':P.d,'vertices':P.N,
                         'tested_pairs':len(chosen),'conservative_failures':failed,
                         'maximum_graph_distance':best[0], 'routes':results})
    # All ordered pair distances are independently computed for these finite examples.
    for name,P,_ in built:
        total_bases+=P.enumerated_bases;total_vertices+=P.N
        total_edges+=sum(map(len,P.graph))//2
        for v in range(P.N):
            require(len(distances(P.graph,[v]))==P.N,'disconnected complete polytope graph')
            total_pairs+=P.N
    # A real geometric repeated-label walk, with every occurrence accounted.
    P=built[0][1];data=built[0][2];s,t=P.endpoints(data)
    plan=P.optimize(s,t,0,'potential');repeat=deepcopy(plan)
    a,x,y=repeat['legs'][0];b=repeat['legs'][1][0]
    repeat['legs'][1:1]=[[b,y,y],[a,y,y]]
    repeat['slack_limit']=2
    repeated_geometry=P.verify_plan(s,t,repeat)
    require(repeated_geometry['region_occurrences']>repeated_geometry['distinct_regions'],
            'revisit test accidentally used distinct labels')
    (ROOT/'fixtures/repeated_region_plan.json').write_text(json.dumps(repeat,indent=2)+'\n')
    # Independent verifier rejects altered source problems and forged route certificates.
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('negative control accepted: '+name)
    for name,key,value in [('float','A',None),('bad_balance','positive_balance',[2]*9+[1]),
                           ('bad_strict_point','strict_point',[10**9]*4)]:
        bad=deepcopy(data)
        if key=='A':bad['A'][0][0]=0.125
        else:bad[key]=value
        reject(name,lambda bad=bad:ExactSimplePolytope(bad))
    reject('incomplete_enumeration',lambda:ExactSimplePolytope(data,1))
    bad=deepcopy(data);bad['A'].append(bad['A'][0]);bad['b'].append(bad['b'][0])
    bad['positive_balance'][0]=Q(1,2);bad['positive_balance'].append(Q(1,2))
    reject('duplicated_facet_description',lambda:ExactSimplePolytope(bad))
    octa={'A':list(map(list,product((-1,1),repeat=3))),'b':[1]*8,
          'strict_point':[0]*3,'positive_balance':[1]*8}
    reject('nonsimple_description',lambda:ExactSimplePolytope(octa))
    valid=P.repair(s,t,2,'conservative')
    for key,value in [('start',t),('end',s),('dimension',5),('excess',99),('cost',0),('charge',True),('kind','edge')]:
        bad=deepcopy(valid);bad[key]=value
        reject('forged_'+key,lambda bad=bad:P.verify_repair(s,t,bad))
    for key,value in [('old_vertex',s),('objective_value',999999),('slack_limit',-1)]:
        bad=deepcopy(valid);bad['plan'][key]=value
        reject('plan_'+key,lambda bad=bad:P.verify_repair(s,t,bad))
    bad=deepcopy(valid);bad['plan']['legs'][0][0]=next(iter(P.active[s]))
    reject('unavailable_row',lambda:P.verify_repair(s,t,bad))
    bad=deepcopy(valid);bad['children']=bad['children'][:-1]
    reject('dropped_child_occurrence',lambda:P.verify_repair(s,t,bad))
    bad=deepcopy(valid);bad['children'][0]['end']=s
    reject('changed_child_endpoint',lambda:P.verify_repair(s,t,bad))
    bad=deepcopy(repeat);bad['slack_limit']=0
    reject('uncharged_repeated_regions',lambda:P.verify_plan(s,t,bad))
    P12=built[1][1];s12,t12=P12.endpoints(built[1][2])
    bad=P12.repair(s12,t12,0,'potential');require(bad['charge']>0,'missing positive-charge control')
    bad=deepcopy(bad);bad['charge']=0
    reject('erased_cross_level_charge',lambda:P12.verify_repair(s12,t12,bad))
    # Check that failure is not confused with invalid input or a diameter claim.
    try:P12.repair(s12,t12,0,'conservative')
    except NoCertificate:pass
    else:raise AssertionError('strict-geodesic no-certificate control did not fail')
    # New amortization theorem: fixed additive excess spill, not zero spill.
    additive_results=[];additive_states=additive_transitions=0
    for name,P,data in built:
        if 'start_active' in data:
            sA,tA=P.endpoints(data)
        else:
            _,sA,tA=max((distances(P.graph,[j])[i],i,j)
                         for i in range(P.N) for j in range(i))
        solver=AllowanceSolver(P,2)
        try:
            certA=solver.solve(sA,tA,1)
        except NoCertificate:
            additive_results.append({'name':name,'status':'NO_ADMITTED_TREE'})
            continue
        got=verify_allowance(P,sA,tA,certA,2)
        additive_results.append({'name':name,'status':'PASS',**got})
        additive_states+=solver.states;additive_transitions+=solver.transitions
        if name=='cyclic_polar_12':
            (ROOT/'fixtures/cyclic_polar_12_additive_certificate.json').write_text(
                json.dumps(certA,indent=2)+'\n')
            require(got['cost']==6 and got['polynomial_bound']==80,'additive focused fixture changed')
            bad=deepcopy(certA);bad['allowance']=1
            reject('changed_additive_allowance',lambda bad=bad,P=P,sA=sA,tA=tA:
                verify_allowance(P,sA,tA,bad,2))
            bad=deepcopy(certA);bad['kind']='small';bad['route']=got['route']
            reject('large_excess_small_leaf',lambda bad=bad,P=P,sA=sA,tA=tA:
                verify_allowance(P,sA,tA,bad,2))
            bad=deepcopy(certA);bad['plan']=P.optimize(sA,tA,0,'potential')
            reject('uncharged_additive_sibling_spill',lambda bad=bad,P=P,sA=sA,tA=tA:
                verify_allowance(P,sA,tA,bad,2))
            bad=deepcopy(certA);bad['cost']=1
            reject('forged_additive_total_cost',lambda bad=bad,P=P,sA=sA,tA=tA:
                verify_allowance(P,sA,tA,bad,2))
            try:solver.solve(sA,tA,0)
            except NoCertificate:pass
            else:raise AssertionError('strict-geodesic additive control should fail')
    paths = sorted((ROOT/'Solutions').glob('*.lean'))+sorted((ROOT/'scripts').glob('*.py'))
    receipt={'status':'PASS','scope':'Exact finite checks, not Lean or Prove2Me acceptance.',
             'graph_windows':stats,'shifted_excess_checks':shifted,
             'additive_allowance_examples':additive_results,
             'additive_solver_states':additive_states,'additive_solver_transitions':additive_transitions,
             'polytope_instances':len(built),'enumerated_active_bases':total_bases,
             'complete_vertices':total_vertices,'exact_edges':total_edges,'ordered_graph_distances':total_pairs,
             'independently_audited_label_walks':exact_walks,'verified_recursive_routes':len(all_routes),
             'verified_edge_occurrences':sum(r['cost'] for r in all_routes),
             'verified_internal_node_occurrences':sum(r['nodes'] for r in all_routes),
             'negative_controls_rejected':len(rejected),'negative_control_names':rejected,
             'valid_but_no_zero_charge_tree_controls':1,
             'repeated_region_geometric_check':repeated_geometry,
             'dp_states_evaluated':sum(P.dp_state_visits for _,P,_ in built),
             'dp_transitions_evaluated':sum(P.dp_transitions for _,P,_ in built),
             'examples':examples,'routes':all_routes,
             'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
             'elapsed_seconds':round(time.monotonic()-begin,3)}
    (ROOT/'research/PORTAL_DETOUR_CHECK_2026-09-12.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    compact={k:v for k,v in receipt.items() if k not in ('examples','routes','graph_windows')}
    compact['graph_windows']={k:v for k,v in stats.items() if k!='sharp_slack_examples'}
    compact['focused_counterexamples']=[{'name':x['name'], 'vertices':x['vertices'],
        'graph_distance':x['graph_distance'],
        'minimum_mass_by_slack':[r['minimum'] for r in x['optimality_table'] if r['objective']=='excess'],
        'minimum_child_potential_by_slack':[r['minimum'] for r in x['optimality_table'] if r['objective']=='potential'],
        'conservative_route':x['conservative_route']} for x in examples[:2]]
    compact['other_examples']=[{k:v for k,v in x.items() if k!='routes'} for x in examples[2:]]
    (ROOT/'research/PORTAL_DETOUR_SUMMARY_2026-09-12.json').write_text(json.dumps(compact,indent=2,sort_keys=True)+'\n')
    print(json.dumps(compact,indent=2,sort_keys=True))


if __name__=='__main__':main()
