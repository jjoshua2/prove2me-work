#!/usr/bin/env python3
"""Original-edge audits for the target-roof constant-face phase barrier.

Full trajectories d2..12 are executed; d16/32/64 checks are explicitly SELECTED
steps only. SymPy is used only for independent small complete H-graph recovery.
No new Lean, Actions or platform verification is claimed by this script.
"""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json, time
import target_roof_phase_barrier as roof
import simple_tangent_policy_audit as old

ROOT = Path(__file__).resolve().parents[1]
require, dot, serial = old.require, old.dot, old.serial
EXPECTED_DEPENDENCY_BLOB = '73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976'


def source_hashes():
    paths = [ROOT/'scripts'/s for s in ('target_roof_phase_barrier.py', 'test_target_roof_phase_barrier.py', 'simple_tangent_policy_audit.py')]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def small_graph(data):
    from sympy import Matrix, Rational
    A, b = data['A'], data['b']; d = len(data['start']); V = set(); active = {}
    for ids in combinations(range(len(A)), d):
        M = Matrix([[Rational(v) for v in A[i]] for i in ids])
        if not M.det(): continue
        x = tuple(Q(v) for v in M.inv()*Matrix([Rational(b[i]) for i in ids]))
        if old.feasible(A, b, x): V.add(x)
    V = sorted(V)
    for i, x in enumerate(V): active[i] = set(old.active_rows(A, b, x))
    G = [set() for _ in V]
    for i, j in combinations(range(len(V)), 2):
        shared = sorted(active[i]&active[j])
        if shared and Matrix([A[k] for k in shared]).rank() == d-1:
            G[i].add(j); G[j].add(i)
    start = V.index(tuple(data['start'])); end = V.index(tuple(data['target']['point']))
    dist = {start: 0}; todo = [start]
    for i in todo:
        for j in G[i]:
            if j not in dist: dist[j] = dist[i]+1; todo.append(j)
    require(len(dist) == len(V), 'independent original graph disconnected')
    return V, G, {'vertices': len(V), 'edges': sum(map(len, G))//2,
                   'independent_source_target_distance': dist[end],
                   'simple_vertices': sum(len(active[i]) == d for i in range(len(V)))}


def run_dimension(d):
    begin = time.monotonic(); data, packet = roof.execute_locked(d)
    comparison = roof.comparison_route(data); facets = roof.facet_anchors(data)
    full = roof.full_gain_comparator(data)
    require(full['verified']['edges'] == d and full['verified']['target_facets_lost'] == 0,
            'completed-gain test trajectory changed')
    # Every visited old vertex must satisfy every roof row strictly. The
    # recipe proof asserts this for all nonoptimal cube vertices; exhaust it
    # independently here, not merely for the prefix exposed by the selector.
    old_vertices_checked = 0
    for j in range(2**d-1):
        x, _ = roof.cube_vertex(d, j)
        require(all(dot(a, x) < z for a, z in zip(data['A'][2*d:], data['b'][2*d:])), 'roof deletes a required old vertex')
        old_vertices_checked += 1
    independent = None
    if d <= 4:
        V, G, independent = small_graph(data)
        for steps in (packet['steps'], comparison['steps'], full['certificate']['steps']):
            for s in steps:
                x, y = tuple(s['basis']['point']), tuple(s['to'])
                require(x in V and y in V and V.index(y) in G[V.index(x)], 'independent original graph rejects edge')
        require(independent['independent_source_target_distance'] == d, 'small shortest comparison changed')
    # Disable discovery: the stored packet is still audited purely by equations.
    inv = old.invert
    def forbidden(*args, **kwargs): raise AssertionError('auditor called inverse discovery')
    old.invert = forbidden
    try:
        replay = roof.audit_locked_route(data, packet['steps'])
        require(replay == packet['verified'], 'search-free audit disagrees')
        for s in comparison['steps']: roof.audit_any_edge(data['A'], data['b'], data['objective'], s)
    finally: old.invert = inv
    result = {**packet['verified'], 'comparison_route_edges': comparison['edges'],
              'completed_gain_edges': full['verified']['edges'],
              'completed_gain_target_facets_lost': full['verified']['target_facets_lost'],
              'genuine_facet_anchors': len(facets['relative_interior_points']),
              'all_retained_old_vertices_checked': old_vertices_checked,
              'independent_graph': independent, 'audit_with_inverse_disabled': True,
              'seconds': round(time.monotonic()-begin, 3)}
    if d <= 5:
        (ROOT/f'fixtures/target_roof_{d}_input.json').write_text(json.dumps(serial(data), indent=2)+'\n')
        (ROOT/f'fixtures/target_roof_{d}_routes.json').write_text(json.dumps(serial({'locked': packet, 'comparison': comparison, 'completed_gain': full, 'facets': facets}), indent=2)+'\n')
    return result


def selected_large():
    out = []
    for d in (16, 32, 64):
        data = roof.roof_input(d); checked = []
        for index in (0, 2**(d-1)-1, 2**d-3, 2**d-2):
            s = roof.phase_step(data, index); info = roof.audit_phase_step(data, s)
            expected_hit = index == 2**d-2
            require(bool(info['target_rows_after']) == expected_hit, 'large selected-step phase status')
            checked.append(index)
        out.append({'dimension': d, 'only_selected_phase_steps_executed': checked,
                    'all_dimension_formula_total_locked_edges': 2**d+d-2,
                    'all_dimension_formula_full_face_edges': 2**d-2,
                    'comparison_route_formula': d,
                    'comparison_route_executed_in_this_large_check': False,
                    'large_exponential_route_executed': False})
    return out


def negatives():
    data, packet = roof.execute_locked(4); names = []
    def reject(name, task):
        try: task()
        except (ValueError, KeyError, IndexError, TypeError, ZeroDivisionError): names.append(name)
        else: raise AssertionError('accepted forged claim '+name)
    def route_forgery(name, edit):
        c = deepcopy(packet['steps']); edit(c); reject(name, lambda: roof.audit_locked_route(data, c))
    route_forgery('omitted_first_step', lambda c: c.pop(0))
    route_forgery('omitted_tail', lambda c: c.pop())
    route_forgery('wrong_ray', lambda c: c[0].update(selected=3))
    route_forgery('nonmaximal_step', lambda c: c[0].update(length=c[0]['length']/2))
    route_forgery('false_blocker', lambda c: c[0].update(blocker=0))
    route_forgery('endpoint_as_diagonal', lambda c: c[0].update(to=data['target']['point']))
    route_forgery('inexact_step', lambda c: c[0].update(length=float(c[0]['length'])))
    route_forgery('false_inverse', lambda c: c[0]['basis']['directions'][0].__setitem__(0, 2))
    route_forgery('omitted_active_row', lambda c: c[0]['basis']['active'].pop())
    bad = deepcopy(data); bad['target']['weights'][0] = 0
    reject('nonstrict_target_weights', lambda: roof.audit_locked_route(bad, packet['steps']))
    bad = deepcopy(data); bad['objective'][0] += 1
    reject('wrong_target_objective', lambda: roof.audit_locked_route(bad, packet['steps']))
    bad = deepcopy(data); bad['A'][0][0] = -1.0
    reject('float_original_row', lambda: roof.audit_locked_route(bad, packet['steps']))
    bad = deepcopy(data); bad['start'] = [1]*4
    reject('different_start', lambda: roof.audit_locked_route(bad, packet['steps']))
    reject('phase_cap', lambda: roof.execute_phase(4, edge_cap=5))
    reject('route_cap', lambda: roof.execute_locked(4, edge_cap=15))
    reject('nonstrict_midpoint', lambda: roof.strict_midpoint(data['A'], data['b'], data['target']['point'], data['target']['point']))
    reject('invalid_dimension', lambda: roof.roof_input(True))
    return names


def main():
    p = argparse.ArgumentParser(); p.add_argument('--dimension', type=int); p.add_argument('--aux', action='store_true'); p.add_argument('--assemble', action='store_true')
    a = p.parse_args(); (ROOT/'research').mkdir(exist_ok=True); (ROOT/'fixtures').mkdir(exist_ok=True)
    dep = (ROOT/'scripts/simple_tangent_policy_audit.py').read_bytes()
    require(hashlib.sha1(b'blob '+str(len(dep)).encode()+b'\0'+dep).hexdigest() == EXPECTED_DEPENDENCY_BLOB,
            'old auditor no longer matches frozen unchanged source')
    dimensions = [a.dimension] if a.dimension is not None else list(range(2, 13)) if not (a.aux or a.assemble) else []
    for d in dimensions:
        r = run_dimension(d)
        (ROOT/f'research/TARGET_ROOF_STAGE_{d}.json').write_text(json.dumps(serial({'source_sha256': source_hashes(), 'result': r}), indent=2)+'\n')
        print(d, r['edges'], r['full_common_face_edges'], r['seconds'], flush=True)
    if a.aux or (a.dimension is None and not a.assemble):
        result = {'source_sha256': source_hashes(), 'selected_large': selected_large(), 'rejected': negatives()}
        (ROOT/'research/TARGET_ROOF_STAGE_aux.json').write_text(json.dumps(serial(result), indent=2)+'\n'); print('AUX PASS', flush=True)
    if a.assemble or (a.dimension is None and not a.aux):
        stages = [json.loads((ROOT/f'research/TARGET_ROOF_STAGE_{d}.json').read_text()) for d in range(2, 13)]
        aux = json.loads((ROOT/'research/TARGET_ROOF_STAGE_aux.json').read_text())
        require(all(s['source_sha256'] == source_hashes() for s in stages+[aux]), 'stale test source')
        results = [s['result'] for s in stages]
        totals = {k: sum(r[k] for r in results) for k in ('edges', 'first_target_facet_after_edges', 'full_common_face_edges', 'comparison_route_edges', 'completed_gain_edges', 'genuine_facet_anchors', 'all_retained_old_vertices_checked')}
        out = {'status': 'PASS', 'scope': 'Exact canonical normalized policy with adaptive target-face locking. Written all-d proof; no new Lean or platform verdict.',
               'source_sha256': source_hashes(), 'unchanged_auditor_git_blob': EXPECTED_DEPENDENCY_BLOB,
               'fully_executed_dimensions': list(range(2, 13)), 'totals': totals, 'results': results,
               'selected_large_checks': aux['selected_large'], 'negative_controls': aux['rejected'],
               'default_image_selector_replayed': False, 'exponential_diameter_claimed': False}
        (ROOT/'research/TARGET_ROOF_PHASE_CHECK.json').write_text(json.dumps(out, indent=2)+'\n')
        print('ASSEMBLED', totals, flush=True)

if __name__ == '__main__': main()
