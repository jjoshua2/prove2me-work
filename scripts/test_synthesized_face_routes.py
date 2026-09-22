#!/usr/bin/env python3
"""Exact supporting tests for synthesized, face-local normalized routing.

The producer synthesizes each denominator from the COMPLETE planned face,
then uses subset dynamic programming. The consumer independently enumerates
all eligible row orders and audits every normalizer's exhaustive/sign-bound
certificate and every whole original edge. This is not Lean-extracted code.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import normalizer_synthesis as ns
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old
import test_normalized_slack_routes as previous
import test_normalizer_synthesis as cases

need = ns.need


class Data:
    def __init__(self, model, rows):
        self.model = model; self.rows = rows; self.V = model['vertices']
        self.d = len(self.V[0]); self.active = [old.active(rows, x) for x in self.V]
        self.certificates = {}; self.checked = {}; self.replay = False
        old.validate_h(model, rows)

    @lru_cache(None)
    def face(self, H):
        return tuple(i for i, active in enumerate(self.active) if set(H) <= active)

    def key(self, v, H, j):
        return f'{v}:{",".join(map(str, sorted(H)))}:{j}'

    def entry(self, v, H, j):
        key = self.key(v, H, j)
        if key not in self.certificates:
            need(not self.replay, 'missing synthesized-face certificate')
            F = self.face(tuple(sorted(H))); need(v in F, 'target absent from face')
            row = self.rows[j]; C = [self.V[i] for i in F]
            s = [row[-1] - g.dot(row[:-1], x) for x in C]
            cert = ns.optimize(C, s, F.index(v))
            self.certificates[key] = dict(target=v, rows=sorted(H), row=j,
                                         vertices=list(F), synthesis=cert)
        return self.certificates[key]

    def audit_entry(self, v, H, j):
        key = self.key(v, H, j)
        if key in self.checked:
            return self.checked[key]
        cert = self.entry(v, H, j); F = self.face(tuple(sorted(H)))
        need(cert['target'] == v and cert['rows'] == sorted(H) and cert['row'] == j,
             'changed face/row binding')
        need(cert['vertices'] == list(F), 'incomplete actual face vertices')
        need(cert['synthesis']['anchor'] == F.index(v), 'wrong anchor')
        row = self.rows[j]; C = [self.V[i] for i in F]
        s = [row[-1] - g.dot(row[:-1], x) for x in C]
        stats = ns.audit(C, s, cert['synthesis'])
        out = cert['synthesis']; slope = tuple(map(Q, out['records'][out['best']]['slope']))
        self.checked[key] = (out['minimum'] - 1, slope, stats)
        return self.checked[key]

    def charge(self, v, H, j):
        out = self.entry(v, H, j)['synthesis']
        return out['minimum'] - 1

    def ratio(self, v, H, j, x):
        out = self.entry(v, H, j)['synthesis']
        E = tuple(map(Q, out['records'][out['best']]['slope']))
        q = 1 + g.dot(E, tuple(a - b for a, b in zip(self.V[x], self.V[v])))
        need(q > 0, 'nonpositive reached denominator')
        row = self.rows[j]
        return (row[-1] - g.dot(row[:-1], self.V[x])) / q, E


def select(D, u, v):
    G = D.active[u] & D.active[v]; T = D.active[v] - G
    cap = min(D.d, len(D.rows) - D.d)
    @lru_cache(None)
    def visit(chosen):
        H = G | set(chosen)
        if g.rank([D.rows[j][:-1] for j in sorted(H)]) == D.d:
            return (0, ())
        if len(chosen) == cap:
            return None
        options = []
        for j in sorted(T - set(chosen)):
            tail = visit(tuple(sorted((*chosen, j))))
            if tail is not None:
                options.append((D.charge(v, H, j) + tail[0], (j,) + tail[1]))
        return min(options, key=lambda item: (item[0], len(item[1]), item[1])) if options else None
    result = visit(()); need(result is not None, 'no determining flag')
    return list(result[1]), result[0], G, T


def produce(D, u, v):
    J, budget, G, T = select(D, u, v); H = set(G); path = [u]; phases = []; edges = []
    for j in J:
        lo = len(path) - 1; c = D.entry(v, H, j)
        while j not in D.active[path[-1]]:
            x = path[-1]; r, E = D.ratio(v, H, j, x)
            objective = tuple(a + r * e for a, e in zip(D.rows[j][:-1], E))
            locks = D.active[x] & D.active[v]
            y, edge = g.improving_edge(D.model, frozenset(D.face(tuple(sorted(locks)))), x, objective)
            need(H <= D.active[y] and locks <= D.active[y], 'lost target lock')
            need(D.ratio(v, H, j, y)[0] < r, 'ratio did not decrease')
            edges.append(dict(row=j, entry_ratio=r, edge=edge)); path.append(y)
            need(len(path) - 1 - lo <= c['synthesis']['minimum'] - 1, 'phase exceeds spectrum')
        phases.append(dict(row=j, entry_rows=sorted(H), start=lo, end=len(path)-1,
                           charge=c['synthesis']['minimum']-1))
        H.add(j)
    need(path[-1] == v, 'determining flag did not reach target')
    return dict(u=u, v=v, shared=sorted(G), missing=sorted(T), order=J, budget=budget,
                path=path, phases=phases, edges=edges)


def consume(D, c):
    u, v = c['u'], c['v']; need(0 <= u < len(D.V) and 0 <= v < len(D.V), 'bad endpoints')
    G = D.active[u] & D.active[v]; T = D.active[v] - G; J = c['order']; cap = min(D.d, len(D.rows)-D.d)
    need(c['shared'] == sorted(G) and c['missing'] == sorted(T), 'bad original row binding')
    need(len(J) == len(set(J)) and set(J) <= T and len(J) <= cap, 'ineligible flag')
    need(previous.exact_rank([D.rows[j][:-1] for j in sorted(G | set(J))], D.d) == D.d,
         'nontrivial determining kernel')
    # Exhaust every eligible order independently of the producer's DP.
    best = raw_best = global_best = None; candidates = 0
    for k in range(min(cap, len(T)) + 1):
        for R in permutations(sorted(T), k):
            if previous.exact_rank([D.rows[j][:-1] for j in sorted(G | set(R))], D.d) != D.d:
                continue
            H = set(G); cost = raw = glob = 0
            for j in R:
                w, _, _ = D.audit_entry(v, H, j); cost += w
                F = D.face(tuple(sorted(H)))
                raw += len({g.dot(D.rows[j][:-1], D.V[x]) for x in F}) - 1
                glob += D.audit_entry(v, set(), j)[0]
                H.add(j)
            best = cost if best is None else min(best, cost)
            raw_best = raw if raw_best is None else min(raw_best, raw)
            global_best = glob if global_best is None else min(global_best, glob)
            candidates += 1
    need(candidates and c['budget'] == best, 'wrong minimum synthesized local budget')
    need(best <= raw_best and best <= global_best, 'failed previous-budget dominance')
    p = c['path']; need(p and p[0] == u and p[-1] == v and all(0 <= x < len(D.V) for x in p), 'wrong route')
    need(len(c['edges']) == len(p)-1 and len(c['phases']) == len(J), 'bad record count')
    H = set(G); cursor = total = multi = nonacq = changes = zero_phases = 0
    for j, phase in zip(J, c['phases']):
        w, E, _ = D.audit_entry(v, H, j); lo, hi = phase['start'], phase['end']
        need(phase['row'] == j and phase['entry_rows'] == sorted(H) and phase['charge'] == w, 'wrong phase charge')
        need(lo == cursor and lo <= hi < len(p) and hi-lo <= w, 'bad phase partition')
        need(j in D.active[p[hi]] and all(H <= D.active[p[t]] for t in range(lo,hi+1)), 'left face/not acquired')
        previous_obj = None
        for t in range(lo, hi):
            x, y = p[t:t+2]; r, slope = D.ratio(v, H, j, x); record = c['edges'][t]
            objective = tuple(a + r*e for a,e in zip(D.rows[j][:-1], E))
            need(record['row'] == j and Q(record['entry_ratio']) == r, 'wrong linearization ratio')
            need(tuple(map(Q,record['edge']['objective'])) == objective, 'wrong linear objective')
            need(D.ratio(v,H,j,y)[0] < r, 'nondecreasing normalized slack')
            before = D.active[x] & D.active[v]; after = D.active[y] & D.active[v]
            need(before <= after, 'target equality lost')
            edge = record['edge']
            need(edge['u'] == x and edge['v'] == y and set(edge['face']) == set(D.face(tuple(sorted(before)))), 'wrong original lock face')
            g.verify_record(D.model, edge)
            nonacq += before == after
            changes += previous_obj is not None and previous_obj != objective; previous_obj = objective
        multi += hi-lo > 1; zero_phases += hi == lo; total += w; cursor = hi; H.add(j)
    need(cursor == len(p)-1 and total == c['budget'] and len(p)-1 <= total, 'unaccounted original edges')
    return dict(candidate_orders=candidates, raw_local_minimum=raw_best, global_normalized_minimum=global_best,
                multi_edge_phases=multi, nonacquiring_steps=nonacq, objective_changes=changes, zero_edge_phases=zero_phases)


def corruptions(D, good):
    controls = []
    edits = [('false optimal budget', lambda c: c.update(budget=c['budget']+1)),
             ('repeated selected row', lambda c: c['order'].append(c['order'][0])),
             ('wrong planned face', lambda c: c['phases'][0]['entry_rows'].append(c['order'][0])),
             ('uncharged phase', lambda c: c['phases'][0].update(charge=0)),
             ('stationary edge', lambda c: c['edges'][0]['edge'].update(v=c['path'][0])),
             ('wrong objective', lambda c: c['edges'][0]['edge'].update(objective=[0]*D.d)),
             ('wrong entry ratio', lambda c: c['edges'][0].update(entry_ratio=-1))]
    for name, edit in edits:
        c = deepcopy(good); edit(c)
        try: consume(D, c)
        except (ValueError,AssertionError): controls.append(dict(case=name,rejected=True))
        else: raise AssertionError('accepted corruption '+name)
    c = deepcopy(good); H = set(c['phases'][0]['entry_rows']); j = c['order'][0]; v = c['v']
    key = D.key(v,H,j)
    for name, edit in [('omitted actual face vertex', lambda e: e['vertices'].pop()),
                       ('false spectrum optimum', lambda e: e['synthesis'].update(minimum=0)),
                       ('false feasibility witness', lambda e: e['synthesis']['records'][e['synthesis']['best']].update(slope=[0]*D.d))]:
        entry = deepcopy(D.certificates[key]); saved = deepcopy(entry)
        edit(entry); D.certificates[key] = entry; D.checked.clear()
        try: consume(D,c)
        except (ValueError,AssertionError): controls.append(dict(case=name,rejected=True))
        else:
            # A zero slope can be legitimate; corrupt its displayed denominators instead.
            entry['synthesis']['records'][entry['synthesis']['best']]['denominators']=[-1]*len(entry['vertices'])
            try: consume(D,c)
            except (ValueError,AssertionError): controls.append(dict(case=name,rejected=True))
            else: raise AssertionError('accepted corruption '+name)
        finally: D.certificates[key]=saved; D.checked.clear()
    return controls


def run(name, points):
    model = g.reference(points); rows = old.h_rows(model); D = Data(model,rows); routes=[]; controls=[]
    totals=dict(routes=0,edges=0,shortest_edges=0,nonshortest_routes=0,candidate_orders=0,
                better_than_raw_local=0,better_than_global_normalized=0,better_than_both=0,
                multi_edge_phases=0,nonacquiring_steps=0,objective_changes=0,zero_edge_phases=0)
    examples=[]
    for u in range(len(D.V)):
        distances=old.distances(model,u)
        for v in range(len(D.V)):
            c=produce(D,u,v); r=consume(D,c); routes.append(c); L=len(c['path'])-1
            totals['routes']+=1;totals['edges']+=L;totals['shortest_edges']+=distances[v]
            totals['nonshortest_routes']+=L>distances[v]
            betterraw=c['budget']<r['raw_local_minimum'];betterglob=c['budget']<r['global_normalized_minimum']
            totals['better_than_raw_local']+=betterraw;totals['better_than_global_normalized']+=betterglob
            totals['better_than_both']+=betterraw and betterglob
            for k in ('candidate_orders','multi_edge_phases','nonacquiring_steps','objective_changes','zero_edge_phases'):totals[k]+=r[k]
            if betterraw and betterglob and len(examples)<3: examples.append(dict(source=u,target=v,budget=c['budget'],raw_local=r['raw_local_minimum'],global_normalized=r['global_normalized_minimum']))
            if name=='projective_cube2' and L and not controls and c['budget']:controls=corruptions(D,c)
    records=json.loads(json.dumps(ns.encoded(D.certificates))); saved_routes=json.loads(json.dumps(ns.encoded(routes)))
    D2=Data(model,rows);D2.certificates=records;D2.replay=True
    saved=(ns.optimize,ns.solve_system,ns.eliminate_equalities,ns.strict_feasible,g.improving_edge,globals()['select'],globals()['produce'])
    def disabled(*args,**kwargs): raise RuntimeError('producer disabled')
    ns.optimize=ns.solve_system=ns.eliminate_equalities=ns.strict_feasible=g.improving_edge=globals()['select']=globals()['produce']=disabled
    try:
        for c in saved_routes:consume(D2,c)
    finally:ns.optimize,ns.solve_system,ns.eliminate_equalities,ns.strict_feasible,g.improving_edge,globals()['select'],globals()['produce']=saved
    stats=[t[2] for t in D2.checked.values()]
    nonpositive_outside=0
    for entry in records.values():
        out=entry['synthesis'];E=tuple(map(Q,out['records'][out['best']]['slope'])); v=entry['target']
        if any(1+g.dot(E,tuple(a-b for a,b in zip(x,D.V[v])))<=0 for x in D.V):nonpositive_outside+=1
    report=dict(name=name,dimension=D.d,vertices=len(D.V),original_rows=len(rows),**totals,
                normalizers_checked=len(stats),systems=sum(s['systems'] for s in stats),
                positive_systems=sum(s['positive_systems'] for s in stats),excluded_systems=sum(s['excluded_systems'] for s in stats),
                locally_positive_but_not_globally_positive=nonpositive_outside,strict_improvement_examples=examples)
    fixture=dict(name=name,points=model['points'],rows=rows,normalizers=records,routes=saved_routes)
    return report,fixture,controls


def models():
    return cases.models()+[('hexagonal_pyramid',[(x,y,0) for x,y in [(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]]+[(1,1,2)])]


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',required=True,type=Path);ap.add_argument('--only',default='all')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);reports=[];fixtures=[];controls=[]
    for name,points in models():
        if a.only not in ('all',name):continue
        r,f,c=run(name,points);reports.append(r);fixtures.append(f);controls.extend(c);print(json.dumps(r),flush=True)
    (a.out/'report.json').write_text(json.dumps(dict(kind='exact_supporting_tests_not_Lean',models=reports,controls=controls),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(ns.encoded(fixtures),indent=2)+'\n')

if __name__=='__main__': main()
