#!/usr/bin/env python3
"""Exact portal optimization and cross-level ordinary-edge certificates.

Input: A,b,strict_point,positive_balance for a bounded full-dimensional SIMPLE
rational H-polytope, plus start_active/end_active row sets (or vertex indices).
The complete vertex set is recovered by exhaustive active-basis enumeration.
The optimizer is polynomial in this EXPLICIT incidence representation and its
walk horizon, not in the original H-description. Enumeration is capped and
never silently treated as complete. No floating point or network is used.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import json
from math import comb
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rational(x: Any) -> Q:
    require(not isinstance(x, bool) and isinstance(x, (int, str, Q)),
            'use exact integers/rational strings, never floats or booleans')
    return Q(x)


def dot(x, y):
    require(len(x) == len(y), 'vector dimension mismatch')
    return sum((a*b for a, b in zip(x, y)), Q(0))


def rank(rows):
    a = [list(r) for r in rows]
    if not a:
        return 0
    require(all(len(r) == len(a[0]) for r in a), 'ragged matrix')
    k = 0
    for j in range(len(a[0])):
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        v = a[k][j]
        a[k] = [x/v for x in a[k]]
        for i in range(k+1, len(a)):
            v = a[i][j]
            if v:
                a[i] = [x-v*y for x, y in zip(a[i], a[k])]
        k += 1
        if k == len(a):
            break
    return k


def solve(A, b):
    n = len(A)
    require(len(b) == n and all(len(r) == n for r in A), 'solve shape')
    a = [list(r)+[v] for r, v in zip(A, b)]
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            return None
        a[j], a[p] = a[p], a[j]
        v = a[j][j]
        a[j] = [x/v for x in a[j]]
        for i in range(n):
            if i != j:
                v = a[i][j]
                if v:
                    a[i] = [x-v*y for x, y in zip(a[i], a[j])]
    return tuple(r[-1] for r in a)


def distances(graph, targets):
    D = {i: 0 for i in targets}
    todo = deque(D)
    while todo:
        i = todo.popleft()
        for j in sorted(graph[i]):
            if j not in D:
                D[j] = D[i]+1
                todo.append(j)
    return D


def jsonable(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [jsonable(v) for v in x]
    return x


class NoCertificate(ValueError):
    """No tree exists within the specified finite search family, not a diameter lower bound."""


class ExactSimplePolytope:
    def __init__(self, data: dict[str, Any], max_bases: int = 20000):
        self.A = [[rational(x) for x in r] for r in data['A']]
        self.b = [rational(x) for x in data['b']]
        require(bool(self.A) and bool(self.A[0]), 'positive dimension required')
        self.n, self.d = len(self.A), len(self.A[0])
        require(len(self.b) == self.n and all(len(r) == self.d for r in self.A), 'A/b shape')
        o = [rational(x) for x in data['strict_point']]
        balance = [rational(x) for x in data['positive_balance']]
        require(len(o) == self.d and all(dot(a, o) < b for a, b in zip(self.A, self.b)),
                'strict interior point failed')
        require(len(balance) == self.n and all(x > 0 for x in balance), 'positive balance failed')
        require(all(sum((balance[i]*self.A[i][j] for i in range(self.n)), Q(0)) == 0
                    for j in range(self.d)), 'balance does not annihilate normals')
        require(rank(self.A) == self.d, 'normal rank does not certify boundedness')
        self.enumerated_bases = comb(self.n, self.d)
        require(type(max_bases) is int and self.enumerated_bases <= max_bases,
                'complete enumeration exceeds cap; no partial certificate is accepted')
        found = {}
        for base in combinations(range(self.n), self.d):
            x = solve([self.A[i] for i in base], [self.b[i] for i in base])
            if x is not None and all(dot(a, x) <= b for a, b in zip(self.A, self.b)):
                found[x] = frozenset(i for i in range(self.n) if dot(self.A[i], x) == self.b[i])
        require(bool(found), 'no vertices found')
        self.points = sorted(found)
        self.active = [found[x] for x in self.points]
        require(all(len(s) == self.d and rank([self.A[i] for i in s]) == self.d
                    for s in self.active), 'input is not simple in its given facet description')
        self.N = len(self.points)
        self.rows = [frozenset(v for v, s in enumerate(self.active) if i in s) for i in range(self.n)]
        require(all(self.affine_dimension(vs) == self.d-1 for vs in self.rows),
                'input contains a redundant or nonfacet row')
        self.graph = [set() for _ in self.points]
        for u in range(self.N):
            for v in range(u):
                if rank([self.A[i] for i in self.active[u] & self.active[v]]) == self.d-1:
                    self.graph[u].add(v)
                    self.graph[v].add(u)
        require(all(len(vs) == self.d for vs in self.graph), 'simple vertex degree mismatch')
        self.face = lru_cache(None)(self._face)
        self.carrier = lru_cache(None)(self._carrier)
        self.dp_state_visits = 0
        self.dp_transitions = 0
        self.tree_cache = {}

    def affine_dimension(self, vertices):
        vs = sorted(vertices)
        if not vs:
            return -1
        a = self.points[vs[0]]
        return rank([[x-y for x, y in zip(self.points[v], a)] for v in vs[1:]])

    def _face(self, vertices: frozenset[int]):
        require(bool(vertices), 'empty face')
        const = frozenset.intersection(*(self.active[v] for v in vertices))
        actual = frozenset(v for v in range(self.N) if const <= self.active[v])
        require(actual == vertices, 'vertex subset is not a complete exposed face')
        h = self.d-rank([self.A[i] for i in const])
        require(self.affine_dimension(vertices) == h, 'face dimension mismatch')
        rows = frozenset.union(*(self.active[v] for v in vertices))-const
        regions = {i: self.rows[i] & vertices for i in rows}
        require(all(self.affine_dimension(vs) == h-1 for vs in regions.values()), 'nonfacet face trace')
        G = {i: {j for j in rows if i != j and regions[i] & regions[j]} for i in rows}
        return {'vertices': vertices, 'constant': const, 'rows': rows, 'regions': regions,
                'graph': G, 'dimension': h, 'excess': len(rows)-h}

    def _carrier(self, u: int, v: int):
        common = self.active[u] & self.active[v]
        vs = frozenset(z for z in range(self.N) if common <= self.active[z])
        F = self.face(vs)
        return F

    def pair_cost(self, u: int, v: int, objective: str, slack: int = 0):
        if objective == 'recursive':
            return self.repair(u, v, slack, 'lookahead')['cost']
        F = self.carrier(u, v)
        return F['excess'] * (F['dimension'] if objective == 'potential' else 1)

    def endpoints(self, data):
        def get(prefix):
            if prefix+'_active' in data:
                S = data[prefix+'_active']
                require(isinstance(S, list) and all(type(i) is int and 0 <= i < self.n for i in S),
                        'invalid active-row endpoint')
                require(len(S) == len(set(S)), 'duplicate active-row endpoint')
                hits = [v for v, fs in enumerate(self.active) if fs == frozenset(S)]
                require(len(hits) == 1, 'active rows do not identify a unique vertex')
                return hits[0]
            v = data[prefix]
            require(type(v) is int and 0 <= v < self.N, 'invalid endpoint vertex index')
            return v
        return get('start'), get('end')

    def setup(self, start, end):
        F = self.carrier(start, end)
        available = F['rows']-self.active[start]
        require(len(available) == F['excess'], 'full availability identity failed')
        G = {i: F['graph'][i] & available for i in available}
        targets = available & self.active[end]
        D = distances(G, targets)
        return F, available, G, targets, D

    def optimize(self, start: int, end: int, slack: int = 0, objective: str = 'potential'):
        require(type(slack) is int and 0 <= slack <= 12, 'slack must be an integer in 0..12')
        require(objective in ('potential', 'excess', 'recursive'), 'unknown objective')
        require(start != end and end not in self.graph[start], 'use an edge/stationary leaf')
        F, available, G, targets, D = self.setup(start, end)
        INF = 10**30
        # A state includes the remaining number of REGION OCCURRENCES. No
        # visited mask: revisits are intentional and their slack is charged.
        @lru_cache(None)
        def dp(left, row, entry):
            self.dp_state_visits += 1
            if row not in D or D[row]+1 > left:
                return INF, ()
            best = (self.pair_cost(entry, end, objective, slack), ((row, entry, end),)) \
                if row in targets else (INF, ())
            if left > 1:
                for nxt in sorted(G[row]):
                    if nxt not in D or D[nxt]+1 > left-1:
                        continue
                    for portal in sorted(F['regions'][row] & F['regions'][nxt]):
                        self.dp_transitions += 1
                        value, tail = dp(left-1, nxt, portal)
                        candidate = (self.pair_cost(entry, portal, objective, slack)+value,
                                     ((row, entry, portal),)+tail)
                        if (candidate[0], len(candidate[1]), candidate[1]) < \
                           (best[0], len(best[1]), best[1]):
                            best = candidate
            return best
        best = None
        for old in sorted(self.graph[start] & F['vertices']):
            added = (self.active[old]-self.active[start]) & available
            require(len(added) == 1, 'initial edge does not enter exactly one available facet')
            row = next(iter(added))
            if row not in D:
                continue
            value, legs = dp(D[row]+1+slack, row, old)
            key = (value, len(legs), old, legs)
            if best is None or key < best:
                best = key
        require(best is not None and best[0] < INF, 'no admitted portal walk')
        plan = {'old_vertex': best[2], 'legs': [list(x) for x in best[3]],
                'slack_limit': slack, 'objective': objective, 'objective_value': best[0]}
        self.verify_plan(start, end, plan)
        return plan

    def verify_plan(self, start, end, plan):
        F, available, G, targets, D = self.setup(start, end)
        old = plan['old_vertex']; legs = plan['legs']; k = plan['slack_limit']
        require(type(old) is int and old in self.graph[start] & F['vertices'], 'false initial edge')
        require(type(k) is int and 0 <= k <= 12, 'invalid slack claim')
        require(plan['objective'] in ('excess', 'potential', 'recursive'), 'false objective name')
        require(isinstance(legs, list) and bool(legs), 'missing portal legs')
        previous = old
        for i, leg in enumerate(legs):
            require(isinstance(leg, list) and len(leg) == 3 and all(type(x) is int for x in leg),
                    'invalid portal leg')
            row, x, y = leg
            require(row in available and x in F['regions'][row] and y in F['regions'][row],
                    'portal lies outside its actual face')
            require(x == previous, 'broken portal chain')
            if i:
                require(row in G[legs[i-1][0]], 'consecutive rows are not distinct and adjacent')
            child = self.carrier(x, y)
            require(child['dimension'] < F['dimension'], 'child does not lie in a proper face')
            previous = y
        require(previous == end, 'wrong requested endpoint')
        added = (self.active[old]-self.active[start]) & available
        require(legs[0][0] in added, 'incorrect first cut row')
        actual_slack = len(legs)-1-D[legs[0][0]]
        require(0 <= actual_slack <= k, 'walk exceeds independently computed distance/slack')
        labels = [leg[0] for leg in legs]
        load = []
        for i, (row, x, y) in enumerate(legs):
            contacts = sum(j == row or row in G[j] for j in available)
            require(self.carrier(x, y)['excess'] <= contacts, 'pointwise carrier saving failed')
            load.append(contacts)
        for j in available:
            indices = [i for i, row in enumerate(labels) if row == j or row in G[j]]
            require(len(indices) <= k+3 and (not indices or max(indices)-min(indices) <= k+2),
                    'occurrence contact-window theorem failed')
        children = [self.carrier(x, y) for _, x, y in legs]
        mass = sum(c['excess'] for c in children)
        child_potential = sum(c['dimension']*c['excess'] for c in children)
        require(mass <= sum(load) <= (k+3)*len(available), 'near-geodesic aggregate failed')
        objective = child_potential if plan['objective'] == 'potential' else mass
        require(type(plan['objective_value']) is int and plan['objective_value'] >= 0, 'invalid objective value')
        if plan['objective'] != 'recursive':
            require(plan['objective_value'] == objective, 'forged objective value')
        return {'parent_dimension': F['dimension'], 'parent_excess': F['excess'],
                'carrier_mass': mass, 'child_potential': child_potential,
                'local_charge': max(0, 1+child_potential-F['dimension']*F['excess']),
                'actual_slack': actual_slack, 'region_occurrences': len(legs),
                'distinct_regions': len(set(labels)), 'contact_sum': sum(load),
                'mass_cap': (k+3)*len(available)}

    def exhaustive_optimum(self, start, end, slack=0, objective='potential', max_walks=200000):
        """Independent optimality audit: enumerate label walks, then solve
        the portal chain in a different order. This does not call optimize()."""
        require(objective in ('potential', 'excess'), 'exhaustive audit accepts only static objectives')
        F, available, G, targets, D = self.setup(start, end)
        best = None; walks = 0
        for old in sorted(self.graph[start] & F['vertices']):
            first = next(iter((self.active[old]-self.active[start]) & available))
            if first not in D:
                continue
            limit = D[first]+1+slack
            def visit(labels):
                nonlocal best, walks
                row = labels[-1]
                if row in targets:
                    walks += 1
                    require(walks <= max_walks, 'exhaustive audit cap reached; no optimum asserted')
                    current = {old: 0}
                    for a, b in zip(labels, labels[1:]):
                        nxt = {}
                        for y in F['regions'][a] & F['regions'][b]:
                            nxt[y] = min(v+self.pair_cost(x, y, objective) for x, v in current.items())
                        current = nxt
                    value = min(v+self.pair_cost(x, end, objective) for x, v in current.items())
                    if best is None or value < best:
                        best = value
                if len(labels) < limit:
                    for nxt in sorted(G[row]):
                        if nxt in D and D[nxt] <= limit-len(labels)-1:
                            visit(labels+[nxt])
            visit([first])
        require(best is not None, 'no admissible exhaustive walk')
        return best, walks

    def optimize_conservative(self, start, end, slack):
        """Exact search for locally nonincreasing dimension*excess potential.
        This knapsack state accounts for the WHOLE sum of sibling potentials.
        Child zero-charge feasibility is solved recursively at lower dimension.
        """
        require(type(slack) is int and 0 <= slack <= 12, 'invalid conservative slack')
        F, available, G, targets, D = self.setup(start, end)
        budget = F['dimension']*F['excess']-1
        INF = 10**30
        @lru_cache(None)
        def child(x, y):
            try:
                cert = self.repair(x, y, slack, 'conservative')
                return cert['cost']
            except NoCertificate:
                return INF
        @lru_cache(None)
        def dp(left, row, entry, remaining):
            self.dp_state_visits += 1
            if row not in D or D[row]+1 > left:
                return INF, ()
            best = (INF, ())
            terminal = self.pair_cost(entry, end, 'potential')
            if row in targets and terminal <= remaining:
                value = child(entry, end)
                if value < INF:
                    best = value, ((row, entry, end),)
            if left > 1:
                for nxt in sorted(G[row]):
                    if nxt not in D or D[nxt]+1 > left-1:
                        continue
                    for portal in sorted(F['regions'][row] & F['regions'][nxt]):
                        potential = self.pair_cost(entry, portal, 'potential')
                        if potential > remaining:
                            continue
                        value = child(entry, portal)
                        if value >= INF:
                            continue
                        self.dp_transitions += 1
                        tail_value, tail = dp(left-1, nxt, portal, remaining-potential)
                        candidate = value+tail_value, ((row, entry, portal),)+tail
                        if (candidate[0], len(candidate[1]), candidate[1]) < \
                           (best[0], len(best[1]), best[1]):
                            best = candidate
            return best
        best = None
        for old in sorted(self.graph[start] & F['vertices']):
            first = next(iter((self.active[old]-self.active[start]) & available))
            if first not in D:
                continue
            value, legs = dp(D[first]+1+slack, first, old, budget)
            key = value, len(legs), old, legs
            if best is None or key < best:
                best = key
        if best is None or best[0] >= INF:
            raise NoCertificate('no zero-charge tree within the admitted detour family')
        plan = {'old_vertex': best[2], 'legs': [list(x) for x in best[3]],
                'slack_limit': slack, 'objective': 'recursive', 'objective_value': best[0],
                'policy': 'zero_charge'}
        require(self.verify_plan(start, end, plan)['local_charge'] == 0,
                'conservative optimizer violated its budget')
        return plan

    def repair(self, start, end, slack=0, mode='conservative'):
        require(mode in ('potential', 'lookahead', 'conservative'), 'unknown recursive mode')
        key = start, end, slack, mode
        if key in self.tree_cache:
            if self.tree_cache[key] is None:
                raise NoCertificate('no zero-charge tree within the admitted detour family')
            return self.tree_cache[key]
        F = self.carrier(start, end)
        if start == end:
            out = {'kind': 'stationary', 'start': start, 'end': end,
                   'dimension': 0, 'excess': 0, 'cost': 0, 'charge': 0}
        elif end in self.graph[start]:
            out = {'kind': 'edge', 'start': start, 'end': end,
                   'dimension': 1, 'excess': 1, 'cost': 1, 'charge': 0}
        else:
            try:
                plan = self.optimize_conservative(start, end, slack) if mode == 'conservative' else \
                    self.optimize(start, end, slack, 'recursive' if mode == 'lookahead' else 'potential')
            except NoCertificate:
                self.tree_cache[key] = None
                raise
            metrics = self.verify_plan(start, end, plan)
            children = [self.repair(x, y, slack, mode) for _, x, y in plan['legs']]
            out = {'kind': 'node', 'start': start, 'end': end, 'dimension': F['dimension'],
                   'excess': F['excess'], 'cost': 1+sum(c['cost'] for c in children),
                   'charge': metrics['local_charge']+sum(c['charge'] for c in children),
                   'plan': plan, 'children': children}
        self.tree_cache[key] = out
        return out

    def verify_repair(self, start, end, cert):
        """Independent certificate verifier: never calls discovery or optimizer."""
        F = self.carrier(start, end)
        require(cert['start'] == start and cert['end'] == end, 'certificate endpoints changed')
        require(type(cert['dimension']) is int and cert['dimension'] == F['dimension'], 'false dimension')
        require(type(cert['excess']) is int and cert['excess'] == F['excess'], 'false carrier excess')
        kind = cert['kind']
        if kind == 'stationary':
            require(start == end, 'nonstationary zero leaf')
            route = [start]; cost = charge = nodes = 0; leaves = 1
        elif kind == 'edge':
            require(end in self.graph[start], 'claimed leaf is not an actual ordinary edge')
            route = [start, end]; cost = leaves = 1; charge = nodes = 0
        else:
            require(kind == 'node', 'unknown certificate constructor')
            metrics = self.verify_plan(start, end, cert['plan'])
            legs, children = cert['plan']['legs'], cert['children']
            require(len(legs) == len(children), 'children do not match actual portal occurrences')
            route = [start, cert['plan']['old_vertex']]
            cost = nodes = 1; charge = metrics['local_charge']; leaves = 0
            for (_, x, y), child in zip(legs, children):
                got = self.verify_repair(x, y, child)
                require(route[-1] == got['route'][0], 'child route does not concatenate')
                route += got['route'][1:]
                cost += got['cost']; charge += got['charge']; nodes += got['nodes']; leaves += got['leaves']
            if cert['plan']['objective'] == 'recursive':
                require(cert['plan']['objective_value'] == cost-1, 'forged recursive objective')
            if cert['plan'].get('policy') == 'zero_charge':
                require(charge == 0, 'nonzero charge in purported conservative tree')
        require(type(cert['cost']) is int and cert['cost'] == cost, 'forged assembled cost')
        require(type(cert['charge']) is int and cert['charge'] == charge, 'forged cumulative charge')
        require(len(route)-1 == cost and route[0] == start and route[-1] == end, 'assembled route mismatch')
        require(all(y in self.graph[x] for x, y in zip(route, route[1:])), 'assembled non-edge')
        require(cost <= F['dimension']*F['excess']+charge, 'telescoping bound failed')
        return {'route': route, 'cost': cost, 'charge': charge, 'nodes': nodes, 'leaves': leaves,
                'potential_bound': F['dimension']*F['excess']+charge}


def cyclic_input(n: int, d: int):
    """An exact centered moment-curve polar. No Gale criterion is trusted:
    its vertices are found from ALL active bases by the independent model."""
    require(n >= d+1 and d >= 2, 'cyclic fixture size')
    points = [[Q(i)**j for j in range(1, d+1)] for i in range(n)]
    center = [sum(p[j] for p in points)/n for j in range(d)]
    return {'A': [[p[j]-center[j] for j in range(d)] for p in points],
            'b': [1]*n, 'strict_point': [0]*d, 'positive_balance': [1]*n}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--slack', type=int, default=2)
    parser.add_argument('--mode', choices=('potential','lookahead','conservative'), default='conservative')
    parser.add_argument('--max-bases', type=int, default=20000)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text())
        P = ExactSimplePolytope(data, args.max_bases)
        start, end = P.endpoints(data)
        cert = P.repair(start, end, args.slack, args.mode)
        verified = P.verify_repair(start, end, cert)
        out = {'certificate': cert, 'verified': verified, 'complete_vertex_count': P.N,
               'enumerated_bases': P.enumerated_bases,
               'route_coordinates': [P.points[i] for i in verified['route']],
               'scope': 'Exact finite polyhedral/edge checks; not a Lean or Prove2Me verdict.'}
        text = json.dumps(jsonable(out), indent=2, sort_keys=True)+'\n'
        if args.output:
            args.output.write_text(text)
        else:
            print(text)
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        parser.exit(2, f'Certificate rejected: {exc}\n')


if __name__ == '__main__':
    main()
