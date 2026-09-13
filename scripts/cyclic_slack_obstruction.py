#!/usr/bin/env python3
"""Cyclic-polar certificates for the failure of uniformly bounded portal slack.

The facet description is the centered moment-curve polar in EVEN dimension.
Its complete incidence model follows from the proved matching/sign criterion
in the companion note. Optional exact H-basis enumeration crosschecks that
criterion in small tests. Large explicit routes do NOT enumerate vertices.

The root optimizer reuses #208's specified first-edge/available-facet family.
No conclusion about all possible radial/basis-star certificates is asserted.
All arithmetic is integral or rational; no numerical zero threshold is used.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import json
from math import comb
from pathlib import Path
from typing import Iterable
from portal_detour_optimizer import ExactSimplePolytope, dot, rank, require, jsonable, rational


def dimensions(n: int, d: int) -> None:
    require(type(n) is int and type(d) is int and d >= 4 and d % 2 == 0 and n > d,
            'require integers n>d>=4 with d even')


def cycle_distance(n: int, i: int, j: int) -> int:
    require(0 <= i < n and 0 <= j < n, 'row index outside cycle')
    z = abs(i-j)
    return min(z, n-z)


def matching_for(n: int, active: Iterable[int]) -> tuple[tuple[int, int], ...]:
    S = set(active)
    require(S and len(S) < n and len(S) % 2 == 0, 'invalid matching support size')
    require(all(type(i) is int and 0 <= i < n for i in S), 'invalid matching row')
    # Cut the cycle after a missing label; every remaining occupied run must
    # have even length. Pair consecutive labels in each run.
    start = next(i for i in range(n) if i not in S)
    run = []; edges = []
    for k in range(1, n+1):
        i = (start+k) % n
        if i in S:
            run.append(i)
        else:
            require(len(run) % 2 == 0, 'support contains an odd occupied run')
            edges.extend((run[j], run[j+1]) for j in range(0, len(run), 2))
            run = []
    require(not run, 'cycle cut did not close')
    return tuple(edges)


def extend_matching(n: int, partial: Iterable[tuple[int, int]], row: int):
    """Add one edge by an alternating path, retaining EVERY covered label.
    The result also covers the requested row, even when it starts unmatched.
    This is a constructive witness that a free domino makes carrier excess e.
    """
    M = {frozenset(edge) for edge in partial}
    require(0 <= row < n, 'invalid requested row')
    mate = {}
    for edge in M:
        require(len(edge) == 2, 'loop in matching')
        a, b = sorted(edge)
        require(cycle_distance(n, a, b) == 1 and a not in mate and b not in mate,
                'not a matching of cycle edges')
        mate[a] = b; mate[b] = a
    covered = set(mate)
    require(len(covered)+2 < n+1, 'not enough unmatched vertices')
    start = row if row not in covered else next(i for i in range(n) if i not in covered)
    path = [start]
    while True:
        nxt = (path[-1]+1) % n
        require(nxt not in path, 'alternating path returned before a free endpoint')
        path.append(nxt)
        if nxt not in mate:
            break
        partner = mate[nxt]
        require(partner == (nxt+1) % n and partner not in path, 'alternation failed')
        path.append(partner)
    out = set(M)
    for j in range(1, len(path)-1, 2):
        out.remove(frozenset((path[j], path[j+1])))
    for j in range(0, len(path)-1, 2):
        out.add(frozenset((path[j], path[j+1])))
    support = set().union(*out)
    require(len(out) == len(M)+1 and len(support) == 2*len(out), 'augmentation size failed')
    require(covered <= support and row in support, 'lost old coverage or requested row')
    return tuple(tuple(sorted(edge)) for edge in sorted(out, key=lambda x: sorted(x)))


def all_supports(n: int, d: int, max_vertices: int = 10000):
    dimensions(n, d); r = d//2
    predicted = n*comb(n-r, r)//(n-r)
    require(type(max_vertices) is int and predicted <= max_vertices,
            'complete incidence enumeration exceeds cap; no partial model is returned')
    out = set()
    for chosen in combinations(range(n), r):
        S = frozenset(j for i in chosen for j in (i, (i+1) % n))
        if len(S) == d:
            out.add(S)
    require(len(out) == predicted, 'matching-count formula mismatch')
    return sorted(out, key=lambda x: tuple(sorted(x)))


class CyclicPortalModel(ExactSimplePolytope):
    """Complete matching-derived incidence model; not arbitrary supplied data."""
    def __init__(self, n: int, d: int = 4, max_vertices: int = 10000):
        dimensions(n, d); self.n = n; self.d = d
        self.active = all_supports(n, d, max_vertices); self.N = len(self.active)
        self.index = {s: i for i, s in enumerate(self.active)}
        self.rows = [frozenset(v for v, S in enumerate(self.active) if j in S) for j in range(n)]
        self.graph = [set() for _ in self.active]
        ridges = {}
        for v, S in enumerate(self.active):
            for j in S:
                ridges.setdefault(S-{j}, []).append(v)
        for hits in ridges.values():
            require(len(hits) == 2, 'ridge must lie in two facets of the cyclic polytope')
            a, b = hits; self.graph[a].add(b); self.graph[b].add(a)
        require(all(len(g) == d for g in self.graph), 'dual graph is not simple of degree d')
        self.face = lru_cache(None)(self._face); self.carrier = lru_cache(None)(self._carrier)
        self.dp_state_visits = 0; self.dp_transitions = 0; self.tree_cache = {}

    def _face(self, vertices):
        common = frozenset.intersection(*(self.active[v] for v in vertices))
        actual = frozenset(v for v, S in enumerate(self.active) if common <= S)
        require(actual == vertices, 'incomplete exposed face')
        h = self.d-len(common)
        rows = frozenset.union(*(self.active[v] for v in vertices))-common
        regions = {j: self.rows[j] & vertices for j in rows}
        G = {j: {k for k in rows if k != j and regions[j] & regions[k]} for j in rows}
        return {'vertices': vertices, 'constant': common, 'rows': rows, 'regions': regions,
                'graph': G, 'dimension': h, 'excess': len(rows)-h}

    def block_endpoints(self):
        require(self.n % 2 == 0 and self.n//2 > self.d, 'need separated opposite blocks')
        return self.index[frozenset(range(self.d))], self.index[frozenset(range(self.n//2, self.n//2+self.d))]

    def audit_pair(self, u: int, v: int):
        A, B = self.active[u], self.active[v]; K = A & B; e = self.n-self.d
        F = self.carrier(u, v); mass = F['excess']
        require(mass <= e, 'carrier excess exceeds the parent')
        witness_count = 0
        for S in (A, B):
            M = matching_for(self.n, S)
            free = [edge for edge in M if not set(edge) & K]
            if free:
                partial = tuple(edge for edge in M if edge != free[0])
                for row in range(self.n):
                    full = extend_matching(self.n, partial, row)
                    T = frozenset(x for edge in full for x in edge)
                    require(T in self.index and K <= T and row in T, 'false carrier-row witness')
                    witness_count += 1
                require(mass == e, 'a free domino did not give full carrier excess')
        if mass < e:
            for S, T in ((A, B), (B, A)):
                require(all(any(cycle_distance(self.n, i, j) <= 1 for j in T) for i in S),
                        'light transition moves a row by more than one')
        return witness_count


def moment_description(n: int, d: int):
    dimensions(n, d)
    mu = [sum(Q(i)**j for i in range(n))/n for j in range(1, d+1)]
    return {'A': [[Q(i)**j-mu[j-1] for j in range(1, d+1)] for i in range(n)],
            'b': [1]*n, 'strict_point': [0]*d, 'positive_balance': [1]*n}


def vertex_from_roots(n: int, d: int, active: Iterable[int]):
    """Exact primal-dual slack certificate; no other vertices are enumerated."""
    dimensions(n, d); S = frozenset(active)
    require(len(S) == d, 'need d distinct active rows'); matching_for(n, S)
    coefficients = [1]
    for i in sorted(S):
        new = [0]*(len(coefficients)+1)
        for j, c in enumerate(coefficients):
            new[j] -= i*c; new[j+1] += c
        coefficients = new
    def evaluate(t):
        out = 0
        for c in reversed(coefficients): out = out*t+c
        return out
    values = [evaluate(i) for i in range(n)]
    nonzero = next(x for x in values if x)
    sign = 1 if nonzero > 0 else -1
    coefficients = [sign*c for c in coefficients]; values = [sign*v for v in values]
    require(all(v >= 0 for v in values) and {i for i,v in enumerate(values) if v == 0} == S,
            'root polynomial is not a supporting slack polynomial')
    mean = Q(sum(values), n)
    require(mean > 0, 'normalization has no positive mean slack')
    point = tuple(-Q(c)/mean for c in coefficients[1:])
    return point, {'active': sorted(S), 'polynomial_coefficients': coefficients,
                   'mean_polynomial_value': mean}


def verify_vertex(n: int, d: int, point, cert, description=None):
    data = moment_description(n, d) if description is None else description
    S = frozenset(cert['active']); require(len(S) == d and all(type(i) is int for i in S), 'false active count')
    coefficients = cert['polynomial_coefficients']; mean = rational(cert['mean_polynomial_value'])
    require(all(type(c) is int for c in coefficients), 'polynomial coefficients must be integers')
    point = tuple(rational(x) for x in point)
    require(len(coefficients) == d+1 and mean > 0 and len(point) == d, 'bad slack certificate shape')
    values = []
    for i, row in enumerate(data['A']):
        val = sum(Q(c)*Q(i)**j for j,c in enumerate(coefficients)); values.append(val)
        slack = 1-dot(row, point)
        require(val >= 0 and slack == val/mean and (val == 0) == (i in S),
                'polynomial/linear slack identity failed')
    require(sum(values)/n == mean and rank([data['A'][i] for i in S]) == d,
            'vertex normalization or active rank failed')


def adaptive_block_certificate(n: int, d: int):
    dimensions(n, d); m = n//2
    require(n % 2 == 0 and m > d, 'need separated nonwrapping blocks')
    data = moment_description(n, d); points = []; vertices = []
    for j in range(m+1):
        p, c = vertex_from_roots(n, d, range(j, j+d))
        points.append(p); vertices.append(c)
    legs = [{'row': j+d-1, 'entry': j, 'exit': j+1, 'dimension': 1, 'excess': 1}
            for j in range(1, m)]
    cert = {'n': n, 'dimension': d, 'parent_excess': n-d,
            'source_active': list(range(d)), 'target_active': list(range(m,m+d)),
            'points': points, 'vertex_certificates': vertices, 'legs': legs,
            'actual_edge_count': m, 'region_slack': m-3,
            'total_child_excess': m-1, 'large_carriers': 0,
            'scope': 'Exact ordinary-edge route and root mass conservation; no shortest-distance assertion.'}
    verify_adaptive_certificate(cert)
    return cert


def verify_adaptive_certificate(cert):
    n, d = cert['n'], cert['dimension']; dimensions(n,d); m=n//2
    require(n % 2 == 0 and m > d, 'invalid block range')
    data=moment_description(n,d); points=[tuple(rational(x) for x in p) for p in cert['points']]; vertices=cert['vertex_certificates']
    require(all(type(cert[key]) is int for key in ('parent_excess','actual_edge_count','region_slack','total_child_excess','large_carriers')), 'integer certificate fields required')
    require(len(points)==m+1 and len(vertices)==m+1, 'incomplete route')
    for j,(point,vc) in enumerate(zip(points,vertices)):
        require(vc['active']==list(range(j,j+d)), 'route active signature changed')
        verify_vertex(n,d,point,vc,data)
    for j in range(m):
        require(points[j]!=points[j+1], 'stationary step claimed as edge')
        common=set(vertices[j]['active']) & set(vertices[j+1]['active'])
        require(len(common)==d-1 and rank([data['A'][i] for i in common])==d-1,
                'shared supporting equalities do not define an ordinary edge')
    expected=[{'row':j+d-1,'entry':j,'exit':j+1,'dimension':1,'excess':1} for j in range(1,m)]
    require(cert['legs']==expected and all(type(v) is int for leg in cert['legs'] for v in leg.values()), 'changed charged portal occurrences')
    require(cert['source_active']==list(range(d)) and cert['target_active']==list(range(m,m+d)),
            'changed requested endpoints')
    require(cert['actual_edge_count']==m and cert['region_slack']==m-3,
            'false route length or region slack')
    require(cert['total_child_excess']==m-1 <= n-d and cert['parent_excess']==n-d,
            'root excess conservation failed')
    require(cert['large_carriers']==0, 'false large-carrier count')
    return {'edge_count':m, 'child_mass':m-1, 'parent_excess':n-d, 'slack':m-3}



def two_heavy_upper_witness(n: int, d: int):
    """A two-leg shortest-label repair attaining mass exactly 2(n-d).
    Each leg has a free-domino certificate. Augmentation covers every row
    inside that carrier, proving its intrinsic excess is the FULL parent e.
    """
    dimensions(n,d); m=n//2
    require(n%2==0 and m>d, 'need disjoint opposite blocks')
    source=frozenset(range(d)); old=frozenset([n-1,*range(d-1)])
    portal=frozenset([n-1,0,*range(m,m+d-2)]); target=frozenset(range(m,m+d))
    require(len(source & old)==d-1, 'initial step not adjacent')
    for S in (source,old,portal,target): matching_for(n,S)
    result=[]
    for row,A,B in ((n-1,old,portal),(m,portal,target)):
        K=A&B; M=matching_for(n,B)
        edge=next(edge for edge in M if not set(edge)&K)
        partial=tuple(e for e in M if e!=edge)
        for j in range(n):
            complete=extend_matching(n,partial,j)
            S={x for e in complete for x in e}
            require(K<=S and j in S and len(S)==d, 'invalid all-row carrier witness')
            matching_for(n,S)
        result.append({'row':row,'entry_active':sorted(A),'exit_active':sorted(B),
                       'common_rows':sorted(K),'partial_matching':[list(e) for e in partial],
                       'carrier_dimension':d-len(K),'carrier_excess':n-d})
    return {'source_active':sorted(source),'old_active':sorted(old),'target_active':sorted(target),
            'legs':result,'total_child_excess':2*(n-d),'region_slack':0}


def obstruction_parameters(n: int, d: int, k: int, allowance: int):
    dimensions(n,d)
    require(n%2==0 and type(k)is int and k>=0 and type(allowance)is int and allowance>=0,
            'invalid slack/allowance')
    m=n//2; gap=m-d+1; e=n-d
    require(gap>k+3, 'parameters do not meet the proved support-separation threshold')
    return {'n':n,'dimension':d,'parent_excess':e,'slack_limit':k,
            'support_separation':gap,'max_transition_count':k+3,
            'minimum_child_excess':2*e,'allowance':allowance,
            'bounded_spill_refuted':allowance<e,
            'minimum_necessary_slack_for_mass_below_2e':m-d-2,
            'explicit_conserving_slack':m-3,'explicit_edge_count':m}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--facets',type=int,default=40);ap.add_argument('--dimension',type=int,default=8)
    ap.add_argument('--slack',type=int,default=4);ap.add_argument('--allowance',type=int,default=2)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    try:
        result={'obstruction':obstruction_parameters(args.facets,args.dimension,args.slack,args.allowance),
                'adaptive_certificate':adaptive_block_certificate(args.facets,args.dimension),
                'two_heavy_upper_witness':two_heavy_upper_witness(args.facets,args.dimension)}
        text=json.dumps(jsonable(result),indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:
        ap.exit(2,f'Certificate rejected: {exc}\n')

if __name__=='__main__': main()
