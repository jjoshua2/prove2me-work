#!/usr/bin/env python3
"""Discover ALL segment-summand directions using one certified antipodal walk.

Input: original rational A,b and a feasible vertex start. No candidate direction,
whole vertex set, normal fan, or Minkowski representation is supplied. A capped
lexicographic simplex search constructs a walk from a unique maximizer of c to
its unique minimizer. The independently checked walk contains EVERY nonzero
segment-factor direction. The earlier exact fiber tester filters this complete
finite list and produces a segment-free residual with a maximal zonotope factor.

Discovery may take exponentially many pivots or initial active-basis trials.
Completeness is certified on SUCCESS; no strongly-polynomial algorithm claim.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
from exact_farkas_lp import ExactLP, parse, rat, serial, dot, require, problem_hash, verify_dual
from recognized_segment_routes import inverse, rank, verify_edges
from hpoly_segment_peeling import peel, verify_peeling


def canonical(v):
    first = next((x for x in v if x), None)
    require(first is not None, 'zero vector is not a direction')
    return tuple(x / first for x in v)


def series_compare(a, b):
    for k in sorted(a.keys() | b.keys()):
        delta = a.get(k, Q(0)) - b.get(k, Q(0))
        if delta: return 1 if delta > 0 else -1
    return 0


class LexWalk:
    """Original-row basis pivots; symbolic perturbations affect only tie order."""
    def __init__(self, A, b, start):
        self.A, self.b = parse(A, b)
        self.m, self.d = len(A), len(A[0])
        self.start = tuple(map(rat, start))
        require(len(self.start) == self.d and all(dot(a, self.start) <= t
                for a, t in zip(self.A, self.b)), 'infeasible source')
        self.active = [i for i, (a, t) in enumerate(zip(self.A, self.b)) if dot(a, self.start) == t]
        require(rank([self.A[i] for i in self.active]) == self.d, 'source is not a vertex')
        self.cache = {}

    def inv(self, B):
        B = tuple(B)
        if B not in self.cache: self.cache[B] = inverse([self.A[i] for i in B])
        return self.cache[B]

    def coeff(self, c, inv):
        return tuple(sum((c[k] * inv[k][j] for k in range(self.d)), Q(0)) for j in range(self.d))

    def point(self, B):
        return tuple(dot(row, [self.b[i] for i in B]) for row in self.inv(B))

    def ratio(self, B, r, denominator=Q(1)):
        alpha = self.coeff(self.A[r], self.inv(B))
        terms = {0: (self.b[r]-dot(alpha, [self.b[i] for i in B])) / denominator,
                 r+1: Q(1)/denominator}
        for i, v in zip(B, alpha): terms[i+1] = terms.get(i+1, Q(0))-v/denominator
        return {k: v for k, v in terms.items() if v}

    def feasible(self, B):
        try: self.inv(B)
        except ValueError: return False
        return all(series_compare(self.ratio(B, i), {}) >= 0 for i in range(self.m))

    def source_basis(self, cap):
        for tried, B in enumerate(combinations(self.active, self.d), 1):
            require(tried <= cap, 'active-basis search cap; no completeness certificate returned')
            if self.feasible(B): return tuple(B), tried
        raise ValueError('no symbolically feasible source basis found')

    def run(self, B0, c, pivot_cap):
        B = B0; seen = set(); route = [self.start]; steps = []
        objective = tuple(-x for x in c)
        for _ in range(pivot_cap+1):
            require(B not in seen, 'unexpected basis revisit')
            seen.add(B)
            inv = self.inv(B); lam = self.coeff(objective, inv)
            bad = [j for j, v in enumerate(lam) if v < 0]
            if not bad:
                require(all(v > 0 for v in lam), 'nongeneric terminal objective')
                return {'source_basis': B0, 'target_basis': B, 'normal': c,
                        'target_weights': lam, 'pivots': steps, 'route': route}
            require(len(steps) < pivot_cap, 'pivot cap; no complete direction catalogue claimed')
            j = min(bad, key=lambda j: B[j])
            delta = tuple(-row[j] for row in inv)
            entering = None; best = None
            for r, a in enumerate(self.A):
                den = dot(a, delta)
                if den <= 0: continue
                value = self.ratio(B, r, den)
                if best is None or series_compare(value, best) < 0: entering, best = r, value
                elif series_compare(value, best) == 0: raise ValueError('symbolic ratio tie')
            require(entering is not None, 'unbounded improving direction')
            require(series_compare(best, {}) > 0, 'nonpositive symbolic step')
            NB = tuple(entering if k == j else r for k, r in enumerate(B))
            require(self.feasible(NB), 'new basis not symbolically feasible')
            x, y = self.point(B), self.point(NB)
            require(all(dot(a, y) <= t for a, t in zip(self.A, self.b)), 'original limit infeasible')
            steps.append({'basis': B, 'leave_position': j, 'enter': entering,
                          'next_basis': NB, 'real_step': best.get(0, Q(0))})
            if y != x:
                require(dot(c, y) < dot(c, x), 'original edge not strictly monotone')
                route.append(y)
            B = NB
        raise ValueError('pivot cap reached')


def boundedness_certificate(A, b, start, pivot_cap):
    d = len(A[0]); lp = ExactLP(A, b, start, pivot_cap)
    evidence = []
    for j in range(d):
        for sign in (-1, 1):
            e = tuple(Q(sign * int(i == j)) for i in range(d))
            out = lp.maximize(e)
            evidence.append({'coordinate': j, 'sign': sign, 'dual': out['dual'], 'bound': out['value']})
    return evidence, lp.pivots


def verify_walk(Araw, braw, start, c):
    """Verify original endpoints/edges and strict antipodality; no pivot search.

    The stored discovery pivots are audit metadata. Completeness only needs the
    finite original-H walk, strict dual endpoint supports and boundedness proof.
    """
    A, b = parse(Araw, braw); d = len(A[0]); n = len(A)
    require(c['problem_sha256'] == problem_hash(A, b), 'H-data changed')
    route = [tuple(map(rat, p)) for p in c['route']]
    require(route and route[0] == tuple(map(rat, start)), 'changed source')
    L = verify_edges(A, b, route)
    normal = tuple(map(rat, c['normal'])); require(len(normal) == d, 'normal dimension')
    for field, weights, point, sign in [('source_basis', c['source_weights'], route[0], 1),
                                        ('target_basis', c['target_weights'], route[-1], -1)]:
        B = c[field]
        require(len(B) == d and len(set(B)) == d and all(type(i) is int and 0 <= i < n for i in B), 'invalid support basis')
        values = tuple(map(rat, weights))
        require(len(values) == d and all(v > 0 for v in values), 'endpoint support must be strictly positive')
        require(rank([A[i] for i in B]) == d and all(dot(A[i], point) == b[i] for i in B), 'not a tight full-rank endpoint basis')
        require(all(sum((v*A[i][j] for v, i in zip(values, B)), Q(0)) == sign*normal[j] for j in range(d)), 'opposite endpoint normals not certified')
    seen = set()
    for item in c['boundedness']:
        j, s = item['coordinate'], item['sign']
        require(type(j) is int and type(s) is int and 0 <= j < d and s in (-1,1) and (j,s) not in seen, 'bad boundedness index')
        seen.add((j,s)); obj = tuple(Q(s*int(k == j)) for k in range(d))
        require(verify_dual(A,b,obj,item['dual']) == rat(item['bound']), 'wrong coordinate bound')
    require(len(seen) == 2*d, 'incomplete boundedness certificate')
    require(all(dot(normal,y) < dot(normal,x) for x,y in zip(route,route[1:])), 'nonmonotone discovery walk')
    directions = sorted({canonical(tuple(v-u for u,v in zip(x,y))) for x,y in zip(route,route[1:])})
    require([tuple(map(rat,g)) for g in c['candidate_directions']] == directions, 'candidate list omits/adds a walk direction')
    return {'status':'PASS','walk_edges':L,'candidate_directions':len(directions),
            'strict_antipodal_endpoints':True,'all_segment_directions_covered':True,
            'scope':'Complete segment-direction cover from exact opposite supports and original edges, not a bound on search runtime.'}


def discover_walk(Araw, braw, start, pivot_cap=20000, basis_cap=100000, objective_cap=16):
    model = LexWalk(Araw,braw,start); A,b = model.A,model.b
    bounds,bound_pivots = boundedness_certificate(A,b,model.start,pivot_cap)
    B,attempts = model.source_basis(basis_cap)
    theoretical = model.d * comb(model.m, max(0,model.d-1)) + 1
    errors = []
    for trial in range(1,min(objective_cap,theoretical)+1):
        z = Q(1,trial+2); weights = tuple(1+z**(j+1) for j in range(model.d))
        normal = tuple(sum((w*A[i][k] for w,i in zip(weights,B)),Q(0)) for k in range(model.d))
        try: result = model.run(B,normal,pivot_cap)
        except ValueError as exc:
            if str(exc) != 'nongeneric terminal objective': raise
            errors.append(str(exc)); continue
        dirs = sorted({canonical(tuple(v-u for u,v in zip(x,y))) for x,y in zip(result['route'],result['route'][1:])})
        result.update({'problem_sha256':problem_hash(A,b),'source_weights':weights,'boundedness':bounds,
                       'candidate_directions':dirs,'discovery':{'source_basis_trials':attempts,
                       'objective_trial':trial,'root_avoidance_trial_bound':theoretical,
                       'boundedness_lp_pivots':bound_pivots,'original_basis_pivots':len(result['pivots']),
                       'stationary_pivots':len(result['pivots'])-len(result['route'])+1}})
        result = serial(result); verify_walk(A,b,start,result); return result
    raise ValueError('objective cap; no antipodal completeness certificate returned')


def catalogue(A,b,start,**limits):
    walk = discover_walk(A,b,start,**limits)
    peeling = peel(A,b,walk['candidate_directions'],start,pivot_cap=limits.get('pivot_cap',20000))
    out = {'walk':walk,'peeling':peeling}
    return {'certificate':out,'verified':verify_catalogue(A,b,start,out)}


def verify_catalogue(A,b,start,c):
    walk = verify_walk(A,b,start,c['walk'])
    require([step['direction'] for step in c['peeling']['steps']] == c['walk']['candidate_directions'], 'not every covered direction was tested')
    peeling = verify_peeling(A,b,c['peeling'])
    positive = []
    for s in c['peeling']['steps']:
        if rat(s['capacity']) > 0:
            positive.append(tuple(map(rat,s['direction'])))
            require(rat(s['removed']) == rat(s['capacity']), 'incomplete extraction invalidates segment-free residual')
    require(len(positive) <= walk['walk_edges'], 'too many distinct segment factors')
    return {**walk,'positive_segment_directions':len(positive),
            'zero_capacity_candidates':len(c['peeling']['steps'])-len(positive),
            'maximal_zonotope_factor_complete':True,'residual_has_no_nonzero_segment_summand':True,
            'pair_proofs':peeling['opposing_pair_proofs'],
            'scope':'Exact complete direction catalogue and maximal segment stripping. Residual need not be indecomposable into higher-dimensional summands.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--pivot-cap',type=int,default=20000);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=verify_catalogue(data['A'],data['b'],data['start'],json.loads(a.certificate.read_text())) if a.certificate else catalogue(data['A'],data['b'],data['start'],pivot_cap=a.pivot_cap)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No complete catalogue: {exc}\n')
if __name__=='__main__':main()
