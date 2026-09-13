#!/usr/bin/env python3
"""Recognize and maximally remove a candidate segment summand from ORIGINAL H-data.

For g!=0, compute the minimum full g-fiber length using one exact LP for each
positive/negative row pair. Farkas multipliers prove the entire H-polytope equals
its erosion plus the segment. A matching feasible point proves maximality.
No vertices, facets, circuits, or putative Minkowski decomposition are supplied.
Candidate directions remain inputs; arbitrary direction discovery is not claimed.

LP discovery uses capped exact Bland simplex; polynomially many LP calls do not
imply a polynomial pivot bound for this implementation. Verification uses only
rational linear identities and never invokes an optimizer.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from exact_farkas_lp import (ExactLP, Unbounded, parse, rat, serial, dot, require,
                            problem_hash, feasible_point, verify_dual)


def direction(raw, d):
    g = tuple(map(rat, raw))
    require(len(g) == d and any(g), 'nonzero direction of correct dimension required')
    return g


def directions(A, g):
    alpha = tuple(dot(a, g) for a in A)
    positive = [i for i, v in enumerate(alpha) if v > 0]
    negative = [i for i, v in enumerate(alpha) if v < 0]
    require(positive and negative, 'finite two-sided fiber direction required')
    return alpha, positive, negative


def pair_data(A, b, alpha, i, j):
    a, beta = alpha[i], -alpha[j]
    objective = tuple(beta*x+a*y for x, y in zip(A[i], A[j]))
    constant = beta*b[i]+a*b[j]
    return objective, constant, a*beta


def peel_one(Araw, braw, raw_g, seed=None, amount=None, pivot_cap=20000):
    A, b = parse(Araw, braw); g = direction(raw_g, len(A[0]))
    point = feasible_point(A, b, seed, pivot_cap)
    alpha, plus, minus = directions(A, g)
    solver = ExactLP(A, b, point, pivot_cap)
    proofs = []; worst = None; cache = {}
    for i in plus:
        for j in minus:
            objective, constant, scale = pair_data(A, b, alpha, i, j)
            # Reuse objectives arising from proportional rows or duplicate pairs.
            norm = max(map(abs, objective), default=Q(0)) or Q(1)
            key = tuple(v/norm for v in objective)
            if key not in cache: cache[key] = solver.maximize(key)
            optimum = cache[key]
            dual = [[r, serial(rat(v)*norm)] for r, v in optimum['dual']]
            value = rat(optimum['value'])*norm
            width = (constant-value)/scale
            require(width >= 0, 'negative width on a feasible fiber')
            proofs.append({'upper_row': i, 'lower_row': j, 'dual': dual})
            if worst is None or width < worst[0]:
                worst = width, i, j, optimum['point']
    capacity, i, j, witness = worst
    tau = capacity if amount is None else rat(amount)
    require(0 <= tau <= capacity, 'requested removal exceeds the proved capacity')
    certificate = serial({'problem_sha256': problem_hash(A, b), 'direction': g,
                          'capacity': capacity, 'removed': tau, 'pair_proofs': proofs,
                          'limiting_pair': [i, j], 'limiting_point': witness})
    result = verify_one(A, b, certificate)
    new_b = tuple(t-tau*max(v, Q(0)) for t, v in zip(b, alpha))
    U = min((b[k]-dot(A[k], point))/alpha[k] for k in plus)
    coefficient = max(Q(0), tau-U)
    new_seed = tuple(x-coefficient*v for x, v in zip(point, g))
    require(all(dot(a, new_seed) <= t for a, t in zip(A, new_b)), 'erosion seed construction failed')
    return {'certificate': certificate, 'verified': result, 'core_b': serial(new_b),
            'core_seed': serial(new_seed), 'lp_calls': solver.calls, 'lp_pivots': solver.pivots}


def verify_one(Araw, braw, c):
    """Exact BOTH-sided statement: complete global removal proof and sharp upper bound."""
    A, b = parse(Araw, braw); d = len(A[0])
    require(c['problem_sha256'] == problem_hash(A, b), 'changed H-system')
    g = direction(c['direction'], d); alpha, plus, minus = directions(A, g)
    capacity, tau = rat(c['capacity']), rat(c['removed'])
    require(0 <= tau <= capacity, 'invalid nonnegative capacity/removal')
    wanted = {(i, j) for i in plus for j in minus}; seen = set()
    for proof in c['pair_proofs']:
        i, j = proof['upper_row'], proof['lower_row']
        require(type(i) is int and type(j) is int and (i, j) in wanted and (i, j) not in seen,
                'missing, repeated, or invalid row pair')
        seen.add((i, j))
        v, constant, denominator = pair_data(A, b, alpha, i, j)
        upper = verify_dual(A, b, v, proof['dual'])
        require(upper <= constant-capacity*denominator, 'Farkas pair bound insufficient')
    require(seen == wanted, 'not all opposing row pairs were certified')
    limiting = c['limiting_pair']
    require(isinstance(limiting, list) and len(limiting) == 2 and
            all(type(i) is int for i in limiting) and tuple(limiting) in wanted,
            'invalid limiting pair')
    x = tuple(map(rat, c['limiting_point']))
    require(len(x) == d and all(dot(a, x) <= t for a, t in zip(A, b)), 'infeasible sharpness point')
    v, constant, denominator = pair_data(A, b, alpha, *limiting)
    require(constant-dot(v, x) == capacity*denominator, 'capacity upper witness is not sharp')
    U = min((b[k]-dot(A[k], x))/alpha[k] for k in plus)
    L = max((b[k]-dot(A[k], x))/alpha[k] for k in minus)
    require(U-L == capacity, 'limiting point does not exhibit the full shortest fiber')
    fiber_start = tuple(a+L*z for a, z in zip(x, g))
    fiber_end = tuple(a+U*z for a, z in zip(x, g))
    for p in (fiber_start, fiber_end):
        require(all(dot(a, p) <= t for a, t in zip(A, b)), 'invalid limiting fiber endpoint')
    return serial({'status': 'PASS', 'dimension': d, 'rows': len(A),
                   'opposing_pairs': len(wanted), 'capacity': capacity, 'removed': tau,
                   'limiting_fiber': [fiber_start, fiber_end],
                   'scope': 'Exact global Minkowski equality and maximality; no Lean/platform verdict.'})


def peel(A, b, candidates, seed=None, pivot_cap=20000):
    A, current = parse(A, b); point = feasible_point(A, current, seed, pivot_cap)
    steps = []; segments = []; calls = pivots = 0
    for raw in candidates:
        out = peel_one(A, current, raw, point, pivot_cap=pivot_cap)
        steps.append(out['certificate']); current = tuple(map(rat, out['core_b']))
        point = tuple(map(rat, out['core_seed'])); calls += out['lp_calls']; pivots += out['lp_pivots']
        tau = rat(out['certificate']['removed']); g = tuple(map(rat, raw))
        if tau: segments.append(tuple(tau*v for v in g))
    return {'steps': steps, 'core_b': serial(current), 'core_seed': serial(point),
            'segments': serial(segments), 'lp_calls': calls, 'lp_pivots': pivots}


def verify_peeling(A, b, packet):
    A, current = parse(A, b); segments = []; pairs = 0
    for c in packet['steps']:
        out = verify_one(A, current, c); pairs += out['opposing_pairs']
        tau = rat(c['removed']); g = tuple(map(rat, c['direction']))
        current = tuple(t-tau*max(dot(a, g), Q(0)) for a, t in zip(A, current))
        if tau: segments.append(tuple(tau*v for v in g))
    require(list(current) == list(map(rat, packet['core_b'])), 'false coarse right-hand sides')
    require([tuple(map(rat, g)) for g in packet['segments']] == segments, 'false extracted summands')
    point = tuple(map(rat, packet['core_seed']))
    require(len(point) == len(A[0]) and all(dot(a, point) <= t for a, t in zip(A, current)),
            'false coarse feasible point')
    return {'status': 'PASS', 'stages': len(packet['steps']), 'extracted_segments': len(segments),
            'opposing_pair_proofs': pairs}


def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('input', type=Path)
    ap.add_argument('--certificate', type=Path); ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    try:
        data = json.loads(args.input.read_text())
        if args.certificate:
            out = verify_peeling(data['A'], data['b'], json.loads(args.certificate.read_text()))
        else:
            packet = peel(data['A'], data['b'], data['candidate_directions'], data.get('feasible_point'))
            out = {'certificate': packet, 'verified': verify_peeling(data['A'], data['b'], packet)}
        text = json.dumps(serial(out), indent=2, sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text, end='')
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        ap.exit(2, f'No segment certificate: {exc}\n')

if __name__ == '__main__': main()
