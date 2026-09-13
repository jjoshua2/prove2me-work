#!/usr/bin/env python3
"""Final-H -> certified segment removal -> recognized feedback core -> original edges.

Only A,b, two endpoint vertices and CANDIDATE DIRECTIONS are inputs. No segment
length, decomposition, coarse model, affine chart, or parent route is supplied.
The extractor maximizes each removable segment, exact Farkas certificates remove
redundant coarse rows, and an existing positive-feedback-box criterion supplies
the core's <=d edge route. The unchanged wall lifter then returns edges of the
ORIGINAL input polytope, whose active ranks/blockers are independently rechecked.

Recognition is sufficient, not universal. Candidate discovery and arbitrary
coarse-core routing remain outside this tool. Exact simplex discovery is capped;
its certificate verifier uses no LP or route search.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction as Q
from pathlib import Path
from exact_farkas_lp import (ExactLP, Unbounded, dot, parse, rat, require, serial,
                            problem_hash, verify_dual)
from hpoly_segment_peeling import peel, verify_peeling
import implicit_minkowski_lift as lifter


def inverse(A):
    n = len(A); require(all(len(row) == n for row in A), 'square matrix required')
    rows = [list(map(rat, row))+[Q(i == j) for j in range(n)] for i, row in enumerate(A)]
    for j in range(n):
        k = next((i for i in range(j, n) if rows[i][j]), None)
        require(k is not None, 'singular coordinate basis')
        rows[j], rows[k] = rows[k], rows[j]; pivot = rows[j][j]
        rows[j] = [x/pivot for x in rows[j]]
        for i in range(n):
            if i != j and rows[i][j]:
                t = rows[i][j]; rows[i] = [x-t*y for x, y in zip(rows[i], rows[j])]
    return tuple(tuple(row[n:]) for row in rows)


def rank(A):
    return lifter.rank(tuple(tuple(row) for row in A))


def erase_redundancy(A, b, seed, pivot_cap=20000):
    keep = list(range(len(A))); proofs = []; pivots = calls = 0
    for row in list(keep):
        rest = [i for i in keep if i != row]
        if not rest: continue
        solver = ExactLP([A[i] for i in rest], [b[i] for i in rest], seed, pivot_cap)
        calls += 1
        try: out = solver.maximize(A[row])
        except Unbounded:
            pivots += solver.pivots
            continue
        pivots += solver.pivots
        if rat(out['value']) <= b[row]:
            proofs.append({'removed_row': row, 'dual': [[rest[i], v] for i, v in out['dual']]})
            keep = rest
    return {'kept': keep, 'deletions': proofs, 'lp_calls': calls, 'lp_pivots': pivots}


def verify_redundancy(A, b, certificate):
    keep = set(range(len(A)))
    for item in certificate['deletions']:
        row = item['removed_row']
        require(type(row) is int and row in keep, 'invalid repeated row deletion')
        require(all(type(i) is int and i in keep and i != row for i, _ in item['dual']),
                'redundancy proof uses removed/self row')
        value = verify_dual(A, b, A[row], item['dual'])
        require(value <= b[row], 'row is not implied by retained inequalities')
        keep.remove(row)
    require(certificate['kept'] == sorted(keep), 'false retained row set')
    return sorted(keep)


def endpoint_data(A, b, core_b, x, segments):
    x = tuple(map(rat, x)); d = len(A[0])
    require(len(x) == d and all(dot(a, x) <= t for a, t in zip(A, b)), 'infeasible original endpoint')
    active = [i for i, (a, t) in enumerate(zip(A, b)) if dot(a, x) == t]
    require(rank([A[i] for i in active]) == d, 'original endpoint is not a vertex')
    weights = [Q(int(i in active)) for i in range(len(A))]
    c = tuple(sum((A[i][j] for i in active), Q(0)) for j in range(d))
    chosen = []
    for g in segments:
        value = dot(c, g)
        require(value != 0, 'vertex objective tied on a nonzero extracted segment')
        chosen.append(g if value > 0 else (Q(0),)*d)
    p = tuple(x[j]-sum((g[j] for g in chosen), Q(0)) for j in range(d))
    require(all(dot(a, p) <= t for a, t in zip(A, core_b)), 'coarse endpoint not feasible')
    require(all(dot(A[i], p) == core_b[i] for i in active), 'original support row not inherited')
    return p, weights


def feedback_chart(A, b, keep, source, certificate=None):
    d = len(source)
    require(len(keep) == 2*d, 'coarse system not recognized: need exactly 2d retained rows')
    lower = [i for i in keep if dot(A[i], source) == b[i]]
    require(len(lower) == d, 'coarse source not a simple feedback-box corner')
    B = tuple(tuple(-v for v in A[i]) for i in lower); Binv = inverse(B)
    upper = [None]*d; F = [[Q(0)]*d for _ in range(d)]; u = [Q(0)]*d
    for row in keep:
        if row in lower: continue
        a = tuple(sum((A[row][k]*Binv[k][j] for k in range(d)), Q(0)) for j in range(d))
        positives = [i for i, x in enumerate(a) if x > 0]
        require(len(positives) == 1, 'coarse non-lower row is not a feedback upper bound')
        i = positives[0]
        require(upper[i] is None and all(x <= 0 for j, x in enumerate(a) if j != i),
                'inconsistent feedback coordinate assignment')
        upper[i] = row; u[i] = (b[row]-dot(A[row], source))/a[i]
        require(u[i] > 0, 'feedback intercept is not positive')
        F[i] = [Q(0) if i == j else -x/a[i] for j, x in enumerate(a)]
    M = tuple(tuple(Q(i == j)-F[i][j] for j in range(d)) for i in range(d))
    if certificate is None:
        inv = inverse(M); w = tuple(sum(row, Q(0)) for row in inv)
    else:
        require(certificate['lower_rows'] == lower and certificate['upper_rows'] == upper,
                'forged feedback chart labels')
        w = tuple(map(rat, certificate['positive_vector']))
    require(len(w) == d and all(v > 0 for v in w) and all(dot(row, w) < w[i] for i, row in enumerate(F)),
            'feedback contraction has no supplied positive strict witness')
    return B, Binv, F, u, {'anchor': serial(source), 'lower_rows': lower, 'upper_rows': upper, 'positive_vector': serial(w)}


def feedback_route(A, b, keep, source, target, chart=None):
    anchor = tuple(map(rat, chart['anchor'])) if chart is not None else source
    require(len(anchor) == len(source) and all(dot(a, anchor) <= t for a, t in zip(A, b)),
            'feedback anchor outside the coarse polytope')
    B, Binv, F, u, c = feedback_chart(A, b, keep, anchor, chart)
    d = len(source)
    def signature(x):
        y = tuple(dot(row, tuple(v-w for v, w in zip(x, anchor))) for row in B)
        bits = []
        for i, v in enumerate(y):
            high = u[i]+dot(F[i], y)
            require(v == 0 or v == high, 'coarse endpoint is not a feedback-box vertex')
            bits.append(v != 0)
        return bits
    bits, target_bits = signature(source), signature(target)
    path = [source]
    for changed in range(d):
        if bits[changed] == target_bits[changed]: continue
        bits[changed] = target_bits[changed]
        M = [tuple(Q(i == j)-(F[i][j] if bits[i] else 0) for j in range(d)) for i in range(d)]
        rhs = [u[i] if bits[i] else Q(0) for i in range(d)]
        inv = inverse(M); point = tuple(dot(row, rhs) for row in inv)
        original = tuple(anchor[i]+dot(Binv[i], point) for i in range(d))
        path.append(original)
    require(path[-1] == target and len(path)-1 <= d, 'feedback route endpoint/count failure')
    verify_edges(A, b, path)
    return path, c


def verify_edges(A, b, path):
    d = len(A[0]); active = []
    require(path and len(set(path)) == len(path), 'empty/repeated route vertex')
    for v in path:
        require(len(v) == d and all(dot(a, v) <= t for a, t in zip(A, b)), 'route leaves original inequalities')
        I = {i for i, (a, t) in enumerate(zip(A, b)) if dot(a, v) == t}
        require(rank([A[i] for i in sorted(I)]) == d, 'route point is not an original vertex')
        active.append(I)
    for k, (x, y) in enumerate(zip(path, path[1:])):
        common = sorted(active[k]&active[k+1]); vector = tuple(v-u for u, v in zip(x, y))
        require(rank([A[i] for i in common]) == d-1, 'route step not an original ordinary edge')
        require(any(dot(A[i], vector) < 0 for i in active[k]) and
                any(dot(A[i], vector) > 0 for i in active[k+1]), 'missing original edge blockers')
    return len(path)-1


def reconstruct_lift_input(data, peeling, core_rows, chart=None):
    A, b = parse(data['A'], data['b']); d = len(A[0]); core_b = tuple(map(rat, peeling['core_b']))
    segments = [tuple(map(rat, g)) for g in peeling['segments']]
    p, ws = endpoint_data(A, b, core_b, data['start'], segments)
    q, wt = endpoint_data(A, b, core_b, data['end'], segments)
    keep = verify_redundancy(A, core_b, core_rows)
    path, chart = feedback_route(A, core_b, keep, p, q, chart)
    lift_data = serial({'A': A, 'b': core_b, 'base_route': path,
                        'summands': [[(Q(0),)*d, g] for g in segments],
                        'source_weights': ws, 'target_weights': wt})
    return lift_data, chart


def build(data, pivot_cap=20000):
    A, b = parse(data['A'], data['b'])
    packet = peel(A, b, data['candidate_directions'], data['start'], pivot_cap)
    verify_peeling(A, b, packet)
    core_b = tuple(map(rat, packet['core_b'])); core_seed = tuple(map(rat, packet['core_seed']))
    redundancy = erase_redundancy(A, core_b, core_seed, pivot_cap)
    lift_input, chart = reconstruct_lift_input(data, packet, redundancy)
    lifted = lifter.build(lift_input)['certificate']
    certificate = {'problem_sha256': problem_hash(A, b), 'peeling': packet,
                   'coarse_redundancy': redundancy, 'feedback_chart': chart, 'lift': lifted}
    return {'certificate': serial(certificate), 'verified': verify(data, serial(certificate))}


def verify(data, c):
    A, b = parse(data['A'], data['b']); d = len(A[0])
    require(c['problem_sha256'] == problem_hash(A, b), 'original problem changed')
    candidates = [tuple(map(rat, g)) for g in data['candidate_directions']]
    require([tuple(map(rat, item['direction'])) for item in c['peeling']['steps']] == candidates,
            'candidate directions changed')
    removal = verify_peeling(A, b, c['peeling'])
    lift_data, _ = reconstruct_lift_input(data, c['peeling'], c['coarse_redundancy'], c['feedback_chart'])
    report = lifter.verify(lift_data, c['lift'])
    route = [tuple(map(rat, x)) for x in c['lift']['route']]
    require(route[0] == tuple(map(rat, data['start'])) and route[-1] == tuple(map(rat, data['end'])),
            'requested final-H endpoints changed')
    length = verify_edges(A, b, route)
    q = report['added_directions']; base_length = report['base_edges']
    require(length <= (q+1)*base_length+q <= (q+1)*d+q, 'recognized global budget failed')
    return {'status': 'PASS', 'dimension': d, 'original_rows': len(A),
            'positive_segment_extractions': removal['extracted_segments'],
            'pair_implication_certificates': removal['opposing_pair_proofs'],
            'coarse_rows_retained': len(c['coarse_redundancy']['kept']),
            'coarse_edge_route': base_length, 'original_ordinary_edges': length,
            'added_directions': q, 'all_endpoint_bound_for_recognized_model': (q+1)*d+q,
            'lp_calls_in_discovery': c['peeling']['lp_calls']+c['coarse_redundancy']['lp_calls'],
            'lp_pivots_in_discovery': c['peeling']['lp_pivots']+c['coarse_redundancy']['lp_pivots'],
            'scope': 'Exact original-H decomposition, feedback core and ordinary-edge certificate. No universal recognition, sampler runtime or Lean/platform verdict.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('input', type=Path)
    ap.add_argument('--certificate', type=Path); ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    try:
        data = json.loads(args.input.read_text())
        out = verify(data, json.loads(args.certificate.read_text())) if args.certificate else build(data)
        text = json.dumps(serial(out), indent=2, sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text, end='')
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        ap.exit(2, f'No recognized route certificate (not a diameter lower bound): {exc}\n')

if __name__ == '__main__': main()
