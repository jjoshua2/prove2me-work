#!/usr/bin/env python3
"""Exact metric barriers, diagonal gain balancing, and short original-edge paths.

No universal diameter or good-chart theorem is assumed. The gain test recognizes
ONLY positive diagonal equivalence to signed roots. Its negative cycle witness
is not a certificate against arbitrary affine or projective transformations.
The separate four-ray identity gives the all-affine conditioning obstruction.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
from typing import Sequence
import argparse
import json
import original_route_exclusion as edge


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(x) -> Q:
    require(isinstance(x, (int, str, Q)) and not isinstance(x, bool), 'exact rational required')
    return Q(x)


def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: serial(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [serial(v) for v in x]
    return x


def binding(x) -> str:
    return sha256(json.dumps(serial(x), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def pair_rows(raw):
    require(isinstance(raw, (list, tuple)) and raw and raw[0], 'nonempty row matrix required')
    A = tuple(tuple(map(rat, row)) for row in raw)
    d = len(A[0]); require(all(len(row) == d for row in A), 'row dimensions')
    supports = [tuple(i for i, v in enumerate(row) if v) for row in A]
    require(all(1 <= len(S) <= 2 for S in supports), 'rows must have one or two nonzeros')
    return A, supports


def recognize_balance(raw):
    """Find positive diagonal scaling, or a checked inconsistent gain cycle."""
    A, supports = pair_rows(raw); d = len(A[0])
    graph = [[] for _ in range(d)]
    for r, S in enumerate(supports):
        if len(S) == 2:
            i, j = S; gain = abs(A[r][i] / A[r][j])
            graph[i].append((j, r, gain)); graph[j].append((i, r, 1 / gain))
    scales = [None] * d; tree = [[] for _ in range(d)]
    for root in range(d):
        if scales[root] is not None: continue
        scales[root] = Q(1); todo = deque([root])
        while todo:
            i = todo.popleft()
            for j, r, gain in graph[i]:
                if scales[j] is None:
                    scales[j] = scales[i] * gain
                    tree[i].append((j, r)); tree[j].append((i, r)); todo.append(j)
    for r, S in enumerate(supports):
        if len(S) != 2: continue
        i, j = S; gain = abs(A[r][i] / A[r][j])
        if scales[j] == gain * scales[i]: continue
        # Produce a tree path i->j, then close it using this edge j->i.
        parents = {i: None}; todo = deque([i])
        while j not in parents:
            x = todo.popleft()
            for y, rr in tree[x]:
                if y not in parents: parents[y] = (x, rr); todo.append(y)
        steps = []; x = j
        while x != i:
            p, rr = parents[x]; steps.append({'row': rr, 'from': p, 'to': x}); x = p
        steps.reverse(); steps.append({'row': r, 'from': j, 'to': i})
        product = Q(1)
        for st in steps: product *= abs(A[st['row']][st['from']] / A[st['row']][st['to']])
        cert = {'format': 'signed-gain-balance-v1', 'input_sha256': binding(A),
                'status': 'INCONSISTENT_CYCLE', 'cycle': steps, 'gain_product': str(product)}
        verify_balance(A, cert); return cert
    weights = [1 / abs(row[S[0]] * scales[S[0]]) for row, S in zip(A, supports)]
    cert = {'format': 'signed-gain-balance-v1', 'input_sha256': binding(A), 'status': 'BALANCED',
            'scales': serial(scales), 'row_weights': serial(weights)}
    verify_balance(A, cert); return cert


def verify_balance(raw, cert):
    """No spanning-tree search, propagation, LP, or logarithmic tolerance."""
    A, supports = pair_rows(raw); d = len(A[0])
    require(cert['format'] == 'signed-gain-balance-v1' and cert['input_sha256'] == binding(A), 'changed rows')
    if cert['status'] == 'BALANCED':
        scales = tuple(map(rat, cert['scales'])); weights = tuple(map(rat, cert['row_weights']))
        require(len(scales) == d and len(weights) == len(A), 'scaling dimensions')
        require(all(s > 0 for s in scales) and all(r > 0 for r in weights), 'positive scales required')
        for a, w, S in zip(A, weights, supports):
            require(all(abs(w * a[i] * scales[i]) == 1 for i in S), 'not a signed-root row after scaling')
        return {'status': 'PASS', 'conclusion': 'positive diagonal signed-root chart exists',
                'dimension': d, 'rows': len(A), 'row_identities': sum(map(len, supports))}
    require(cert['status'] == 'INCONSISTENT_CYCLE', 'unknown balance status')
    steps = cert['cycle']; require(isinstance(steps, list) and steps, 'empty cycle')
    product = Q(1)
    for j, st in enumerate(steps):
        r, u, v = st['row'], st['from'], st['to']
        require(all(type(z) is int for z in (r, u, v)) and 0 <= r < len(A), 'bad cycle labels')
        require(len(supports[r]) == 2 and {u, v} == set(supports[r]), 'step is not an original pair row')
        require(v == steps[(j + 1) % len(steps)]['from'], 'cycle not closed/contiguous')
        product *= abs(A[r][u] / A[r][v])
    require(product != 1 and product == rat(cert['gain_product']), 'false inconsistent cycle')
    return {'status': 'PASS', 'conclusion': 'no positive diagonal signed-root chart',
            'cycle_length': len(steps), 'gain_product': str(product),
            'scope': 'Only diagonal scaling is excluded; not every affine chart or short route.'}


def balanced_H(raw, b, cert):
    report = verify_balance(raw, cert); require(cert['status'] == 'BALANCED', 'no chart')
    A, _ = pair_rows(raw); rhs = tuple(map(rat, b)); require(len(rhs) == len(A), 'RHS dimensions')
    scales = tuple(map(rat, cert['scales'])); weights = tuple(map(rat, cert['row_weights']))
    B = tuple(tuple(w * a * s for a, s in zip(row, scales)) for row, w in zip(A, weights))
    return B, tuple(w * z for w, z in zip(weights, rhs)), report


def metric_bound(e, X, Y, Z):
    e, X, Y, Z = map(rat, (e, X, Y, Z))
    require(0 < e < 1 and X > 0 and Y > 0 and Z * Z < X * Y, 'positive definite metric and 0<e<1 required')
    D = X * Y - Z * Z
    denom = [X * (X + 2 * e * Z + e * e * Y), Y * (Y + 2 * e * Z + e * e * X)]
    require(all(z > 0 for z in denom), 'Gram denominator')
    selected = 0 if X >= Y else 1
    U, V = (X, Y) if selected == 0 else (Y, X)
    gap = (Z + e * U) ** 2 + (1 - e * e) * U * (U - V)
    require(gap == denom[selected] - D and gap >= 0, 'metric square identity failed')
    sins = [e * e * D / z for z in denom]
    require(sins[selected] <= e * e, 'uniform metric bound failed')
    return {'status': 'PASS', 'epsilon': str(e), 'Gram': serial([X, Y, Z]),
            'squared_pair_sines': serial(sins), 'selected_pair': selected,
            'nonnegative_gap': str(gap), 'bound': str(e * e)}


def polygon(e):
    e = rat(e); require(0 < e <= Q(1, 2), 'octagon range 0<epsilon<=1/2')
    t = (1 + e / 2) / (1 + e)
    return tuple(tuple(map(Q, p)) for p in [(1, -1), (1, Q(1, 2)), (t, t), (Q(1, 2), 1),
             (-1, 1), (-1, -Q(1, 2)), (-t, -t), (-Q(1, 2), -1)])


def product_H(e, d):
    e = rat(e); require(type(d) is int and d >= 2, 'dimension >=2')
    polygon(e)
    first = [(1, 0), (1, e), (e, 1), (0, 1), (-1, 0), (-1, -e), (-e, -1), (0, -1)]
    A = [tuple(map(Q, a)) + (Q(0),) * (d - 2) for a in first]
    b = [Q(1), 1 + e / 2, 1 + e / 2, Q(1), Q(1), 1 + e / 2, 1 + e / 2, Q(1)]
    for j in range(2, d):
        for sign in (1, -1):
            A.append(tuple(Q(sign if k == j else 0) for k in range(d))); b.append(Q(1))
    return tuple(A), tuple(b)


def shortest_product_points(e, d, a, bits_a, b, bits_b):
    V = polygon(e)
    require(type(a) is int and type(b) is int and 0 <= a < 8 and 0 <= b < 8, 'bad octagon labels')
    require(len(bits_a) == len(bits_b) == d - 2 and all(x in (-1, 1) for x in (*bits_a, *bits_b)), 'bad cube endpoint')
    forward, backward = (b - a) % 8, (a - b) % 8; step = 1 if forward <= backward else -1
    route = [V[(a + step * j) % 8] + tuple(map(Q, bits_a)) for j in range(min(forward, backward) + 1)]
    for j in range(d - 2):
        if bits_a[j] != bits_b[j]:
            x = list(route[-1]); x[j + 2] = Q(bits_b[j]); route.append(tuple(x))
    return route


def product_anchors(e, d):
    V = polygon(e); A, b = product_H(e, d); points = []
    for i in range(8):
        points.append(tuple((x + y) / 2 for x, y in zip(V[i], V[(i + 1) % 8])) + (Q(0),) * (d - 2))
    for j in range(2, d):
        for sign in (1, -1): points.append(tuple(Q(sign if k == j else 0) for k in range(d)))
    for i, x in enumerate(points):
        require(all(edge.dot(a, x) == rhs if k == i else edge.dot(a, x) < rhs for k, (a, rhs) in enumerate(zip(A, b))), 'facet anchor failed')
    return points


def route_packet(A, b, points):
    packet = {'format': 'original-route-witness-v1', 'input_sha256': edge.binding(A, b, points[0], points[-1]),
              'vertices': [edge.vertex_packet(A, b, x) for x in points], 'length': len(points) - 1}
    edge.add_path_inverses(A, packet)
    raw = serial({'A': A, 'b': b, 'start': points[0], 'target': points[-1]})
    packet = serial(packet); checked = edge.verify_path(raw, packet)
    return {'input': raw, 'certificate': packet, 'verified': checked}


def product_record(e, d, a=0, b=4, bits_a=None, bits_b=None):
    bits_a = [-1] * (d - 2) if bits_a is None else list(bits_a)
    bits_b = [1] * (d - 2) if bits_b is None else list(bits_b)
    points = shortest_product_points(e, d, a, bits_a, b, bits_b)
    A, rhs = product_H(e, d); record = route_packet(A, rhs, points)
    record['family'] = {'epsilon': str(rat(e)), 'dimension': d, 'first_octagon': a, 'last_octagon': b,
                        'first_cube': bits_a, 'last_cube': bits_b}
    record['facet_anchors'] = serial(product_anchors(e, d))
    record['proved_family_diameter'] = d + 2
    record['optimum_Gram_2x2'] = serial([1, 1, -rat(e)])
    return record


def verify_product_record(record):
    f = record['family']; e, d = rat(f['epsilon']), f['dimension']; A, b = product_H(e, d)
    raw = record['input']; require(raw['A'] == serial(A) and raw['b'] == serial(b), 'family-to-original-H binding')
    V = polygon(e)
    require(all(type(f[k]) is int and 0 <= f[k] < 8 for k in ('first_octagon', 'last_octagon')), 'invalid octagon endpoint labels')
    require(all(isinstance(f[k], list) and len(f[k]) == d - 2 and all(type(x) is int and x in (-1, 1) for x in f[k]) for k in ('first_cube', 'last_cube')), 'invalid cube endpoint labels')
    source = V[f['first_octagon']] + tuple(map(Q, f['first_cube']))
    target = V[f['last_octagon']] + tuple(map(Q, f['last_cube']))
    require(raw['start'] == serial(source) and raw['target'] == serial(target), 'endpoint binding')
    result = edge.verify_path(raw, record['certificate'])
    anchors = [tuple(map(rat, p)) for p in record['facet_anchors']]
    require(len(anchors) == len(A) and all(len(x) == d for x in anchors), 'anchor count/dimension')
    for i, x in enumerate(anchors):
        require(all(edge.dot(a, x) == rhs if k == i else edge.dot(a, x) < rhs for k, (a, rhs) in enumerate(zip(A, b))), 'not a genuine facet witness')
    a, z = f['first_octagon'], f['last_octagon']; shortest = min((a-z) % 8, (z-a) % 8) + sum(x != y for x, y in zip(f['first_cube'], f['last_cube']))
    require(result['original_edges'] == shortest and record['proved_family_diameter'] == d + 2, 'wrong product distance')
    require(record['optimum_Gram_2x2'] == serial([1, 1, -e]), 'wrong attaining metric')
    optimum = metric_bound(e, 1, 1, -e)
    require(optimum['squared_pair_sines'] == serial([e*e, e*e]), 'optimum not attained')
    common = set(record['certificate']['vertices'][0]['active']) & set(record['certificate']['vertices'][-1]['active'])
    return {'status': 'PASS', 'dimension': d, 'genuine_facets': len(A), 'route_edges': shortest,
            'common_endpoint_facets': len(common), 'family_diameter': d + 2,
            'best_local_delta': str(e), 'scope': 'Product-geometry proof plus exact records; not a separately Lean-verified polytope theorem.'}


def truncated_data(e, d):
    """One shallow vertex cut; the remaining bad feasible pairs survive."""
    A, b = product_H(e, d)
    normal = tuple([Q(1), Q(-1)] + [Q(-1)] * (d - 2))
    w = polygon(e)[0] + (Q(-1),) * (d - 2)
    neighbors = [polygon(e)[1] + w[2:], polygon(e)[7] + w[2:]]
    for j in range(2, d):
        v = list(w); v[j] = Q(1); neighbors.append(tuple(v))
    ports = []
    for v in neighbors:
        alpha = Q(1, 4) / edge.dot(normal, tuple(x - y for x, y in zip(w, v)))
        ports.append(tuple(x + alpha * (y - x) for x, y in zip(w, v)))
    return A + (normal,), b + (Q(d) - Q(1, 4),), w, ports


def truncated_record(e, d):
    A, b, w, ports = truncated_data(e, d)
    old_path = shortest_product_points(e, d, 0, [-1] * (d - 2), 4, [1] * (d - 2))
    points = [ports[0]] + old_path[1:]
    anchors = product_anchors(e, d)
    anchors.append(tuple(sum(p[j] for p in ports) / d for j in range(d)))
    r = route_packet(A, b, points)
    r.update(family={'epsilon': str(rat(e)), 'dimension': d}, facet_anchors=serial(anchors),
             all_pairs_upper_bound=d + 3, selected_shortest=d + 2)
    verify_truncated_record(r)
    return r


def verify_truncated_record(record):
    f = record['family']; e, d = rat(f['epsilon']), f['dimension']
    A, b, w, ports = truncated_data(e, d)
    raw = record['input']
    require(raw['A'] == serial(A) and raw['b'] == serial(b), 'wrong truncated original H')
    target = polygon(e)[4] + (Q(1),) * (d - 2)
    require(raw['start'] == serial(ports[0]) and raw['target'] == serial(target), 'wrong truncated endpoints')
    result = edge.verify_path(raw, record['certificate'])
    anchors = [tuple(map(rat, x)) for x in record['facet_anchors']]
    require(len(anchors) == len(A) and all(len(x) == d for x in anchors), 'truncation anchors shape')
    for i, x in enumerate(anchors):
        require(all(edge.dot(a, x) == z if j == i else edge.dot(a, x) < z for j, (a, z) in enumerate(zip(A, b))), 'invalid truncated facet anchor')
    require(result['original_edges'] == record['selected_shortest'] == d + 2, 'wrong truncated route count')
    require(record['all_pairs_upper_bound'] == d + 3, 'wrong one-cut diameter bound')
    # The two bad pairs are still feasible independent basis rows, not arbitrary
    # normals which never coexist at a vertex.
    for i, pair in [(1, (0, 1)), (3, (2, 3))]:
        x = polygon(e)[i] + (Q(-1),) * (d - 2)
        require(all(edge.dot(a, x) <= z for a, z in zip(A, b)), 'lost bad-pair vertex')
        require(set(pair) <= set(edge.active(A, b, x)) and edge.dot(A[-1], x) < b[-1], 'bad pair was cut away')
    return {'status': 'PASS', 'dimension': d, 'genuine_facets': len(A),
            'selected_shortest_edges': d + 2, 'all_pairs_upper_bound': d + 3,
            'all_affine_local_delta_upper': str(e),
            'nonproduct_reason': 'simplex facet and more than d+2 facets',
            'scope': 'Written shallow-cut/product-graph proof and exact H witnesses, not extra Lean conclusions.'}


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('input', type=Path)
    p.add_argument('--certificate', type=Path); p.add_argument('--output', type=Path, required=True)
    args = p.parse_args(); data = json.loads(args.input.read_text())
    result = verify_balance(data['A'], json.loads(args.certificate.read_text())) if args.certificate else recognize_balance(data['A'])
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')

if __name__ == '__main__': main()
