#!/usr/bin/env python3
"""Affine-invariant coordinate-level obstruction with original-edge comparators.

Recognizes a supplied affine image of the triangular Klee--Minty family from
all actual H rows. The exponential count is a proved recurrence, not a large
vertex enumeration or an empirical search over coordinate charts. Research
arithmetic only; no Lean extraction or general polytope recognition is claimed.
"""
from __future__ import annotations
from fractions import Fraction as Q
from hashlib import sha256
from math import isqrt
from pathlib import Path
import argparse
import json
import original_route_exclusion as audit

require, rat, serial, dot = audit.require, audit.rat, audit.serial, audit.dot


def eye(d): return tuple(tuple(Q(i == j) for j in range(d)) for i in range(d))
def vec(x, d):
    require(isinstance(x, (list, tuple)) and len(x) == d, 'vector dimension')
    return tuple(map(rat, x))
def mat(x, d):
    require(isinstance(x, (list, tuple)) and len(x) == d, 'matrix dimension')
    return tuple(vec(r, d) for r in x)
def mv(A, x): return tuple(dot(a, x) for a in A)
def mm(A, B):
    cols = list(zip(*B))
    return tuple(tuple(dot(a, c) for c in cols) for a in A)
def add(x, y): return tuple(a+b for a, b in zip(x, y))
def sub(x, y): return tuple(a-b for a, b in zip(x, y))


def vertex(bits, epsilon):
    require(isinstance(bits, (list, tuple)) and bits and
            all(type(t) is int and t in (0, 1) for t in bits), 'invalid cube bits')
    epsilon = rat(epsilon)
    require(0 < epsilon < Q(1, 2), 'epsilon must lie strictly between zero and one half')
    x = []
    for i, t in enumerate(bits):
        lower = epsilon*x[-1] if i else Q(0)
        x.append(1-lower if t else lower)
    return tuple(x)


def canonical(d, epsilon):
    A, b = [], []
    for i in range(d):
        for t in (0, 1):
            a = [Q(0)]*d
            a[i] = Q(1 if t else -1)
            if i: a[i-1] = epsilon
            A.append(tuple(a)); b.append(Q(t))
    return tuple(A), tuple(b)


def level_lower_bound(d):
    """Least K with K(K-1) >= 2^d, using integer arithmetic only."""
    require(type(d) is int and d >= 1, 'positive dimension required')
    n = 1 << d
    k = (1+isqrt(1+4*n))//2
    if k*(k-1) < n: k += 1
    require(k*(k-1) >= n and (k-1)*(k-2) < n, 'integer bound computation')
    return k


def model(data):
    d = data['dimension']; epsilon = rat(data['epsilon'])
    require(type(d) is int and d >= 1 and 0 < epsilon < Q(1, 2), 'invalid family parameters')
    T = mat(data.get('chart', eye(d)), d)
    S = mat(data.get('inverse_chart', eye(d)), d)
    require(mm(T, S) == eye(d) and mm(S, T) == eye(d), 'not an invertible affine chart')
    offset = vec(data.get('offset', [0]*d), d)
    scales = vec(data.get('row_scales', [1]*(2*d)), 2*d)
    require(all(s > 0 for s in scales), 'nonpositive original row scale')
    C, h = canonical(d, epsilon)
    A0 = mm(C, S)
    A = tuple(tuple(s*t for t in a) for s, a in zip(scales, A0))
    b = tuple(s*(t+dot(a, offset)) for s, a, t in zip(scales, A0, h))
    if 'A' in data or 'b' in data:
        require(tuple(vec(a, d) for a in data['A']) == A and vec(data['b'], 2*d) == b,
                'original H rows differ from the certified affine family')
    return d, epsilon, T, S, offset, scales, A, b


def decode(y, mod):
    d, e, T, S, o, scales, A, b = mod
    y = vec(y, d); x = mv(S, sub(y, o)); bits = []
    for i, z in enumerate(x):
        lower = e*x[i-1] if i else Q(0)
        require(lower < 1-lower and (z == lower or z == 1-lower), 'input is not a family vertex')
        bits.append(int(z == 1-lower))
    require(all(dot(a, y) <= z for a, z in zip(A, b)), 'infeasible decoded vertex')
    return tuple(bits)


def original_packet(bits, mod):
    """PRODUCER: explicit triangular inverse, then exact affine transport."""
    d, e, T, S, o, scales, A, b = mod
    active = [2*i+t for i, t in enumerate(bits)]
    R = [[Q(0)]*d for _ in range(d)]
    for j in range(d):
        for i in range(d):
            z = Q(i == j) - (e*R[i-1][j] if i else 0)
            R[i][j] = z/(1 if bits[i] else -1)
    transported = mm(T, R)
    inverse = [[transported[i][j]/scales[active[j]] for j in range(d)] for i in range(d)]
    return {'point': add(mv(T, vertex(bits, e)), o), 'active': active,
            'basis': active, 'inverse': inverse}


def sparse_vertex_check(A, b, p):
    """Consumer: same right-inverse identities as #271, skipping zero products."""
    d = len(A[0]); x = vec(p['point'], d)
    require(all(dot(a, x) <= rhs for a, rhs in zip(A, b)), 'infeasible original point')
    I = [i for i, (a, z) in enumerate(zip(A, b)) if dot(a, x) == z]
    require(p['active'] == I, 'incomplete active set')
    B = p['basis']; R = mat(p['inverse'], d)
    require(type(B) is list and len(B) == d and len(set(B)) == d and
            all(type(i) is int and i in I for i in B), 'invalid original vertex basis')
    for i, rowid in enumerate(B):
        nz = [(k, z) for k, z in enumerate(A[rowid]) if z]
        for j in range(d):
            require(sum((z*R[k][j] for k, z in nz), Q(0)) == int(i == j), 'false vertex inverse')
    return x, set(I)


def check_path(A, b, source, target, packet):
    require(packet['format'] == 'original-route-witness-v1' and
            packet['input_sha256'] == audit.binding(A, b, source, target), 'path binding')
    V = [sparse_vertex_check(A, b, p) for p in packet['vertices']]
    require(V and V[0][0] == source and V[-1][0] == target and
            type(packet['length']) is int and packet['length'] == len(V)-1, 'path endpoints or count')
    require(len(packet['edges']) == len(V)-1, 'missing edge rank record')
    d = len(A[0]); left = set(); debt = 0
    for (x, I), (y, J), e in zip(V, V[1:], packet['edges']):
        rows = e['rows']; R = audit.matrix(e['right_inverse'], d, d-1)
        require(x != y and type(rows) is list and len(rows) == d-1 and len(set(rows)) == d-1 and
                all(type(i) is int and i in I & J for i in rows), 'not a candidate original edge')
        for i, rowid in enumerate(rows):
            nz = [(k, z) for k, z in enumerate(A[rowid]) if z]
            for j in range(d-1):
                require(sum((z*R[k][j] for k, z in nz), Q(0)) == int(i == j), 'false common-row inverse')
        debt += len((J-I) & left); left |= I-J
    return {'original_edges': len(V)-1, 'row_reentries': debt}


def family_anchors(mod):
    d, e, T, S, o, scales, A, b = mod
    out = []
    for i in range(d):
        for t in (0, 1):
            x = [Q(1, 2)]*d
            x[i] = Q(t) if i == 0 else (1-e/2 if t else e/2)
            out.append(add(mv(T, x), o))
    return out


def binding(data):
    mod = model(data); d, e, T, S, o, scales, A, b = mod
    return sha256(json.dumps(serial([d, e, T, S, o, scales, A, b,
                                    vec(data['start'], d), vec(data['target'], d)]),
                             separators=(',', ':')).encode()).hexdigest()


def construct(data):
    mod = model(data); d, e, T, S, o, scales, A, b = mod
    source, target = vec(data['start'], d), vec(data['target'], d)
    first, last = decode(source, mod), decode(target, mod)
    order = [i for i in range(d) if first[i] != last[i]]
    bits = list(first); points = [original_packet(bits, mod)]; edges = []
    for i in order:
        old = points[-1]; columns = [j for j in range(d) if j != i]
        edges.append({'rows': [old['basis'][j] for j in columns],
                      'right_inverse': [[r[j] for j in columns] for r in old['inverse']]})
        bits[i] = last[i]; points.append(original_packet(bits, mod))
    packet = {'format': 'original-route-witness-v1', 'input_sha256': audit.binding(A, b, source, target),
              'vertices': points, 'edges': edges, 'length': len(order)}
    c = {'format': 'affine-level-barrier-v1', 'input_sha256': binding(data),
         'parallel_edge_count': 1 << (d-1), 'universal_coordinate_level_lower_bound': level_lower_bound(d),
         'nonzero_last_column_row': next(i for i in range(d) if T[i][-1]),
         'first_bits': first, 'last_bits': last, 'flip_order': order,
         'target_prefix_levels': [(Q(0), Q(1)) if i == 0 else
             (e*mv(S, sub(target, o))[i-1], 1-e*mv(S, sub(target, o))[i-1]) for i in range(d)],
         'facet_anchors': family_anchors(mod), 'path': packet}
    c = serial(c)
    return {'certificate': c, 'verified': verify(data, c)}


def verify(data, c):
    mod = model(data); d, e, T, S, o, scales, A, b = mod
    require(c['format'] == 'affine-level-barrier-v1' and c['input_sha256'] == binding(data), 'family binding')
    N = 1 << (d-1); K = level_lower_bound(d)
    require(type(c['parallel_edge_count']) is int and c['parallel_edge_count'] == N and
            type(c['universal_coordinate_level_lower_bound']) is int and
            c['universal_coordinate_level_lower_bound'] == K, 'wrong uniform cardinal bound')
    row = c['nonzero_last_column_row']
    require(type(row) is int and 0 <= row < d and T[row][-1] != 0, 'coordinate does not detect the parallel edges')
    source, target = vec(data['start'], d), vec(data['target'], d)
    first, last = decode(source, mod), decode(target, mod)
    require(c['first_bits'] == list(first) and c['last_bits'] == list(last), 'changed endpoint labels')
    target_x = mv(S, sub(target, o))
    prefix_levels = [(Q(0), Q(1)) if i == 0 else
                     (e*target_x[i-1], 1-e*target_x[i-1]) for i in range(d)]
    require(c['target_prefix_levels'] == serial(prefix_levels) and
            all(lo < hi for lo, hi in prefix_levels), 'false target-prefix face levels')
    order = c['flip_order']; needed = {i for i in range(d) if first[i] != last[i]}
    require(type(order) is list and all(type(i) is int for i in order) and
            len(order) == len(needed) and set(order) == needed, 'repeated, omitted or extra bit flip')
    bits = list(first); expected = [first]
    for i in order: bits[i] = last[i]; expected.append(tuple(bits))
    actual = [decode(p['point'], mod) for p in c['path']['vertices']]
    require(actual == expected, 'route disagrees with supplied bit transitions')
    outcome = check_path(A, b, source, target, c['path'])
    require(outcome['original_edges'] == len(needed) and outcome['row_reentries'] == 0,
            'nonshortest or reentering cube route')
    anchors = [vec(x, d) for x in c['facet_anchors']]
    require(len(anchors) == 2*d, 'missing genuine-facet witness')
    for i, x in enumerate(anchors):
        require(all(dot(a, x) == z if i == j else dot(a, x) < z
                    for j, (a, z) in enumerate(zip(A, b))), 'false facet-interior witness')
    return {'status': 'PASS', 'dimension': d, 'genuine_original_facets': 2*d,
            'parallel_edge_lengths_distinct_by_family_proof': N,
            'level_lower_bound_in_every_affine_chart': K,
            'every_injective_affine_embedding_obstructed': True,
            'original_graph_diameter_by_cube_classification': d,
            'shortest_endpoint_distance': len(needed), 'common_original_facets_preserved': d-len(needed),
            'target_prefix_faces_certified': d, 'levels_per_next_coordinate_on_prefix_face': 2,
            **outcome,
            'scope': 'Family proof plus exact rational identities; not chart sampling, Lean, projective/extension obstruction, or a Hirsch counterexample.'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path); p.add_argument('--certificate', type=Path)
    p.add_argument('--output', type=Path, required=True); a = p.parse_args()
    data = json.loads(a.input.read_text())
    result = verify(data, json.loads(a.certificate.read_text())) if a.certificate else construct(data)
    a.output.write_text(json.dumps(serial(result), sort_keys=True, indent=2)+'\n')
if __name__ == '__main__': main()
