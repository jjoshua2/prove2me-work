#!/usr/bin/env python3
"""Complete counted flagification when higher-defect incidence is a cactus.

Uses the UNCHANGED #262 exact stellar accounting. The new potential is
W + number_of_long_incidence_cycles. It decreases even when a cycle-opening
move leaves W unchanged. A complete antichain is input, not discovered here.
No normality, polytopality, Lean verification, or arbitrary Hirsch bound is
inferred from a successful finite-complex certificate.
"""
from __future__ import annotations
from collections import deque
from itertools import combinations
from pathlib import Path
import argparse, json
import stellar_defect_budget as base

require = base.require
Complex = base.Complex


def incidence(K):
    G = {}
    for j, N in enumerate(K.higher()):
        a = ('h', j); G[a] = set()
        for v in N:
            b = ('v', v); G[a].add(b); G.setdefault(b, set()).add(a)
    return G


def blocks(G):
    """Iterative Tarjan edge-block decomposition; isolated nodes are retained
    in the component count. No NetworkX dependency or recursion depth limit.
    """
    disc = {}; low = {}; parent = {}; stack = []; out = []; count = 0
    for root in sorted(G):
        if root in disc: continue
        count += 1; disc[root] = low[root] = len(disc); parent[root] = None
        walk = [(root, iter(sorted(G[root])))]
        while walk:
            u, it = walk[-1]
            try:
                v = next(it)
            except StopIteration:
                walk.pop(); p = parent[u]
                if p is not None:
                    low[p] = min(low[p], low[u])
                    if low[u] >= disc[p]:
                        B = []
                        while stack:
                            edge = stack.pop(); B.append(edge)
                            if edge == (p, u): break
                        out.append(tuple(B))
                continue
            if v not in disc:
                parent[v] = u; stack.append((u, v))
                disc[v] = low[v] = len(disc)
                walk.append((v, iter(sorted(G[v]))))
            elif v != parent[u] and disc[v] < disc[u]:
                stack.append((u, v)); low[u] = min(low[u], disc[v])
    return out, count


def inspect(K, node_cap=100000):
    G = incidence(K)
    require(len(G) <= node_cap, 'incidence node cap: no class certificate')
    B, c = blocks(G); cycles = []; cactus = True
    for edges in B:
        if len(edges) == 1: continue
        degrees = {}
        for u, v in edges:
            degrees[u] = degrees.get(u, 0)+1; degrees[v] = degrees.get(v, 0)+1
        if len(edges) != len(degrees) or any(d != 2 for d in degrees.values()):
            cactus = False
        else:
            cycles.append(frozenset(degrees))
    q = len(K.higher()); h = len(G)-q; e = sum(map(len, G.values()))//2
    beta = e-len(G)+c; long = sum(len(C) > 4 for C in cycles)
    require(K.weight() == h-q-c+beta, 'incidence Euler identity failed')
    if cactus:
        require(beta == len(cycles), 'cactus cycle-rank identity failed')
        require(q >= c+beta+long, 'rooted-block high-node count failed')
    return {'cactus': cactus, 'higher': q, 'supported_labels': h, 'components': c,
            'incidence_edges': e, 'cycle_rank': beta, 'long_cycles': long,
            'weight': K.weight(), 'potential': K.weight()+long,
            'linear_bound': h-2*c}, G


def twin(K):
    signatures = {}
    for i, N in enumerate(K.higher()):
        for v in N: signatures.setdefault(v, []).append(i)
    groups = {}
    for v, sig in signatures.items(): groups.setdefault(tuple(sig), []).append(v)
    pairs = [tuple(sorted(vs)[:2]) for vs in groups.values() if len(vs) > 1]
    return min(pairs) if pairs else None


def two_core(G):
    H = {u: set(vs) for u, vs in G.items()}
    q = deque(sorted(u for u, vs in H.items() if len(vs) < 2))
    while q:
        u = q.popleft()
        if u not in H: continue
        for v in H.pop(u):
            H[v].remove(u)
            if len(H[v]) < 2: q.append(v)
    return H


def select(K):
    """Derived leaf-block schedule, not bounded lookahead over arbitrary moves."""
    pair = twin(K)
    if pair is not None: return list(pair), 'twin'
    info, G = inspect(K); require(info['cactus'] and K.higher(), 'outside nonempty cactus class')
    C = two_core(G); B, _ = blocks(C); occurrences = {}
    for edges in B:
        for u in set(x for e in edges for x in e): occurrences[u] = occurrences.get(u, 0)+1
    cuts = {u for u, n in occurrences.items() if n > 1}
    leaves = [set(x for e in b for x in e) for b in B if len(b) > 1]
    leaves = sorted((b for b in leaves if len(b & cuts) <= 1), key=lambda b: tuple(sorted(b)))
    require(leaves, 'proved leaf-cycle existence failed')
    for b in leaves:
        for N in sorted(b):
            if N[0] != 'h' or N in cuts: continue
            private = [v[1] for v in G[N] if len(G[v]) == 1]
            require(len(private) == 1, 'twin-free peripheral high node is not a triple')
            for x in sorted(C[N]):
                if x not in b or x in cuts or len(G[x]) != 2: continue
                other = next(v for v in G[x] if v != N)
                if other in cuts: continue
                return sorted((private[0], x[1])), 'long-cycle' if len(b) > 4 else 'four-cycle'
    raise ValueError('proved peripheral opening existence failed')


def construct(K, step_cap=100000):
    require(type(step_cap) is int and step_cap >= 0, 'invalid subdivision cap')
    original = K; initial, _ = inspect(K)
    require(initial['cactus'], 'unsupported overlapping incidence cycles')
    steps = []
    while K.higher():
        require(len(steps) < step_cap, 'subdivision cap: no completed flag certificate')
        before, _ = inspect(K); edge, kind = select(K)
        J, record = base.account(K, edge); after, _ = inspect(J)
        require(after['cactus'] and after['potential'] < before['potential'], 'cactus potential failed')
        steps.append({'kind': kind, 'account': record, 'before': before, 'after': after})
        K = J
    packet = {'format': 'cactus-defect-refinement-v1', 'input_sha256': base.fingerprint(original),
              'initial': initial, 'steps': steps, 'terminal': K.payload()}
    verify(original, packet)
    return packet


def verify(K, packet):
    """Replay exact operations and the strengthened potential, NOT selection.
    Any legal cactus-preserving, potential-decreasing trace can be audited.
    """
    require(packet['format'] == 'cactus-defect-refinement-v1' and
            packet['input_sha256'] == base.fingerprint(K), 'changed initial complex')
    initial, _ = inspect(K)
    require(initial['cactus'] and initial == packet['initial'], 'false cactus input/counts')
    neutral = newborn = 0
    for s in packet['steps']:
        before, _ = inspect(K); require(s['before'] == before, 'incorrect pre-step graph ledger')
        J, actual = base.account(K, s['account']['edge'])
        require(actual == s['account'], 'false exact stellar record')
        after, _ = inspect(J)
        require(after == s['after'] and after['cactus'], 'false post-step graph/class')
        require(after['potential'] < before['potential'], 'no strict augmented-potential drop')
        require(s['kind'] in ('twin', 'long-cycle', 'four-cycle'), 'invalid schedule label')
        if s['kind'] == 'twin':
            u, v = actual['edge']
            require(any(u in N for N in K.higher()) and
                    all((u in N) == (v in N) for N in K.higher()), 'false twin')
        else:
            require(after['weight'] <= before['weight'], 'opening increased weight')
            if s['kind'] == 'long-cycle':
                require(after['long_cycles'] < before['long_cycles'], 'long cycle not eliminated')
            else:
                require(after['weight'] < before['weight'], 'four-cycle opening not paid')
        neutral += after['weight'] == before['weight']
        newborn += actual['created_higher_weight']; K = J
    require(K.payload() == packet['terminal'] and not K.higher(), 'unfinished/false flag output')
    require(len(packet['steps']) <= initial['potential'] <= initial['linear_bound'], 'linear budget failed')
    return {'status': 'PASS', 'subdivisions': len(packet['steps']), 'neutral_openings': neutral,
            'newborn_higher_weight': newborn, 'initial_potential': initial['potential'],
            'linear_bound': initial['linear_bound'], 'initial_cycles': initial['cycle_rank'],
            'initial_long_cycles': initial['long_cycles'], 'refined_vertices': K.n,
            'scope': 'Exact finite cactus refinement; normality/polytopality and original H geometry are separate.'}



def with_twin_prelude(K, edges):
    original = K; prelude = []; h0 = len(set().union(*K.higher())) if K.higher() else 0
    for E in edges:
        u, v = E
        require(any(u in N for N in K.higher()) and
                all((u in N) == (v in N) for N in K.higher()), 'prelude is not a nonempty-incidence twin')
        K, record = base.account(K, E); prelude.append(record)
    tail = construct(K)
    packet = {'format': 'cactus-twin-prelude-v1', 'input_sha256': base.fingerprint(original),
              'prelude': prelude, 'tail': tail, 'initial_high_support': h0}
    verify_prelude(original, packet)
    return packet


def verify_prelude(K, packet):
    require(packet['format'] == 'cactus-twin-prelude-v1' and
            packet['input_sha256'] == base.fingerprint(K), 'changed prelude input')
    h0 = len(set().union(*K.higher())) if K.higher() else 0
    require(h0 == packet['initial_high_support'], 'wrong initial high support')
    for r in packet['prelude']:
        u, v = r['edge']; H = K.higher(); h = len(set().union(*H))
        require(any(u in N for N in H) and all((u in N) == (v in N) for N in H), 'invalid prelude twin')
        K, actual = base.account(K, r['edge'])
        require(actual == r, 'wrong prelude operation')
        h1 = len(set().union(*K.higher())) if K.higher() else 0
        require(h1 < h, 'twin support failed to decrease')
    result = verify(K, packet['tail']); report, _ = inspect(K)
    t = len(packet['prelude'])+result['subdivisions']
    bound = h0-2*report['components']
    require(t <= bound, 'combined linear support bound failed')
    return {**result, 'subdivisions': t, 'prelude_steps': len(packet['prelude']),
            'tail_steps': result['subdivisions'], 'linear_bound': bound}


def flatten(K, packet):
    if packet['format'] == 'cactus-twin-prelude-v1':
        verify_prelude(K, packet)
        return packet['prelude']+[s['account'] for s in packet['tail']['steps']], packet['tail']['terminal']
    verify(K, packet)
    return [s['account'] for s in packet['steps']], packet['terminal']


def flag_route(K, packet, first, last, d, segment_type=None):
    """Use the existing flag-normal segment algorithm and #262 carrier map.
    Refined maximal faces are NOT enumerated. The caller must justify that the
    input is a pure normal (e.g. polytopal boundary) complex of this dimension.
    """
    steps, terminal = flatten(K, packet); F, H = frozenset(first), frozenset(last)
    require(len(F) == len(H) == d and K.face(F) and K.face(H), 'bad original endpoints')
    J = Complex.create(terminal['vertices'], terminal['minimal_nonfaces'])
    U, V = base.lift_pair(F, H, steps)
    class Oracle:
        def __init__(self): self.cache = {}
        def ask(self, S):
            S = frozenset(S)
            if S not in self.cache: self.cache[S] = J.face(S)
            return self.cache[S]
    if segment_type is None:
        from original_facet_segments import Segment
        segment_type = Segment
    O = Oracle(); M = J.n
    alg = segment_type(M, d, O, max(1, M-d), 4*(d+1)*(max(1, M-d)+1))
    fine = alg.between(U & V, U, V)
    require(len(fine)-1 <= M-d, 'normal-flag route bound did not hold')
    path = base.transport(K, steps, fine, d)
    require(path[0] == F and path[-1] == H and all(F & H <= Q for Q in path), 'lost original endpoint/common face')
    return {'refined_path': [sorted(S) for S in fine], 'original_path': [sorted(S) for S in path],
            'original_edges': len(path)-1, 'refined_edges': len(fine)-1, 'bound': M-d,
            'stationary_steps': len(fine)-len(path), 'membership_queries': len(O.cache),
            'enumerated_refined_facets': 0}


def main():
    ap = argparse.ArgumentParser(description=__doc__); ap.add_argument('input', type=Path)
    ap.add_argument('--output', type=Path, required=True); ap.add_argument('--certificate', type=Path)
    a = ap.parse_args()
    try:
        raw = json.loads(a.input.read_text()); K = Complex.create(raw['vertices'], raw['minimal_nonfaces'])
        c = json.loads(a.certificate.read_text()) if a.certificate else construct(K)
        a.output.write_text(json.dumps({'certificate': c, 'verified': verify(K, c)}, indent=2)+'\n')
    except (ValueError, KeyError, TypeError, IndexError, OSError) as e:
        ap.exit(2, f'No completed verified refinement: {e}\n')

if __name__ == '__main__': main()
