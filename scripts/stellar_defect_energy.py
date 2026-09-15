#!/usr/bin/env python3
"""Exact branching certificates for stellar refinements of finite complexes.

A Complex is DEFINED by its COMPLETE minimal-nonface list. A geometric caller
must certify that list against its original polytope. Local checks do not infer
completeness from a sample. Research software, not Lean-extracted code.
"""
from __future__ import annotations
from collections import defaultdict, deque
from dataclasses import dataclass
from itertools import combinations
from math import comb
from typing import Iterable
import argparse, hashlib, json
from pathlib import Path

Face = frozenset[int]

def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)

def ordered(sets: Iterable[Iterable[int]]) -> list[Face]:
    return sorted(set(map(frozenset, sets)), key=lambda s: (len(s), tuple(sorted(s))))

def minimal(sets: Iterable[Iterable[int]]) -> list[Face]:
    # Same-size distinct sets cannot absorb each other. For small faces, test
    # their subsets against hash tables rather than scanning all missing pairs.
    result = []; by_size = {}
    for s in ordered(sets):
        covered = False
        for size, group in by_size.items():
            if size >= len(s):
                continue
            if comb(len(s), size) < len(group):
                covered = any(frozenset(t) in group for t in combinations(s, size))
            else:
                covered = any(t <= s for t in group)
            if covered:
                break
        if not covered:
            result.append(s)
            by_size.setdefault(len(s), set()).add(s)
    return result

@dataclass(frozen=True)
class Complex:
    n: int
    missing: tuple[Face, ...]

    def __post_init__(self) -> None:
        need(type(self.n) is int and self.n >= 0, 'invalid label count')
        need(all(len(s) >= 2 and all(type(i) is int and 0 <= i < self.n for i in s)
                 for s in self.missing), 'invalid minimal nonface')
        need(list(self.missing) == minimal(self.missing), 'noncanonical/nonminimal list')

    @classmethod
    def make(cls, n: int, missing: Iterable[Iterable[int]]) -> Complex:
        return cls(n, tuple(ordered(missing)))

    def face(self, s: Iterable[int]) -> bool:
        s = frozenset(s)
        need(all(type(i) is int and 0 <= i < self.n for i in s), 'bad face label')
        return not any(t <= s for t in self.missing)

    def higher(self) -> tuple[Face, ...]:
        return tuple(s for s in self.missing if len(s) >= 3)

    def energy(self) -> int:
        return sum(len(s)-2 for s in self.higher())

    def data(self) -> dict:
        return {'n': self.n, 'missing': [sorted(s) for s in self.missing]}

    def digest(self) -> str:
        return hashlib.sha256(json.dumps(self.data(), sort_keys=True,
                            separators=(',', ':')).encode()).hexdigest()

    def twins(self) -> list[tuple[int, int]]:
        h = self.higher()
        sig = {i: tuple(j for j, s in enumerate(h) if i in s) for i in range(self.n)}
        return [e for e in combinations(range(self.n), 2) if sig[e[0]] and sig[e[0]] == sig[e[1]]]

    def productive_edges(self) -> list[tuple[int, int]]:
        # Every two-subset of a higher MINIMAL nonface is an actual face edge.
        return sorted({e for s in self.higher() for e in combinations(sorted(s), 2)})


def stellar(k: Complex, edge: Iterable[int]) -> Complex:
    """The exact minimal-nonface formula already established in PR #261."""
    e = frozenset(edge)
    need(len(e) == 2 and k.face(e), 'not a face edge')
    return Complex.make(k.n+1, minimal([e] + [n for n in k.missing if not e <= n]
                  + [(n-e) | {k.n} for n in k.missing if n & e]))


def analyze(k: Complex, edge: Iterable[int]) -> tuple[Complex, dict]:
    """Exact necessary-and-sufficient no-branch criterion and energy ledger.

    Persistent generators are old nonfaces not containing E, descendants of
    nonfaces containing E, and descendants of old pairs touching E. Additional
    surviving generators come only from mixed HIGHER nonfaces.
    """
    e = frozenset(edge)
    need(len(e) == 2 and k.face(e), 'not a face edge')
    z = k.n
    base = ordered([e] + [n for n in k.missing if not e <= n]
                   + [(n-e) | {z} for n in k.missing
                      if e <= n or (len(n) == 2 and n & e)])
    need(base == minimal(base), 'persistent generators unexpectedly contain one another')
    mixed = [n for n in k.higher() if len(n & e) == 1]
    certificates = []
    for n in mixed:
        witnesses = [w for w in k.missing
                     if (e <= w or (len(w) == 2 and w & e)) and w-e <= n-e]
        certificates.append({'old_mixed': sorted(n),
                             'absorber': sorted(witnesses[0]) if witnesses else None})
    j = stellar(k, e)
    base_set = set(base)
    extra = [n for n in j.missing if n not in base_set]
    need(all(z in n and len(n) >= 3 for n in extra), 'unexpected extra generator')
    c = sum(e <= n for n in k.higher())
    b = sum(len(n)-2 for n in extra)
    need(j.energy() == k.energy()-c+b, 'energy identity failed')
    no_branch = all(x['absorber'] is not None for x in certificates)
    need(no_branch == (not extra), 'no-branch characterization failed')
    if no_branch:
        need(j.energy() == k.energy()-c, 'nonbranching descent identity failed')
        need(len(j.higher()) == len(k.higher())-sum(len(n) == 3 and e <= n for n in k.missing),
             'nonbranching higher-count identity failed')
    high = k.higher(); u, v = sorted(e)
    sig_u = tuple(i for i, n in enumerate(high) if u in n)
    sig_v = tuple(i for i, n in enumerate(high) if v in n)
    record = {'input_sha256': k.digest(), 'edge': sorted(e), 'new_label': z,
              'higher_before': len(k.higher()), 'higher_after': len(j.higher()),
              'energy_before': k.energy(), 'energy_after': j.energy(),
              'containing_defects': c, 'branch_energy': b,
              'extra_higher': [sorted(n) for n in extra],
              'mixed_absorbers': certificates, 'no_branch': no_branch,
              'twin': bool(sig_u) and sig_u == sig_v, 'output_sha256': j.digest()}
    return j, record


def verify_step(k: Complex, record: dict) -> Complex:
    j, expected = analyze(k, record['edge'])
    need(record == expected, 'incorrect local witness/energy record')
    return j


def schedule(k: Complex, mode: str = 'two-step', step_cap: int = 1000,
             search_cap: int = 100000) -> dict:
    """Construct only completed descending macros; return honest stalls.

    two-step permits a plateau or rise at the first step, but each accepted
    macro ends at strictly smaller integer energy. No universal success claim.
    """
    need(mode in ('twins', 'nonbranch', 'energy', 'two-step'), 'unknown mode')
    need(type(step_cap) is int and step_cap >= 0 and type(search_cap) is int and search_cap > 0,
         'invalid cap')
    initial = k; steps = []; macros = []; queries = 0
    status = 'flag'
    while k.higher():
        candidates = []
        edges = k.twins() if mode == 'twins' else k.productive_edges()
        for e in edges:
            queries += 1
            need(queries <= search_cap, 'search cap: no completed schedule claim')
            j, rec = analyze(k, e)
            if mode == 'nonbranch' and not rec['no_branch']:
                continue
            if j.energy() < k.energy():
                candidates.append((j.energy(), len(j.higher()), tuple(e), (rec,), j))
        if not candidates and mode == 'two-step':
            for e in k.productive_edges():
                j, rec = analyze(k, e)
                for f in j.productive_edges():
                    queries += 1
                    need(queries <= search_cap, 'two-step search cap: no completion claim')
                    jj, rr = analyze(j, f)
                    if jj.energy() < k.energy():
                        candidates.append((jj.energy(), len(jj.higher()), (e, f), (rec, rr), jj))
        if not candidates:
            status = 'stalled'; break
        choice = min(candidates, key=lambda x: x[:3])
        new, packet = choice[4], choice[3]
        need(len(steps)+len(packet) <= step_cap, 'step cap: no completed schedule claim')
        macros.append({'start': len(steps), 'length': len(packet),
                       'energy_before': k.energy(), 'energy_after': new.energy()})
        steps.extend(packet); k = new
    result = {'mode': mode, 'initial': initial.data(), 'input_sha256': initial.digest(),
              'status': status, 'steps': steps, 'macros': macros,
              'final': k.data(), 'search_evaluations': queries}
    verify_schedule(result)
    return result


def verify_schedule(packet: dict) -> dict:
    k = Complex.make(packet['initial']['n'], packet['initial']['missing'])
    need(packet['input_sha256'] == k.digest(), 'initial digest mismatch')
    phi = k.energy(); c = b = 0; energies = [phi]
    for record in packet['steps']:
        k = verify_step(k, record); energies.append(k.energy())
        c += record['containing_defects']; b += record['branch_energy']
    need(packet['final'] == k.data(), 'final complex mismatch')
    need(k.energy() == phi-c+b, 'telescoping identity failed')
    pos = 0
    for macro in packet['macros']:
        length = macro['length']; need(length in (1, 2), 'bad macro length')
        need(macro['start'] == pos and pos+length < len(energies), 'bad macro indexing')
        need(macro['energy_before'] == energies[pos] and macro['energy_after'] == energies[pos+length],
             'false macro endpoints')
        need(energies[pos+length] < energies[pos], 'macro did not descend')
        pos += length
    need(pos == len(packet['steps']), 'unaccounted steps')
    need(pos <= 2*(phi-k.energy()), 'two-step resource bound failed')
    need(packet['status'] in ('flag', 'stalled'), 'bad completion state')
    need((packet['status'] == 'flag') == (not k.higher()), 'false flag claim')
    return {'stellar_steps': pos, 'initial_energy': phi, 'final_energy': k.energy(),
            'total_destroyed_incidence': c, 'total_branch_energy': b,
            'nonbranching_steps': sum(x['no_branch'] for x in packet['steps']),
            'higher_count_increases': sum(x['higher_after'] > x['higher_before'] for x in packet['steps']),
            'macro_count': len(packet['macros']), 'flag': not k.higher(),
            'refined_vertices': k.n,
            'flag_bound_valid_only_if_flag': not k.higher()}


def facet_subdivide(facets: Iterable[Face], edge: Iterable[int], z: int) -> tuple[Face, ...]:
    """Independent literal subdivision on MAXIMAL simplices."""
    e = frozenset(edge); facets = tuple(facets)
    need(len(e) == 2 and any(e <= f for f in facets), 'no such face edge')
    need(all(z not in f for f in facets), 'new label already used')
    return tuple(ordered([f for f in facets if not e <= f]
                         + [(f-{v}) | {z} for f in facets if e <= f for v in e]))


def ridge_graph(facets: Iterable[Face], d: int) -> dict[Face, set[Face]]:
    facets = tuple(facets); ridges = defaultdict(list)
    need(all(len(f) == d for f in facets), 'complex is not pure of the stated dimension')
    for f in facets:
        for v in f:
            ridges[f-{v}].append(f)
    g = {f: set() for f in facets}
    for neighbours in ridges.values():
        for f, h in combinations(neighbours, 2):
            g[f].add(h); g[h].add(f)
    return g


def shortest(g: dict[Face, set[Face]], x: Face, y: Face, locked: Face = frozenset()) -> list[Face]:
    need(x in g and y in g and locked <= x & y, 'invalid endpoints/locks')
    parent = {x: None}; queue = deque([x])
    while queue and y not in parent:
        f = queue.popleft()
        for h in sorted(g[f], key=lambda s: tuple(sorted(s))):
            if h not in parent and locked <= h:
                parent[h] = f; queue.append(h)
    need(y in parent, 'disconnected locked facet graph')
    path = [y]
    while path[-1] != x:
        path.append(parent[path[-1]])
    return path[::-1]


def lift_endpoints(f: Face, h: Face, steps: list[dict]) -> tuple[Face, Face]:
    # Same compatible endpoint-lift rule as PR #261; old labels are retained.
    for step in steps:
        e = frozenset(step['edge']); z = step['new_label']; oldf, oldh = f, h
        if e <= oldf:
            v = max(e-oldh) if e-oldh else max(e)
            f = (oldf-{v}) | {z}
        if e <= oldh:
            v = max(e-oldf) if e-oldf else max(e)
            h = (oldh-{v}) | {z}
    return f, h



def verify_carrier_path(facets: Iterable[Face], d: int, packet: dict, route: dict,
                        f: Face, h: Face) -> dict:
    """Replay a saved route without BFS, shortest-path search, or discovery.

    The caller supplies the complete old maximal-simplex table; geometric
    callers must establish its completeness separately from these local tests.
    """
    info = verify_schedule(packet)
    need(info['flag'], 'not a completed flag refinement')
    initial = tuple(map(frozenset, facets))
    need(f in initial and h in initial, 'unknown original endpoints')
    stages = [initial]
    for step in packet['steps']:
        stages.append(facet_subdivide(stages[-1], step['edge'], step['new_label']))
    fine = list(map(frozenset, route['refined_path']))
    x, y = lift_endpoints(f, h, packet['steps'])
    need(fine and fine[0] == x and fine[-1] == y, 'wrong refined endpoints')
    need(all(q in set(stages[-1]) and x & y <= q for q in fine), 'invalid/ unlocked refined facet')
    need(all(len(a & b) == d-1 for a, b in zip(fine, fine[1:])), 'refined nonedge')
    need(len(fine)-1 <= info['refined_vertices']-d, 'false refined length bound')
    walk = fine
    for j in reversed(range(len(packet['steps']))):
        step = packet['steps'][j]; e = frozenset(step['edge']); z = step['new_label']
        walk = [(q-{z}) | e if z in q else q for q in walk]
        old = set(stages[j])
        need(all(q in old for q in walk), 'invalid old carrier')
        need(all(a == b or len(a & b) == d-1 for a, b in zip(walk, walk[1:])), 'carrier chord')
    coarse = []
    for q in walk:
        if not coarse or q != coarse[-1]:
            coarse.append(q)
    need(coarse[0] == f and coarse[-1] == h, 'wrong original endpoints')
    need(all(f & h <= q for q in coarse), 'lost original common face')
    expected = {'refined_path': [sorted(q) for q in fine], 'original_path': [sorted(q) for q in coarse],
                'refined_steps': len(fine)-1, 'original_steps': len(coarse)-1,
                'stationary_carriers': len(fine)-len(coarse),
                'all_pairs_bound_from_flag_theorem': info['refined_vertices']-d,
                'intermediate_levels_checked': len(packet['steps'])}
    need(route == expected, 'saved carrier route/count mismatch')
    return expected


def carrier_route(facets: Iterable[Face], d: int, packet: dict, f: Face, h: Face) -> dict:
    """Exact finite reference router. It DOES enumerate the refined graph.

    The general length guarantee imports the normal-flag theorem. BFS here
    constructs a reference witness, not an efficient arbitrary-H algorithm.
    """
    info = verify_schedule(packet); need(info['flag'], 'residual nonflag complex: no bound')
    initial = tuple(facets); need(f in initial and h in initial, 'unknown original facet')
    stages = [initial]
    for step in packet['steps']:
        stages.append(facet_subdivide(stages[-1], step['edge'], step['new_label']))
    x, y = lift_endpoints(f, h, packet['steps']); g = ridge_graph(stages[-1], d)
    fine = shortest(g, x, y, x & y)
    need(len(fine)-1 <= info['refined_vertices']-d, 'flag route exceeded M-d')
    walk = fine[:]; levels = []
    for j in reversed(range(len(packet['steps']))):
        step = packet['steps'][j]; e = frozenset(step['edge']); z = step['new_label']
        walk = [(q-{z}) | e if z in q else q for q in walk]
        level = set(stages[j])
        need(all(q in level for q in walk), 'carrier is not an actual old facet')
        need(all(a == b or len(a & b) == d-1 for a, b in zip(walk, walk[1:])), 'carrier chord')
        levels.append(len(walk)-1)
    coarse = []
    for q in walk:
        if not coarse or q != coarse[-1]:
            coarse.append(q)
    need(coarse[0] == f and coarse[-1] == h, 'wrong projected endpoints')
    need(all(f & h <= q for q in coarse), 'lost an original common facet')
    need(all(len(a & b) == d-1 for a, b in zip(coarse, coarse[1:])), 'not original adjacency')
    return {'refined_path': [sorted(x) for x in fine], 'original_path': [sorted(x) for x in coarse],
            'refined_steps': len(fine)-1, 'original_steps': len(coarse)-1,
            'stationary_carriers': len(fine)-len(coarse),
            'all_pairs_bound_from_flag_theorem': info['refined_vertices']-d,
            'intermediate_levels_checked': len(levels)}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path); p.add_argument('--verify', action='store_true')
    p.add_argument('--mode', choices=('twins', 'nonbranch', 'energy', 'two-step'), default='two-step')
    p.add_argument('--out', type=Path)
    a = p.parse_args(); data = json.loads(a.input.read_text())
    result = verify_schedule(data) if a.verify else schedule(Complex.make(data['n'], data['missing']), a.mode)
    text = json.dumps(result, indent=2)+'\n'
    if a.out: a.out.write_text(text)
    else: print(text, end='')

if __name__ == '__main__':
    main()
