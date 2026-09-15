#!/usr/bin/env python3
"""Exact mixed-edge defect accounting, extending #261's twin-only refinement.

The input specifies a finite complex by its COMPLETE minimal nonfaces. This
module does not discover that list from H-inequalities or certify normality.
For a polytopal dual sphere, a completed flag subdivision gives the classical
normal-flag bound on ORIGINAL edges via the carrier maps below.

The new accounting permits mixed incidences and even creation of new higher
nonfaces when the created weight is smaller than the removed weight. Neither
existence of such a move at every state nor a polynomial bound in the original
facet count is asserted. Caps and local stalls return explicit partial status.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from math import comb
import argparse, hashlib, json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def ordered(sets):
    return sorted(set(map(frozenset, sets)), key=lambda S: (len(S), tuple(sorted(S))))


def minimal(sets):
    """Exact antichain reduction, using the cheaper of two subset searches."""
    result = []; by_size = {}
    for S in ordered(sets):
        blocked = False
        for k, previous in by_size.items():
            if k > len(S):
                continue
            if comb(len(S), k) < len(previous):
                blocked = any(frozenset(T) in previous for T in combinations(sorted(S), k))
            else:
                blocked = any(T <= S for T in previous)
            if blocked:
                break
        if not blocked:
            result.append(S); by_size.setdefault(len(S), set()).add(S)
    return result


def lists(sets):
    return [sorted(S) for S in ordered(sets)]


@dataclass(frozen=True)
class Complex:
    n: int
    missing: tuple

    @staticmethod
    def create(n, missing):
        require(type(n) is int and n >= 0, 'invalid vertex count')
        require(isinstance(missing, (list, tuple)), 'missing-face list required')
        sets = []
        for raw in missing:
            require(isinstance(raw, (list, tuple, set, frozenset)), 'invalid nonface')
            require(all(type(i) is int and 0 <= i < n for i in raw), 'invalid label')
            require(len(set(raw)) == len(raw) and len(raw) >= 2, 'invalid nonface size/duplicates')
            sets.append(frozenset(raw))
        require(len(set(sets)) == len(sets), 'duplicate minimal nonface')
        require(ordered(sets) == minimal(sets), 'nonface list is not an antichain')
        return Complex(n, tuple(ordered(sets)))

    def face(self, S):
        require(all(type(i) is int and 0 <= i < self.n for i in S), 'invalid face label')
        S = frozenset(S)
        return not any(N <= S for N in self.missing)

    def higher(self):
        return [N for N in self.missing if len(N) >= 3]

    def weight(self):
        return sum(len(N)-2 for N in self.higher())

    def payload(self):
        return {'vertices': self.n, 'minimal_nonfaces': lists(self.missing)}


def fingerprint(K):
    return hashlib.sha256(json.dumps(K.payload(), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def account(K, edge):
    """Complete residue computation; no simplified mixed-incidence update.

    The stellar formula is the earlier #261 membership formula, reused with
    explicit minimal residuals. Every nonface containing z is z union R with
    R minimal among the sets N minus E for old nonfaces meeting E.
    """
    require(isinstance(edge, (list, tuple)) and len(edge) == 2 and
            all(type(i) is int and 0 <= i < K.n for i in edge), 'invalid edge labels')
    E = frozenset(edge)
    require(len(E) == 2 and K.face(E), 'subdivision requires an actual face edge')
    common = [N for N in K.higher() if E <= N]
    residues = minimal([N-E for N in K.missing if N & E])
    J = Complex.create(K.n+1, lists([E] + [N for N in K.missing if not E <= N] +
                                     [R | {K.n} for R in residues]))
    inherited = {N-E for N in common}
    newborn = [R | {K.n} for R in residues if len(R) >= 2 and R not in inherited]
    debt = sum(len(N)-2 for N in newborn)
    require(J.weight() == K.weight()-len(common)+debt, 'exact defect balance failed')
    # Necessary AND sufficient shielding criterion. A one-sided higher
    # nonface cannot be suppressed by an old nonface inside its proper face.
    blockers = [M for M in K.missing if M & E and (len(M) == 2 or E <= M)]
    shields = []
    unshielded = []
    for N in K.higher():
        if len(N & E) != 1:
            continue
        M = next((M for M in blockers if M-E <= N-E), None)
        if M is None:
            unshielded.append(N)
        else:
            shields.append({'nonface': sorted(N), 'blocker': sorted(M)})
    require((not unshielded) == (not newborn), 'shielding equivalence failed')
    info = {'edge': sorted(E), 'new_label': K.n,
            'weight_before': K.weight(), 'weight_after': J.weight(),
            'consumed_higher_nonfaces': len(common),
            'created_higher_weight': debt, 'created_higher_nonfaces': lists(newborn),
            'shielded': not unshielded, 'shield_witnesses': shields,
            'unshielded_one_sided_nonfaces': lists(unshielded)}
    return J, info


def productive_edges(K):
    return sorted(set(E for N in K.higher() for E in combinations(sorted(N), 2)))


def choices(K, policy):
    require(policy in ('twins', 'shielded', 'budget'), 'unknown refinement policy')
    out = []
    H = K.higher()
    for E in productive_edges(K):
        if policy == 'twins' and any((E[0] in N) != (E[1] in N) for N in H):
            continue
        J, proof = account(K, E)
        if policy in ('twins', 'shielded') and not proof['shielded']:
            continue
        if J.weight() < K.weight():
            out.append((J, proof))
    return sorted(out, key=lambda z: (z[0].weight(), len(z[0].higher()), z[1]['edge']))


def refine(K, policy='budget', step_cap=1000, candidate_cap=200000):
    require(type(step_cap) is int and step_cap >= 0 and type(candidate_cap) is int and
            candidate_cap >= 0, 'nonnegative integer caps required')
    original = K; steps = []; tested = 0; status = 'flag'
    while K.higher():
        if len(steps) >= step_cap:
            status = 'step_cap'; break
        count = len(productive_edges(K))
        if tested+count > candidate_cap:
            status = 'candidate_cap'; break
        tested += count
        available = choices(K, policy)
        if not available:
            status = 'stalled'; break
        K, proof = available[0]; steps.append(proof)
    packet = {'format': 'stellar-defect-budget-v1', 'input_sha256': fingerprint(original),
              'policy': policy, 'steps': steps, 'status': status,
              'terminal': K.payload(), 'candidate_edges_examined': tested}
    verify(original, packet)
    return packet


def verify(K, packet):
    """Check only supplied finite set identities, not discovery or route search.

    For stalled status inspect all productive edges to certify a LOCAL stall.
    A capped/partial packet never obtains a completed flag-refinement verdict.
    """
    require(packet['format'] == 'stellar-defect-budget-v1' and
            packet['input_sha256'] == fingerprint(K), 'changed initial complex')
    policy = packet['policy']
    require(policy in ('twins', 'shielded', 'budget'), 'invalid policy')
    initial = K.weight(); created = consumed = 0; mixed = 0
    for s in packet['steps']:
        E = s['edge']
        if policy == 'twins':
            require(all((E[0] in N) == (E[1] in N) for N in K.higher()), 'not a twin move')
        J, actual = account(K, E)
        require(s == actual and actual['consumed_higher_nonfaces'] > 0, 'forged step accounting')
        if policy != 'budget':
            require(actual['shielded'], 'unshielded move in no-splitting policy')
        require(J.weight() < K.weight(), 'refinement step does not decrease integer weight')
        created += actual['created_higher_weight']
        consumed += actual['consumed_higher_nonfaces']; mixed += not actual['shielded']
        K = J
    require(K.payload() == packet['terminal'], 'incorrect terminal nonfaces')
    status = packet['status']
    require(status in ('flag', 'stalled', 'step_cap', 'candidate_cap', 'partial'), 'invalid result status')
    if status == 'flag':
        require(not K.higher(), 'nonflag output labeled complete')
    if status == 'stalled':
        require(K.higher() and not choices(K, policy), 'false local-stall claim')
    require(K.weight() == initial-consumed+created and
            len(packet['steps']) <= initial-K.weight(), 'telescoping integer descent failed')
    return {'status': 'PASS', 'completion': status, 'initial_weight': initial,
            'remaining_weight': K.weight(), 'stellar_steps': len(packet['steps']),
            'mixed_steps_creating_higher_nonfaces': mixed,
            'total_consumed_higher_nonfaces': consumed, 'total_created_higher_weight': created,
            'refined_vertices': K.n, 'flag': not K.higher(),
            'scope': 'Finite-complex refinement certificate. Normality/polytopality is not inferred; no universal polynomial original-facet bound.'}


def cyclic_four_schedule(n):
    """Explicit shielded flagification of the boundary of C(n,4), n >= 6.

    This family input is the stable-triple description of the cycle. Phase one
    eliminates every higher triple containing cyclic distance-two neighbors.
    Afterwards every remaining productive original edge is shielded. All moves
    use original labels, once per pair, so at most n*(n-3)/2 are required.
    This special-family theorem is not a universal refinement guarantee.
    """
    require(type(n) is int and n >= 6, 'cyclic four-dimensional family needs n >= 6')
    high = [T for T in combinations(range(n), 3)
            if all((a-b) % n not in (1, n-1) for a, b in combinations(T, 2))]
    original = K = Complex.create(n, high); steps = []
    for i in range(n):
        E = sorted(((i-1) % n, (i+1) % n))
        if any(set(E) <= N for N in K.higher()):
            K, s = account(K, E)
            require(s['shielded'], 'cyclic neighbor-pair shielding failed')
            steps.append(s)
    first_phase = len(steps)
    while K.higher():
        E = sorted(K.higher()[0])[:2]
        K, s = account(K, E)
        require(s['shielded'] and max(E) < n, 'residual original-edge shielding failed')
        steps.append(s)
    require(len(steps) <= n*(n-3)//2 and len({tuple(s['edge']) for s in steps}) == len(steps),
            'quadratic distinct original-pair budget failed')
    packet = {'format': 'stellar-defect-budget-v1', 'input_sha256': fingerprint(original),
              'policy': 'shielded', 'steps': steps, 'status': 'flag', 'terminal': K.payload(),
              'candidate_edges_examined': None}
    verify(original, packet)
    return original, packet, {'original_vertices': n, 'original_higher_triples': len(high),
                             'neighbor_pair_steps': first_phase, 'total_steps': len(steps),
                             'refined_vertices': K.n, 'quadratic_refined_vertex_bound': n*(n-1)//2}


def subdivide_facets(facets, edge, z):
    """Literal geometric stellar operation, used for transport/reference tests."""
    E = frozenset(edge)
    return ordered([Q for F in facets for Q in
                    ([F] if not E <= F else [(F-{v}) | {z} for v in sorted(E)])])


def lift_pair(F, H, steps):
    # Same compatible-lift convention as #261; original common labels are preserved.
    for s in steps:
        E, z = frozenset(s['edge']), s['new_label']; oldF, oldH = F, H
        if E <= oldF:
            drop = max(E-oldH) if E-oldH else max(E)
            F = (oldF-{drop}) | {z}
        if E <= oldH:
            drop = max(E-oldF) if E-oldF else max(E)
            H = (oldH-{drop}) | {z}
    return F, H


def transport(K, steps, refined_path, d):
    """Push a provided refined path to the original complex; no BFS here."""
    stages = [K]
    for s in steps:
        K, actual = account(K, s['edge'])
        require(actual == s, 'transport uses an unverified stellar step')
        stages.append(K)
    P = [frozenset(S) for S in refined_path]
    require(P and all(len(F) == d and K.face(F) for F in P), 'invalid refined facets')
    require(all(len(F & H) == d-1 for F, H in zip(P, P[1:])), 'refined nonedge')
    for index in reversed(range(len(steps))):
        E, z = frozenset(steps[index]['edge']), steps[index]['new_label']
        P = [(F-{z}) | E if z in F else F for F in P]
        require(all(len(F) == d and stages[index].face(F) for F in P), 'nonmaximal original carrier')
        require(all(F == H or len(F & H) == d-1 for F, H in zip(P, P[1:])), 'carrier introduces a chord')
    result = [P[0]]
    for F in P[1:]:
        if F != result[-1]: result.append(F)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('input', type=Path)
    p.add_argument('--output', type=Path, required=True); p.add_argument('--certificate', type=Path)
    p.add_argument('--policy', choices=['twins', 'shielded', 'budget'], default='budget')
    p.add_argument('--step-cap', type=int, default=1000)
    a = p.parse_args()
    try:
        data = json.loads(a.input.read_text()); K = Complex.create(data['vertices'], data['minimal_nonfaces'])
        packet = json.loads(a.certificate.read_text()) if a.certificate else refine(K, a.policy, a.step_cap)
        out = {'certificate': packet, 'verified': verify(K, packet)}
        a.output.write_text(json.dumps(out, sort_keys=True, indent=2)+'\n')
    except (ValueError, KeyError, TypeError, IndexError, OSError) as e:
        p.exit(2, f'No verified refinement: {e}\n')

if __name__ == '__main__': main()
