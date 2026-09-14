#!/usr/bin/env python3
"""Hide the target facets during an exponential canonical normalized-gain phase.

Research example, NOT an exponential graph-diameter claim. The explicit input
has 3d genuine ORIGINAL facets and a d-edge comparison route. Before the first
new target facet is acquired, the current/target midpoint is strictly interior,
so adaptive common-face locking cannot change the canonical active-row policy.
The #248 default LP-produced height is a different policy and is not replayed.

The unchanged #249 auditor independently checks every normalized step, original
row inverse identity and maximal original endpoint. This file does not change
its height or claim a polynomial simplex algorithm. No Lean verdict is implied.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse, json
import simple_tangent_policy_audit as old

require, dot, serial = old.require, old.dot, old.serial


def original_cube(d):
    require(type(d) is int and d >= 2, 'dimension must be an integer >= 2')
    A = [[-int(i == j) for j in range(d)] for i in range(d)]
    A += [[0 if j > i else 1 if j == i else 2**(i-j+1)
           for j in range(d)] for i in range(d)]
    return A, [0]*d + [5**(i+1) for i in range(d)]


def cube_vertex(d, index):
    require(type(index) is int and 0 <= index < 2**d, 'Gray index out of range')
    code = index ^ (index >> 1)
    bits = [(code >> i) & 1 for i in range(d)]
    x = []
    for i, bit in enumerate(bits):
        x.append(bit*(5**(i+1)-sum(2**(i-j+1)*x[j] for j in range(i))))
    return x, bits


def cube_basis(d, index):
    """Triangular recurrence as a producer, checked against the original rows."""
    x, bits = cube_vertex(d, index)
    J = sorted(i+d if bits[i] else i for i in range(d))
    D = []
    for released in J:
        coordinate = released % d
        v = []
        for i, bit in enumerate(bits):
            rhs = -int(i == coordinate)
            v.append(rhs-sum(2**(i-j+1)*v[j] for j in range(i)) if bit else -rhs)
        D.append(v)
    return {'point': x, 'active': J, 'directions': D}


def roof_input(d):
    A, b = original_cube(d)
    c = [2**(d-1-j) for j in range(d)]
    epsilon = Q(1, 64*d*5**d)
    y = [epsilon*2**j for j in range(d-1)] + [Q(5**d)-Q(1, 4)]
    for j in range(d-1):
        row = [Q(x) for x in c]; row[j] += epsilon
        A.append(row); b.append(dot(row, y))
    row = [Q(x)-epsilon*int(j < d-1) for j, x in enumerate(c)]
    A.append(row); b.append(dot(row, y))
    target = old.basis_packet(A, b, y)
    target['weights'] = [Q(1, d)]*d
    old.audit_target(A, b, c, target)
    require(target['active'] == list(range(2*d, 3*d)), 'target must use only new roof rows')
    return {'A': A, 'b': b, 'objective': c, 'start': [0]*d,
            'target': target, 'epsilon': epsilon}


def strict_midpoint(A, b, x, y):
    """A strict midpoint proves the smallest common face is the WHOLE polytope."""
    require(len(x) == len(y) == len(A[0]), 'midpoint shape')
    mid = [(u+v)/2 for u, v in zip(map(Q, x), map(Q, y))]
    require(all(dot(a, mid) < z for a, z in zip(A, b)), 'current/target common face is not full')
    return mid


def audit_phase_step(data, step):
    A, b, c, _, target = old.decode_input(serial(data))
    y = old.audit_target(A, b, c, target)
    strict_midpoint(A, b, step['basis']['point'], y)
    result = old.audit_step(A, b, c, step, 'normalized')
    scores = [dot(c, v) for v in step['basis']['directions']]
    require(sum(s == max(scores) for s in scores) == 1, 'selected direction must be uniquely best')
    common_after = sorted(set(old.active_rows(A, b, result)) & set(target['active']))
    return {'to': result, 'target_rows_after': common_after}


def phase_step(data, index):
    d = len(data['start']); require(index < 2**d-1, 'removed optimum is not a phase source')
    return old.make_step(data['A'], data['b'], data['objective'], cube_basis(d, index), 'normalized')


def execute_phase(d, edge_cap=10000, keep=False):
    """Execute only up to first acquisition, not an untested completed route."""
    require(type(edge_cap) is int and edge_cap >= 2**d-1, 'phase cap; no complete phase certificate')
    data = roof_input(d); A, b, c, target = data['A'], data['b'], data['objective'], data['target']
    old.audit_target(A, b, c, target)
    steps = []; before = 0; gain = None
    for index in range(2**d-1):
        s = phase_step(data, index)
        # Do not recreate input or inverses inside the unchanged arithmetic auditor.
        strict_midpoint(A, b, s['basis']['point'], target['point'])
        z = old.audit_step(A, b, c, s, 'normalized')
        scores = [dot(c, v) for v in s['basis']['directions']]
        require(scores.count(max(scores)) == 1, 'nonunique normalized gain')
        hit = set(old.active_rows(A, b, z)) & set(target['active'])
        if index < 2**d-2:
            require(z == cube_vertex(d, index+1)[0] and not hit, 'premature cap or changed Gray successor')
            strict_midpoint(A, b, z, target['point']); before += 1
        else:
            require(bool(hit) and z != target['point'], 'wrong first acquired roof edge')
            require(s['blocker'] in target['active'], 'first acquisition must be an original roof blocker')
        value = dot(c, z)-dot(c, s['basis']['point'])
        gain = value if gain is None else min(gain, value)
        if keep: steps.append(s)
    result = {'status': 'PASS', 'dimension': d, 'original_facets': 3*d,
              'executed_original_edges_to_first_target_facet': 2**d-1,
              'executed_edges_with_full_common_face_at_both_ends': before,
              'strict_current_target_midpoints': 2**d-1,
              'first_acquisition_rows': sorted(hit), 'phase_exit': z,
              'least_objective_gain': gain,
              'complete_route_to_target_claimed': False,
              'policy': 'canonical -sum(active original rows), normalized gain',
              'default_image_selector_replayed': False}
    return data, result, steps


def comparison_route(data):
    """Explicit d-edge monotone path on the LAST new roof facet; not a diagonal."""
    A, b, c = data['A'], data['b'], data['objective']
    y = data['target']['point']; d = len(y); eps = data['epsilon']; total = sum(y[:-1])
    path = [list(data['start'])]
    for size in range(d):
        missing = sum(y[size:-1], Q(0)); p = [y[j]+missing/(size+1) if j < size else Q(0) for j in range(d-1)]
        p.append(dot(c, y)-eps*total-sum((c[j]-eps)*p[j] for j in range(d-1)))
        path.append(p)
    require(path[-1] == y and len(path)-1 == d, 'comparison route endpoint/count')
    steps = []
    for x, z in zip(path, path[1:]):
        basis = old.basis_packet(A, b, x)
        delta = [v-u for u, v in zip(x, z)]
        candidates = []
        for i, ray in enumerate(basis['directions']):
            k = next(j for j, v in enumerate(ray) if v)
            alpha = delta[k]/ray[k]
            if alpha > 0 and delta == [alpha*v for v in ray]: candidates.append((i, alpha))
        require(len(candidates) == 1, 'comparison segment is not an original incident ray')
        i, alpha = candidates[0]; length, blocker = old.maximal_step(A, b, x, basis['directions'][i])
        require(length == alpha, 'comparison point is not the maximal original endpoint')
        s = {'basis': basis, 'selected': i, 'length': length, 'blocker': blocker, 'to': z}
        audit_any_edge(A, b, c, s); steps.append(s)
    return {'steps': steps, 'edges': d, 'route': path}


def audit_any_edge(A, b, c, s):
    x, J, D = old.audit_basis(A, b, s['basis']); i = s['selected']
    require(type(s['length']) in (int, Q) and type(s['blocker']) is int, 'inexact edge parameters')
    require(len(s['to']) == len(x) and all(type(v) in (int, Q) for v in s['to']), 'inexact edge endpoint')
    require(type(i) is int and 0 <= i < len(D), 'bad selected ray')
    length, blocker = old.maximal_step(A, b, x, D[i])
    require(length > 0 and length == s['length'] and blocker == s['blocker'], 'not a full original edge')
    z = [a+length*v for a, v in zip(x, D[i])]
    require(z == s['to'] and old.feasible(A, b, z), 'invalid original endpoint')
    require(all(dot(A[j], z) == b[j] for j in J if j != J[i]), 'lost a common independent original row')
    require(dot(c, z) > dot(c, x), 'comparison route not monotone')
    return z


def facet_anchors(data):
    """A point tight on exactly each ORIGINAL row proves its facet is genuine."""
    A, b = data['A'], data['b']; d = len(data['start']); out = []
    for row in range(3*d):
        if row < d: base = cube_basis(d, 0)
        elif row < 2*d:
            coordinate = row-d
            bits = (1 << coordinate) if coordinate != d-1 else (1 << (d-1)) | 1
            # Binary reflected Gray inversion, used only to locate a feasible anchor.
            index = 0; g = bits
            while g: index ^= g; g >>= 1
            base = cube_basis(d, index)
        else: base = data['target']
        x, J, D = old.audit_basis(A, b, base); require(row in J, 'anchor base not on requested facet')
        direction = [sum(v[k] for j, v in zip(J, D) if j != row) for k in range(d)]
        alpha, _ = old.maximal_step(A, b, x, direction)
        point = [u+alpha*v/2 for u, v in zip(x, direction)]
        require(old.active_rows(A, b, point) == [row] and old.feasible(A, b, point), 'nonfacet or bad relative interior anchor')
        out.append(point)
    interior = strict_midpoint(A, b, data['start'], data['target']['point'])
    return {'relative_interior_points': out, 'strict_interior_point': interior}


def full_gain_comparator(data, edge_cap=10000):
    out = old.construct(data['A'], data['b'], data['objective'], data['start'], data['target'], 'full_gain', edge_cap)
    report = old.audit_route(data['A'], data['b'], data['objective'], data['start'], data['target'], out)
    target = set(data['target']['active']); lost = 0
    for s in out['steps']:
        before = set(s['basis']['active']) & target
        after = set(old.active_rows(data['A'], data['b'], s['to'])) & target
        lost += len(before-after)
    return {'certificate': out, 'verified': {**report, 'target_facets_lost': lost,
            'scope': 'Executed classical completed-gain comparator, not a universal polynomial guarantee.'}}



def audit_locked_step(A, b, c, target, step):
    """Certify optimality on the CURRENT common-face tangent slice.

    Locked rows are equalities: their dual coefficients may have either sign.
    All other dual coefficients must be nonnegative. No inverse or LP is run.
    """
    x, J, D = old.audit_basis(A, b, step['basis'])
    locked = set(J) & set(target['active'])
    scores = [dot(c, v) for v in D]
    eligible = [j for j, row in enumerate(J) if row not in locked and scores[j] > 0]
    require(eligible, 'no admissible improving face ray')
    chosen = step['selected']
    require(type(chosen) is int and chosen in eligible, 'selected ray drops an acquired target facet')
    maximum = max(scores[j] for j in eligible)
    require(scores[chosen] == maximum and sum(scores[j] == maximum for j in eligible) == 1,
            'not a unique maximum on the locked face')
    z = audit_any_edge(A, b, c, step)
    require(locked <= set(old.active_rows(A, b, z)), 'target face was lost')
    dual = [scores[chosen]-v for v in scores]
    require(all(w >= 0 for row, w in zip(J, dual) if row not in locked), 'invalid face optimum dual signs')
    height = [-sum(A[row][k] for row in J) for k in range(len(x))]
    require(all(c[k] == scores[chosen]*height[k] + sum(dual[j]*A[row][k] for j, row in enumerate(J))
                for k in range(len(x))), 'false whole face-slice support identity')
    return z


def make_locked_step(data, x):
    A, b, c, target = data['A'], data['b'], data['objective'], data['target']
    basis = old.basis_packet(A, b, x); J, D = basis['active'], basis['directions']
    locked = set(J) & set(target['active'])
    eligible = [j for j, row in enumerate(J) if row not in locked and dot(c, D[j]) > 0]
    require(eligible, 'no improving ray in current common face')
    i = max(eligible, key=lambda j: dot(c, D[j]))
    length, blocker = old.maximal_step(A, b, x, D[i])
    z = [v+length*w for v, w in zip(x, D[i])]
    step = {'basis': basis, 'selected': i, 'length': length, 'blocker': blocker, 'to': z}
    audit_locked_step(A, b, c, target, step)
    return step


def audit_locked_route(data, steps):
    A, b, c, target = data['A'], data['b'], data['objective'], data['target']
    require(A and len(A) == len(b) and all(len(a) == len(c) for a in A), 'wrong H shape')
    require(all(type(v) in (int, Q) for a in A for v in a) and
            all(type(v) in (int, Q) for v in b+c+list(data['start'])), 'inexact original data')
    old.audit_target(A, b, c, target)
    x = list(data['start']); first = None; constant = 0; seen = {tuple(x)}
    for i, s in enumerate(steps):
        require(s['basis']['point'] == x, 'discontinuous locked route')
        common = set(old.active_rows(A, b, x)) & set(target['active'])
        if not common: strict_midpoint(A, b, x, target['point'])
        z = audit_locked_step(A, b, c, target, s)
        require(tuple(z) not in seen, 'repeated route vertex'); seen.add(tuple(z))
        after = set(old.active_rows(A, b, z)) & set(target['active'])
        if not common and not after: constant += 1
        if first is None and after: first = i+1
        x = z
    require(x == target['point'], 'locked route does not reach the requested target')
    return {'status': 'PASS', 'edges': len(steps), 'first_target_facet_after_edges': first,
            'full_common_face_edges': constant, 'target_faces_lost': 0,
            'strictly_monotone': True, 'original_rows': len(A), 'dimension': len(x),
            'default_image_selector_replayed': False}


def execute_locked(d, edge_cap=10000):
    require(type(edge_cap) is int and edge_cap >= 2**d+d-2, 'locked route cap; no complete route')
    data, phase, steps = execute_phase(d, edge_cap, keep=True)
    x = steps[-1]['to']; tail = 0
    while x != data['target']['point']:
        require(len(steps) < edge_cap, 'locked route cap')
        s = make_locked_step(data, x); steps.append(s); x = s['to']; tail += 1
    require(tail == d-1, 'roof-tail recurrence disagreement')
    report = audit_locked_route(data, steps)
    require(report['edges'] == 2**d+d-2 and report['full_common_face_edges'] == 2**d-2,
            'executed count disagrees with derived formula')
    return data, {'steps': steps, 'verified': report, 'phase': phase}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--dimension', type=int, default=5)
    p.add_argument('--edge-cap', type=int, default=10000)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    try:
        data, phase, steps = execute_phase(args.dimension, args.edge_cap, keep=True)
        output = {'input': data, 'phase': phase, 'phase_steps': steps,
                  'comparison': comparison_route(data), 'facet_anchors': facet_anchors(data)}
        args.output.write_text(json.dumps(serial(output), indent=2)+'\n')
    except (ValueError, KeyError, TypeError, ZeroDivisionError, OSError) as exc:
        p.exit(2, f'No complete phase certificate: {exc}\n')

if __name__ == '__main__': main()
