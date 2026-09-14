#!/usr/bin/env python3
"""Exact original-H regression: a short extension route may project to chords.

Classical Klee--Minty shadow construction of Gaertner--Helbling--Ota--Takahashi,
arXiv:1308.2495, Definition 11 / Lemma 12. This is NOT a new diameter theorem.
The audit supplies original-row positive support multipliers for all enumerated
vertices and checks the image polygon independently by an exact planar hull.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse, hashlib, json, random, time

ROOT = Path(__file__).resolve().parents[1]


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def vertex(bits: tuple[int, ...], eps: Q) -> tuple[Q, ...]:
    out = []
    prev = Q(0)
    for bit in bits:
        prev = bit + (1 - 2 * bit) * eps * prev
        out.append(prev)
    return tuple(out)


def normal_rows(d: int, eps: Q):
    rows, rhs = [], []
    for j in range(d):
        for bit in (0, 1):
            row = [Q(0)] * d
            row[j] = 2 * bit - 1
            if j:
                row[j - 1] = eps
            rows.append(row)
            rhs.append(Q(bit))
    return rows, rhs


def projection_row(d: int, eps: Q) -> tuple[Q, ...]:
    return tuple(eps ** (3 * (d - j - 1)) if j < d - 1 else Q(0) for j in range(d))


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), Q(0))


def exposing_packet(bits: tuple[int, ...], eps: Q):
    d = len(bits)
    c = projection_row(d, eps)
    # Paper's exposing objective c + tau*e_d; all arithmetic remains rational.
    parity, tau = 1, Q(0)
    for j in reversed(range(d)):
        parity *= 1 - 2 * bits[j]
        tau -= parity * eps ** (2 * (d - j))
    objective = list(c)
    objective[-1] = tau
    multipliers = [Q(0)] * d
    following = Q(0)
    for j in reversed(range(d)):
        following = (2 * bits[j] - 1) * (objective[j] - eps * following)
        multipliers[j] = following
    return {'bits': bits, 'vertex': vertex(bits, eps), 'tau': tau,
            'multipliers': multipliers}


def audit_vertex(d: int, eps: Q, cert):
    require(type(d) is int and d >= 2 and type(eps) in (Q, int) and Q(0) < eps < Q(1, 2), 'invalid construction parameters')
    bits, x, lam = cert['bits'], cert['vertex'], cert['multipliers']
    require(len(bits) == d and all(type(b) is int and b in (0, 1) for b in bits), 'invalid bits')
    require(len(x) == d and len(lam) == d, 'wrong certificate dimension')
    require(all(type(a) in (Q, int) for a in [*x, *lam, cert['tau']]), 'inexact numerical data')
    require(all(a > 0 for a in lam), 'strict exposing multipliers required')
    # Each active matrix is lower triangular with diagonal +-1: full rank.
    # Verify original tightness and strictness of the other row in EVERY pair.
    for j in range(d):
        prev = x[j - 1] if j else Q(0)
        require(0 <= x[j] <= 1, 'coordinate feasibility failed')
        require(eps * prev <= x[j] <= 1 - eps * prev, 'original inequality failed')
        active = (2 * bits[j] - 1) * x[j] + eps * prev
        require(active == bits[j], 'claimed active row not tight')
        other = (1 - 2 * bits[j]) * x[j] + eps * prev
        require(other < 1 - bits[j], 'opposite row not strictly slack')
    # Independent coefficient identity. Positivity plus full active rank proves
    # uniqueness over the ENTIRE original H-polytope, without a vertex list.
    c = projection_row(d, eps)
    for j in range(d):
        value = (2 * bits[j] - 1) * lam[j] + (eps * lam[j + 1] if j + 1 < d else 0)
        require(value == (cert['tau'] if j == d - 1 else c[j]), 'false support objective identity')
    return (dot(c, x), x[-1])


def verify_extension_edge(bits, other, eps):
    d = len(bits)
    require(d >= 2 and d == len(other), 'edge endpoint dimension mismatch')
    require(type(eps) in (Q, int) and 0 < eps < Q(1, 2), 'invalid edge parameter')
    require(all(type(b) is int and b in (0, 1) for b in (*bits, *other)), 'invalid edge bits')
    differing = [j for j in range(d) if bits[j] != other[j]]
    require(len(differing) == 1, 'not an ordinary cube edge')
    removed = differing[0]
    # Deleting the changed active row and its column leaves a lower triangular
    # (d-1)-minor with diagonal +-1. This proves common active rank d-1.
    kept = [j for j in range(d) if j != removed]
    for i in kept:
        require(bits[i] == other[i], 'lost common active row')
        require(abs(2 * bits[i] - 1) == 1, 'singular diagonal minor')
    return True


def projection_edge_packet(bits, other, eps, p, q):
    """A candidate image normal must be perpendicular to the projected segment.
    Test both orientations via exact ORIGINAL active-row support coefficients.
    The search returns None for a projected interior chord, not a fake edge.
    """
    d = len(bits)
    c = projection_row(d, eps)
    direction = (q[0] - p[0], q[1] - p[1])
    require(direction != (0, 0), 'collapsed edge')
    for sign in (1, -1):
        f = (sign * direction[1], -sign * direction[0])
        objective = [f[0] * a for a in c]
        objective[-1] += f[1]
        weights = [Q(0)] * d
        following = Q(0)
        for j in reversed(range(d)):
            following = (2 * bits[j] - 1) * (objective[j] - eps * following)
            weights[j] = following
        if all(weights[j] > 0 if bits[j] == other[j] else weights[j] == 0 for j in range(d)):
            return {'image_normal': f, 'active_weights': weights}
    return None


def audit_projection_edge(bits, other, eps, p, q, cert):
    """Positive common-row support identity exposes the WHOLE preimage edge.
    Its nonconstant linear image is therefore an actual exposed image edge.
    No convex-hull routine or all-vertex support test is called here.
    """
    verify_extension_edge(bits, other, eps)
    d = len(bits)
    f, weights = cert['image_normal'], cert['active_weights']
    require(len(f) == 2 and len(weights) == d and f != (0, 0), 'invalid projected normal')
    require(all(type(x) in (int, Q) for x in (*f, *weights, *p, *q)), 'inexact edge data')
    c = projection_row(d, eps)
    x, y = vertex(bits, eps), vertex(other, eps)
    require(p == (dot(c, x), x[-1]) and q == (dot(c, y), y[-1]), 'image coordinates not bound to original vertices')
    require(p != q and dot(f, p) == dot(f, q), 'false image support equality')
    c = projection_row(d, eps)
    for j in range(d):
        require(weights[j] > 0 if bits[j] == other[j] else weights[j] == 0,
                'normal is not positive on exactly the shared original rows')
        value = (2 * bits[j] - 1) * weights[j] + (eps * weights[j + 1] if j + 1 < d else 0)
        require(value == f[0] * c[j] + (f[1] if j == d - 1 else 0), 'false lifted support identity')
    return True


def cross(o, a, b):
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def hull_indices(points):
    order = sorted(range(len(points)), key=lambda i: points[i])
    require(len({points[i] for i in order}) == len(points), 'projection collision')
    def chain(indices):
        out = []
        for i in indices:
            while len(out) >= 2 and cross(points[out[-2]], points[out[-1]], points[i]) <= 0:
                out.pop()
            out.append(i)
        return out
    return chain(order)[:-1] + chain(reversed(order))[:-1]


def gray_chain(d: int):
    order = [()]
    for _ in range(d):
        order = [u + (0,) for u in order] + [u + (1,) for u in reversed(order)]
    return order


def jsonable(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [jsonable(v) for v in x]
    return x


def main(max_dimension: int):
    require(2 <= max_dimension <= 14, 'full enumeration cap exceeded')
    start = time.monotonic()
    eps = Q(1, 4)
    results = []
    total_vertices = total_edges = direct_lp_checks = exposed_image_edges = rejected_chords = 0
    example = None
    for d in range(2, max_dimension + 1):
        bits = list(product((0, 1), repeat=d))
        ids = {u: i for i, u in enumerate(bits)}
        certs = [exposing_packet(u, eps) for u in bits]
        pts = [audit_vertex(d, eps, c) for c in certs]
        hull = hull_indices(pts)
        require(len(hull) == 2 ** d, 'not every projected point is an extreme vertex')
        h_edges = {frozenset((hull[j], hull[(j + 1) % len(hull)])) for j in range(len(hull))}
        order = gray_chain(d)
        require(all(certs[ids[order[j]]]['vertex'][-1] < certs[ids[order[j + 1]]]['vertex'][-1]
                    for j in range(len(order) - 1)), 'recursive height order failed')
        expected = {frozenset((ids[order[j]], ids[order[(j + 1) % len(order)]])) for j in range(len(order))}
        require(h_edges == expected, 'independent planar hull disagrees with boundary order')
        extension_edges = d * 2 ** (d - 1)
        for i, u in enumerate(bits):
            for j in range(d):
                v = u[:j] + (1 - u[j],) + u[j + 1:]
                if i < ids[v]:
                    verify_extension_edge(u, v, eps)
                    packet = projection_edge_packet(u, v, eps, pts[i], pts[ids[v]])
                    is_boundary = frozenset((i, ids[v])) in h_edges
                    require((packet is not None) == is_boundary, 'original-row certificate disagrees with independent hull')
                    if packet is not None:
                        audit_projection_edge(u, v, eps, pts[i], pts[ids[v]], packet)
                        exposed_image_edges += 1
                    else:
                        rejected_chords += 1
        u, middle, v = (0,) * d, (0,) * (d - 1) + (1,), (0,) * (d - 2) + (1, 1)
        require(order[2 ** (d - 1)] == v, 'explicit opposite-image endpoint changed')
        verify_extension_edge(u, middle, eps)
        verify_extension_edge(middle, v, eps)
        require(frozenset((ids[u], ids[middle])) in h_edges, 'first projected segment not boundary edge')
        if d >= 3:
            require(frozenset((ids[middle], ids[v])) not in h_edges, 'interior projected chord was mislabeled an edge')
        # Separate check of global support values over ALL known points for small d.
        if d <= 5:
            for i, cert in enumerate(certs):
                scores = [p[0] + cert['tau'] * p[1] for p in pts]
                require(all(scores[i] > score for j, score in enumerate(scores) if j != i), 'not unique maximizer')
                direct_lp_checks += len(scores)
        results.append({'dimension': d, 'extension_facets': 2 * d, 'extension_vertices': 2 ** d,
                        'extension_edges': extension_edges, 'image_facets': len(hull),
                        'original_endpoint_distance': 2, 'image_endpoint_distance': 2 ** (d - 1),
                        'projection_injective_on_vertices': True,
                        'projected_extension_edges_that_are_not_image_edges': extension_edges - len(hull)})
        total_vertices += len(certs)
        total_edges += extension_edges
        if d == min(8, max_dimension):
            example = {'dimension': d, 'epsilon': eps, 'projection_first_row': projection_row(d, eps),
                       'projection_second_row': [0] * (d - 1) + [1],
                       'two_edge_extension_route': [certs[ids[w]] for w in (u, middle, v)],
                       'image_boundary_order': order,
                       'image_boundary_points': [pts[ids[w]] for w in order]}
    # Large checks are explicit endpoint/support certificates only. The closed
    # counts below come from the proved classical construction, NOT enumeration.
    rng = random.Random(241)
    large = []
    for d in (16, 32, 64):
        samples = [(0,) * d, (0,) * (d - 1) + (1,), (0,) * (d - 2) + (1, 1)]
        samples += [tuple(rng.randrange(2) for _ in range(d)) for _ in range(8)]
        for u in samples: audit_vertex(d, eps, exposing_packet(u, eps))
        verify_extension_edge(samples[0], samples[1], eps)
        verify_extension_edge(samples[1], samples[2], eps)
        large.append({'dimension': d, 'certificates_checked': len(samples),
                      'enumerated_graph': False, 'proved_image_facets': 2 ** d,
                      'proved_image_endpoint_distance': 2 ** (d - 1), 'extension_route_edges': 2})
    rejected = []
    def reject(name, f):
        try: f()
        except (ValueError, TypeError, KeyError, IndexError): rejected.append(name)
        else: raise AssertionError('accepted forged data: ' + name)
    good = exposing_packet((0, 1, 0, 1), eps)
    for name, mutate in [
        ('wrong_coordinate', lambda c: c['vertex'].__setitem__(0, Q(1))),
        ('zero_support_weight', lambda c: c['multipliers'].__setitem__(0, Q(0))),
        ('wrong_objective', lambda c: c.update(tau=c['tau'] + 1)),
        ('floating_data', lambda c: c.update(tau=float(c['tau']))),
    ]:
        bad = deepcopy(good); bad['vertex'] = list(bad['vertex']); mutate(bad)
        reject(name, lambda bad=bad: audit_vertex(4, eps, bad))
    reject('two_bit_chord', lambda: verify_extension_edge((0, 0, 0), (0, 1, 1), eps))
    reject('degenerate_epsilon', lambda: audit_vertex(4, Q(1, 2), good))
    a, b = (0, 0, 0), (0, 0, 1)
    p = audit_vertex(3, eps, exposing_packet(a, eps))
    q = audit_vertex(3, eps, exposing_packet(b, eps))
    cert = projection_edge_packet(a, b, eps, p, q)
    reject('altered_projected_endpoint', lambda: audit_projection_edge(a, b, eps, p, (q[0], q[1] + 1), cert))
    a, b = (0, 0, 1), (0, 1, 1)
    p = audit_vertex(3, eps, exposing_packet(a, eps))
    q = audit_vertex(3, eps, exposing_packet(b, eps))
    reject('true_lift_edge_false_image_edge', lambda: audit_projection_edge(a, b, eps, p, q,
        {'image_normal': (1, 0), 'active_weights': [1, 1, 1]}))
    report = {'status': 'PASS', 'scope': 'exact rational regression of a classical shadow construction; not Lean verification',
              'reference': 'Gaertner, Helbling, Ota, Takahashi, arXiv:1308.2495, Definition 11 and Lemma 12',
              'full_vertex_support_certificates': total_vertices, 'ordinary_extension_edges_checked': total_edges,
              'independent_all_point_support_comparisons': direct_lp_checks,
              'positive_original_row_image_edge_certificates': exposed_image_edges,
              'genuine_extension_edges_rejected_as_projected_chords': rejected_chords,
              'fully_enumerated_examples': results, 'nonenumerating_certificate_examples': large,
              'rejected_count': len(rejected), 'rejected': rejected,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'seconds': round(time.monotonic() - start, 3)}
    (ROOT / 'research').mkdir(exist_ok=True)
    (ROOT / 'fixtures').mkdir(exist_ok=True)
    (ROOT / 'research/PROJECTION_EDGE_GAP_TESTS.json').write_text(json.dumps(report, indent=2) + '\n')
    (ROOT / 'fixtures/projection_edge_gap_example.json').write_text(json.dumps(jsonable(example), indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-dimension', type=int, default=12)
    main(parser.parse_args().max_dimension)
