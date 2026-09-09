#!/usr/bin/env python3
"""Exact certificates for apex-preserving cone-face descent.

The general theorem is proved separately in ConeCarrierDescent.md. These
finite tests enumerate rational vertices/rays and construct parent-edge paths.
Only Python's standard library is needed; run without -O (assertions verify).
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, deque
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
from math import comb
from pathlib import Path

from test_face_preserving_checkpoints import Poly, point, dot, rank, dantzig_polars
from pointed_polyhedron_exact import PointedPolyhedron, recession_rays, orthant_rows


def budget(m: int, k: int) -> int:
    """Explicit improved eccentricity budget for carrier dimension k<=m."""
    assert 0 <= k <= m
    if k <= 1:
        return k
    return (m + 2) // 2 + sum(comb(m, j) for j in range(3, k + 1))


class CarrierCertificate:
    def __init__(self, cone: PointedPolyhedron, cuts):
        assert len(cone.v) == 1
        self.cone = cone
        self.o = cone.v[0]
        assert all(dot(a, self.o) == b for a, b in cone.rows)
        self.cuts = [(point(a), Q(b)) for a, b in cuts]
        assert all(dot(a, self.o) < b for a, b in self.cuts), 'apex must be strictly retained'
        self.m = len(self.cuts)
        self.r = rank([a for a, _ in self.cuts])
        self.P = Poly(cone.rows + self.cuts)
        assert not recession_rays(self.P.rows, cone.d), 'final polytope must be bounded'
        self.root = self.P.v.index(self.o)
        self.old_tight = [cone.active(v) for v in self.P.v]
        self.dim = [cone.d - rank([cone.rows[i][0] for i in t]) for t in self.old_tight]
        self.new_tight = [frozenset(i for i, (a, b) in enumerate(self.cuts) if dot(a, v) == b)
                          for v in self.P.v]
        for v, k in enumerate(self.dim):
            old = [cone.rows[i][0] for i in self.old_tight[v]]
            new = [self.cuts[i][0] for i in self.new_tight[v]]
            assert rank(old + new) == cone.d
            assert k <= rank(new) <= self.r <= self.m
        self.shells = {}
        self.routes = {}
        self.records = {}

    def shell(self, v: int):
        J, k, P = self.old_tight[v], self.dim[v], self.P
        if J in self.shells:
            return self.shells[J]
        face = P.face(J)
        assert self.root in face and v in face
        assert P.face_dim(face) == k
        interior = frozenset(w for w in face if self.old_tight[w] == J)
        boundary = face - interior
        assignments = {}
        for w in sorted(interior):
            old = [self.cone.rows[i][0] for i in J]
            selected = next((ids for ids in combinations(sorted(self.new_tight[w]), k)
                             if rank(old + [self.cuts[i][0] for i in ids]) == self.cone.d), None)
            assert selected is not None
            assert selected not in assignments, 'two vertices assigned one independent cut basis'
            assignments[selected] = w
        assert len(interior) <= comb(self.m, k)
        if k:
            assert self.root in boundary
            assert all(self.dim[w] < k for w in boundary)
        if k == 1:
            assert len(face) == 2
            assert self.root in P.graph[v]
        if k == 2:
            assert len(face) <= self.m + 2
            assert all(len(P.graph[w] & face) == 2 for w in face)
        result = (k, face, interior, boundary, assignments)
        self.shells[J] = result
        return result

    def route(self, v: int) -> list[int]:
        if v in self.routes:
            return self.routes[v]
        P, k = self.P, self.dim[v]
        if k == 0:
            assert v == self.root
            route, records = [v], []
        elif k <= 2:
            _, face, interior, _, _ = self.shell(v)
            route = P.path(v, self.root, face)
            records = [{'dimension': k, 'kind': 'ray' if k == 1 else 'polygon',
                        'carrier_vertices': len(face), 'interior_vertices': len(interior),
                        'prefix_edges': len(route) - 1}]
        else:
            _, face, interior, boundary, _ = self.shell(v)
            prev, queue, target = {v: None}, deque([v]), None
            while queue and target is None:
                a = queue.popleft()
                assert a in interior
                for b in sorted(P.graph[a] & face):
                    if b in prev:
                        continue
                    prev[b] = a
                    if b in boundary:
                        target = b
                        break
                    queue.append(b)
            assert target is not None
            prefix = [target]
            while prefix[-1] != v:
                prefix.append(prev[prefix[-1]])
            prefix.reverse()
            assert len(prefix) == len(set(prefix))
            assert set(prefix[:-1]) <= interior
            assert len(prefix) - 1 <= len(interior) <= comb(self.m, k)
            assert self.dim[target] < k
            tail = self.route(target)
            route = prefix + tail[1:]
            records = [{'dimension': k, 'kind': 'first_boundary', 'carrier_vertices': len(face),
                        'interior_vertices': len(interior), 'prefix_edges': len(prefix) - 1,
                        'next_dimension': self.dim[target]}] + self.records[target]
        assert route[0] == v and route[-1] == self.root
        assert len(route) == len(set(route)), 'nested-carrier route should be simple'
        assert all(b in P.graph[a] for a, b in zip(route, route[1:]))
        assert len(route) - 1 <= budget(self.m, k)
        assert len(route) - 1 <= sum(comb(self.m, j) for j in range(1, k + 1))
        self.routes[v], self.records[v] = route, records
        return route

    def run(self, name: str):
        P = self.P
        for v in range(len(P.v)):
            self.route(v)
        pairs = 0
        for u, v in combinations_with_replacement(range(len(P.v)), 2):
            path = self.routes[u] + self.routes[v][-2::-1]
            assert path[0] == u and path[-1] == v
            assert all(b in P.graph[a] for a, b in zip(path, path[1:]))
            assert len(path) - 1 <= budget(self.m, self.dim[u]) + budget(self.m, self.dim[v])
            pairs += 1
        far = max(range(len(P.v)), key=lambda v: len(self.routes[v]))
        old_budget = 1 + sum(P.diameter(P.face([len(self.cone.rows) + i])) for i in range(self.m))
        return {'name': name, 'dimension': P.d, 'old_rows': len(self.cone.rows),
                'old_rays': len(self.cone.rays), 'new_cuts': self.m, 'new_normal_rank': self.r,
                'max_carrier_dimension': max(self.dim),
                'carrier_dimension_counts': dict(sorted(Counter(map(str, self.dim)).items())),
                'vertices': len(P.v), 'pairs': pairs, 'carriers_certified': len(self.shells),
                'independent_basis_certificates': sum(len(x[4]) for x in self.shells.values()),
                'constructed_max_apex_route': len(self.routes[far]) - 1,
                'actual_apex_eccentricity': max(P.distances(self.root).values()),
                'actual_diameter': P.diameter(), 'explicit_apex_budget': budget(self.m, self.r),
                'explicit_diameter_budget': 2 * budget(self.m, self.r),
                'previous_final_face_budget': old_budget,
                'witness_route': [[str(x) for x in P.v[w]] for w in self.routes[far]],
                'witness_descent': self.records[far]}


def polygon_cone(n: int):
    rows = [(point([2 * i + 1, -1, -i * (i + 1)]), Q(0)) for i in range(n - 1)]
    rows += [(point([-(n - 1), 1, 0]), Q(0))]
    return PointedPolyhedron(rows)


def cube_cone(d: int):
    rows = []
    for i in range(d - 1):
        a = [0] * d
        a[i] = -1
        rows.append((point(a), Q(0)))
        a[i], a[-1] = 1, -1
        rows.append((point(a), Q(0)))
    return PointedPolyhedron(rows)


def rank_two_caps(h, g, m: int):
    out = []
    for j in range(m):
        t = 2 * Q(j, m - 1) - 1 if m > 1 else Q(0)
        out.append((point([(3 - t * t) * a + 2 * t * b for a, b in zip(h, g)]), Q(1)))
    return out


def instances():
    for n in (4, 8, 12, 16, 24):
        cone = polygon_cone(n)
        yield f'pyramid{n}', cone, [(point([0, 0, 1]), Q(1))]
        if n <= 12:
            h, g = point([0, 0, 1]), point([Q(2, n - 1), 0, -1])
            yield f'polygon{n}_rank2', cone, rank_two_caps(h, g, 2)
    for d in (2, 3, 4, 5, 6):
        cone = PointedPolyhedron(orthant_rows(d))
        h = point([1] * d)
        g = point([2 * Q(i, d - 1) - 1 for i in range(d)])
        for m in (2, 4, 6):
            yield f'orthant{d}_rank2_m{m}', cone, rank_two_caps(h, g, m)
    for d in (4, 5):
        cone = cube_cone(d)
        h = point([0] * (d - 1) + [1])
        g = point([2] + [0] * (d - 2) + [-1])
        for m in (2, 5):
            yield f'cubecone{d}_rank2_m{m}', cone, rank_two_caps(h, g, m)
    for d in (3, 4, 5):
        cone = PointedPolyhedron(orthant_rows(d))
        h = point([1] * d)
        g = point([2 * Q(i, d - 1) - 1 for i in range(d)])
        z = point([(-1) ** i for i in range(d)])
        pars = [(-1, -1), (-1, 1), (1, -1), (1, 1), (0, 0), (0, 1), (1, 0)]
        cuts = [(point([(6 - s*s - t*t)*a + 2*s*b + 2*t*c for a,b,c in zip(h,g,z)]),Q(1))
                for s,t in pars]
        for m in (4, 7):
            yield f'orthant{d}_rank3_m{m}', cone, cuts[:m]
    for d in (3, 4):
        cuts = [(point([int(i == j) for j in range(d)]), Q(1)) for i in range(d)]
        yield f'orthant{d}_box', PointedPolyhedron(orthant_rows(d)), cuts
    for poly in dantzig_polars():
        designated = frozenset([3,4,5,6]) if poly.d == 4 else frozenset([0,1,2,3,5])
        roots = sorted(set(([0, len(poly.v)-1] if poly.d == 4 else [0]) + [poly.tight.index(designated)]))
        for root in roots:
            active = poly.tight[root]
            cone = PointedPolyhedron([row for i,row in enumerate(poly.rows) if i in active])
            cuts = [row for i,row in enumerate(poly.rows) if i not in active]
            yield f'Dantzig{poly.d}_root{root}', cone, cuts


def strict_apex_obstruction():
    result = []
    for n in (4, 8, 12, 16, 24):
        cone = polygon_cone(n)
        cuts = [(point([0,0,1]),Q(2)),(point([0,0,-1]),Q(-1))]
        P = Poly(cone.rows + cuts)
        assert rank([a for a,_ in cuts]) == 1
        assert cone.v[0] not in P.v and not P.feasible(cone.v[0])
        assert len(P.v) == 2*n and not recession_rays(P.rows,3)
        assert P.diameter() == n//2+1
        result.append({'base_vertices':n,'cut_rank':1,'final_vertices':len(P.v),
                       'final_diameter':P.diameter(),'strictly_retained_apex':False})
    return result


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--filter',default='')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if not __debug__:
        raise RuntimeError('Do not use Python -O: assertions verify the certificates')
    results=[]
    for name,cone,cuts in instances():
        if args.filter not in name:
            continue
        print('checking',name,file=sys.stderr,flush=True)
        results.append(CarrierCertificate(cone,cuts).run(name))
    report={'results':results,'totals':{'instances':len(results),
            'vertices':sum(r['vertices'] for r in results),'pairs':sum(r['pairs'] for r in results),
            'carriers_certified':sum(r['carriers_certified'] for r in results),
            'independent_basis_certificates':sum(r['independent_basis_certificates'] for r in results)},
            'strict_apex_obstruction':strict_apex_obstruction() if not args.filter else [],
            'all_constructed_routes_within_explicit_budget':True,
            'general_theorem_proved_by_tests':False,'lean_verified':False}
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    else:
        print(text,end='')

if __name__=='__main__':
    main()
