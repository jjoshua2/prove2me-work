#!/usr/bin/env python3
"""Exact rational LP discovery with separately checkable primal/dual witnesses.

This is Bland-rule simplex, NOT a polynomial pivot-bound claim. It operates on
an explicit H-system, never enumerates its vertices, and fails explicitly at a
pivot cap. Witness verification below does not invoke simplex or trust floats.
"""
from __future__ import annotations
from fractions import Fraction as Q
import hashlib
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rat(value):
    require(type(value) in (int, str) or isinstance(value, Q),
            'use exact integers or rational strings, not floats/bools')
    return Q(value)


def serial(value):
    if isinstance(value, Q): return str(value)
    if isinstance(value, dict): return {str(k): serial(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)): return [serial(v) for v in value]
    return value


def dot(a, b):
    require(len(a) == len(b), 'vector shape mismatch')
    return sum((x*y for x, y in zip(a, b) if x and y), Q(0))


def parse(A, b):
    require(isinstance(A, (list, tuple)) and A and A[0], 'positive matrix shape required')
    A = tuple(tuple(map(rat, a)) for a in A)
    b = tuple(map(rat, b)); d = len(A[0])
    require(len(A) == len(b) and all(len(a) == d for a in A), 'H-system shape')
    return A, b


def problem_hash(A, b):
    return hashlib.sha256(json.dumps(serial({'A': A, 'b': b}), sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def dense_dual(raw, count):
    require(isinstance(raw, list), 'dual must be a sparse list')
    out = [Q(0)]*count; seen = set()
    for item in raw:
        require(isinstance(item, list) and len(item) == 2, 'invalid sparse dual entry')
        i, v = item
        require(type(i) is int and 0 <= i < count and i not in seen, 'invalid/repeated dual index')
        out[i] = rat(v); seen.add(i)
        require(out[i] > 0, 'sparse dual entries must be positive')
    return tuple(out)


def sparse_dual(values):
    return [[i, serial(v)] for i, v in enumerate(values) if v]


def verify_dual(A, b, objective, raw):
    dual = dense_dual(raw, len(A))
    require(all(sum((v*a[j] for v, a in zip(dual, A)), Q(0)) == objective[j]
                for j in range(len(objective))), 'dual does not reproduce objective')
    return dot(dual, b)


def verify_optimum(A, b, objective, certificate):
    x = tuple(map(rat, certificate['point']))
    require(len(x) == len(objective) and all(dot(a, x) <= t for a, t in zip(A, b)),
            'invalid primal point')
    bound = verify_dual(A, b, objective, certificate['dual'])
    require(dot(objective, x) == bound == rat(certificate['value']), 'primal/dual gap')
    return x, bound


class Unbounded(ValueError):
    def __init__(self, point, direction):
        super().__init__('LP is unbounded in its objective; exact ray available')
        self.point = point; self.direction = direction


class ExactLP:
    """Free-variable H-LP shifted to a known feasible point; reusable tableau."""
    def __init__(self, A, b, seed, pivot_cap=20000):
        self.A, self.b = parse(A, b); self.m = len(self.A); self.d = len(self.A[0])
        self.seed = tuple(map(rat, seed)); self.cap = pivot_cap
        require(type(pivot_cap) is int and pivot_cap > 0, 'invalid pivot cap')
        require(len(self.seed) == self.d and all(dot(a, self.seed) <= t
                    for a, t in zip(self.A, self.b)), 'LP seed is not feasible')
        self.width = 2*self.d+self.m
        self.table = [list(a)+[-x for x in a]+[Q(i == j) for j in range(self.m)]
                      +[t-dot(a, self.seed)] for i, (a, t) in enumerate(zip(self.A, self.b))]
        self.basis = [2*self.d+i for i in range(self.m)]
        self.pivots = 0; self.calls = 0

    def point(self):
        variables = [Q(0)]*self.width
        for i, v in enumerate(self.basis): variables[v] = self.table[i][-1]
        return tuple(self.seed[j]+variables[j]-variables[self.d+j] for j in range(self.d))

    def maximize(self, objective):
        c = tuple(map(rat, objective)); require(len(c) == self.d, 'objective shape')
        self.calls += 1
        original = list(c)+[-x for x in c]+[Q(0)]*self.m
        reduced = original[:]
        for i, v in enumerate(self.basis):
            t = original[v]
            if t:
                reduced = [a-t*b for a, b in zip(reduced, self.table[i][:-1])]
        start_pivots = self.pivots
        while True:
            entering = next((j for j, v in enumerate(reduced) if v > 0), None)
            if entering is None: break
            candidates = [(row[-1]/row[entering], self.basis[i], i)
                          for i, row in enumerate(self.table) if row[entering] > 0]
            if not candidates:
                values = [Q(0)]*self.width; values[entering] = 1
                for i, v in enumerate(self.basis): values[v] = -self.table[i][entering]
                ray = tuple(values[j]-values[self.d+j] for j in range(self.d))
                require(all(dot(a, ray) <= 0 for a in self.A) and dot(c, ray) > 0,
                        'invalid unbounded ray')
                raise Unbounded(self.point(), ray)
            require(self.pivots-start_pivots < self.cap, 'exact LP pivot cap; no optimum claimed')
            _, _, leaving = min(candidates)
            t = self.table[leaving][entering]
            pivot = [v/t for v in self.table[leaving]]
            self.table[leaving] = pivot
            for i, row in enumerate(self.table):
                if i != leaving and row[entering]:
                    t = row[entering]
                    self.table[i] = [v-t*w for v, w in zip(row, pivot)]
            t = reduced[entering]
            reduced = [v-t*w for v, w in zip(reduced, pivot[:-1])]
            self.basis[leaving] = entering; self.pivots += 1
        dual = tuple(-reduced[2*self.d+i] for i in range(self.m))
        require(all(v >= 0 for v in dual), 'negative final dual coefficient')
        x = self.point()
        certificate = serial({'point': x, 'dual': sparse_dual(dual), 'value': dot(c, x)})
        verify_optimum(self.A, self.b, c, certificate)
        return certificate


def feasible_point(A, b, seed=None, pivot_cap=20000):
    A, b = parse(A, b); d = len(A[0])
    if seed is not None:
        x = tuple(map(rat, seed))
        require(len(x) == d and all(dot(a, x) <= t for a, t in zip(A, b)), 'infeasible supplied point')
        return x
    if all(t >= 0 for t in b): return (Q(0),)*d
    # Phase I: Ax-t<=b, t>=0. This auxiliary seed is explicitly feasible.
    auxiliary = [a+(-Q(1),) for a in A]+[(Q(0),)*d+(-Q(1),)]
    rhs = b+(Q(0),); level = max(Q(0), -min(b))
    solver = ExactLP(auxiliary, rhs, (Q(0),)*d+(level,), pivot_cap)
    out = solver.maximize((Q(0),)*d+(-Q(1),))
    point, value = verify_optimum(tuple(auxiliary), rhs, (Q(0),)*d+(-Q(1),), out)
    require(value == 0, 'H-system infeasible (exact positive phase-I optimum)')
    return point[:-1]
