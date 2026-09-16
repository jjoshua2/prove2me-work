#!/usr/bin/env python3
"""Exact supporting tests for the separate triangular-family Lean theorem.

No finite test below is a proof of the all-real or all-dimension statement.
The published theorem's source, compilation and platform verdict are separate.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
import argparse
import hashlib
import json
import sympy as sp


def point(e, bits):
    result = []
    previous = Q(0)
    for bit in reversed(bits):
        previous = 1-e*previous if bit else e*previous
        result.append(previous)
    return tuple(reversed(result))


def inequalities(e, d):
    rows = []
    for i in range(d):
        for sign, rhs in ((-1, Q(0)), (1, Q(1))):
            rows.append((tuple(Q(sign if j == i else 0) for j in range(d)), rhs))
    for i in range(d-1):
        rows.append((tuple(Q(-1) if j == i else e if j == i+1 else Q(0)
                           for j in range(d)), Q(0)))
        rows.append((tuple(Q(1) if j == i else e if j == i+1 else Q(0)
                           for j in range(d)), Q(1)))
    return rows


def dot(a, x):
    return sum((u*v for u, v in zip(a, x)), Q(0))


def run():
    records = []
    counts = dict(families=0, constructed_points=0, displacements=0,
                  inequality_comparisons=0, original_active_rank_checks=0,
                  embedding_checks=0, detecting_coordinate_checks=0,
                  complete_basis_cases=0)
    digest = hashlib.sha256()
    for e in (Q(1, 4), Q(1, 3), Q(1, 17), Q(1, 2**40)):
        for d in range(1, 9):
            words = list(product((False, True), repeat=d))
            V = [point(e, w) for w in words]
            assert len(set(V)) == len({v[0] for v in V}) == 2**d
            assert all(0 <= a <= 1 for v in V for a in v)
            rows = inequalities(e, d)
            for w, x in zip(words, V):
                assert all(dot(a, x) <= b for a, b in rows)
                counts['inequality_comparisons'] += len(rows)
                if d <= 4:
                    active = [a for a, b in rows if dot(a, x) == b]
                    assert sp.Matrix(active).rank() == d
                    counts['original_active_rank_checks'] += 1
            lengths = []
            for tail in product((False, True), repeat=d-1):
                p, q = point(e, (False, *tail)), point(e, (True, *tail))
                s = point(e, tail)[0] if tail else Q(0)
                lam = 1-2*e*s
                assert lam > 0 and p in V and q in V
                assert tuple(b-a for a, b in zip(p, q)) == (lam,)+(Q(0),)*(d-1)
                lengths.append(lam)
            assert len(set(lengths)) == 2**(d-1)
            # Two concrete full-column-rank embeddings, with positive/negative
            # slopes, dense rows, rectangular images and a constant coordinate.
            for signed in (1, -1):
                T = [tuple(Q(signed if i == j else 0) for j in range(d)) for i in range(d)]
                T.extend([tuple(Q(j+1) for j in range(d)), (Q(0),)*d])
                assert sp.Matrix(T).rank() == d
                images = [tuple(dot(row, x)+Q(i, 7) for i, row in enumerate(T)) for x in V]
                detecting = [i for i, row in enumerate(T) if row[0]]
                assert detecting
                for i in detecting:
                    K = len({z[i] for z in images})
                    assert 2**d <= K*(K-1)
                    counts['detecting_coordinate_checks'] += 1
                counts['embedding_checks'] += 1
            counts['families'] += 1
            counts['constructed_points'] += len(V)
            counts['displacements'] += len(lengths)
            encoded = [[str(x) for x in v] for v in V]
            digest.update(json.dumps(encoded, separators=(',', ':')).encode())
            records.append(dict(epsilon=str(e), dimension=d, points=len(V),
                                distinct_parallel_displacements=len(lengths)))
    # A genuinely independent full active-basis inventory for small original H systems.
    references = []
    e = Q(1, 3)
    for d in (1, 2, 3):
        rows = inequalities(e, d); found = set(); nonsingular = 0
        for J in combinations(range(len(rows)), d):
            counts['complete_basis_cases'] += 1
            M = sp.Matrix([rows[j][0] for j in J])
            if M.det() == 0:
                continue
            nonsingular += 1
            x = tuple(Q(z) for z in M.inv()*sp.Matrix([rows[j][1] for j in J]))
            if all(dot(a, x) <= b for a, b in rows):
                found.add(x)
        expected = {point(e, w) for w in product((False, True), repeat=d)}
        assert found == expected
        references.append(dict(dimension=d, rows=len(rows),
                               nonsingular_bases=nonsingular, feasible_vertices=len(found)))
    # Boundary/assumption countermodels are expected failures of an extension,
    # not failed instances satisfying the theorem's hypotheses.
    controls = []
    for e in (Q(0), Q(1, 2)):
        levels = [point(e, w)[0] for w in product((False, True), repeat=2)]
        assert len(set(levels)) < 4
        controls.append(dict(kind='noninjective_scalar_boundary', epsilon=str(e), levels=list(map(str, levels))))
    bad = point(Q(-1, 4), (False, True))
    assert bad[0] < 0
    controls.append(dict(kind='negative_parameter_not_feasible', point=list(map(str, bad))))
    V = [point(Q(1, 4), w) for w in product((False, True), repeat=3)]
    K = len({x[-1] for x in V})
    assert K*(K-1) < 2**3
    controls.append(dict(kind='noninjective_projection_has_too_few_levels', K=K))
    return dict(status='PASS', counts=counts, families=records,
                complete_small_original_H_references=references,
                assumption_countermodels=controls, point_table_chain_sha256=digest.hexdigest(),
                scope='Exact finite tests; not Lean verification, an all-real proof by sampling, or a new graph-diameter bound.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    report = run()
    report['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
    print(json.dumps(report['counts'], sort_keys=True))

if __name__ == '__main__':
    main()
