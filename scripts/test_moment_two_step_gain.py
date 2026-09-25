#!/usr/bin/env python3
"""Supporting checks for the written two-step extension, NOT Lean verification."""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]


def run():
    spec = importlib.util.spec_from_file_location('six_row_reference', ROOT/'scripts/test_moment_six_row_small_gain.py')
    ref = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ref)
    e = sp.symbols('e', positive=True)
    nodes = [-1, 0, e, 2*e, 3*e, 1]
    A = sp.Matrix([[t-e, t*t-(1+7*e*e)/3] for t in nodes])
    f = A[0, :] + A[5, :]
    u = sp.Matrix([9*e/(1+4*e*e), -3/(1+4*e*e)])
    v = sp.Matrix([0, 3/(2-7*e*e)])
    b = sp.Matrix([-3/(1+3*e+7*e*e), -3/(1+3*e+7*e*e)])
    c = sp.Matrix([3*(1+3*e)/(1+6*e-2*e*e), -3/(1+6*e-2*e*e)])
    gap = (f*(v-u))[0]
    hb = e*(14*e**3+6*e**2+5*e+3)/((1+2*e*e)*(1+3*e+7*e*e))
    hc = e*(3-4*e-4*e**3)/((1+2*e*e)*(1+6*e-2*e*e))
    assert sp.cancel((f*(b-u))[0]/gap-hb) == 0
    assert sp.cancel((f*(c-u))[0]/gap-hc) == 0
    assert sp.cancel(gap-6*(1+2*e*e)/(1+4*e*e)) == 0
    expected = [6*(1+3*e), 9*e, 6*e*(1-e), 3*e*(1-2*e), 0, 0]
    for i in range(6):
        assert sp.cancel(1-(A*c)[i]-expected[i]/(1+6*e-2*e*e)) == 0
    es = [Q(1,n) for n in range(5,41)] + [Q(1,2**n) for n in (8,16,32,64,128)]
    checked = 0
    for epsilon in es:
        _, rows = ref.rows(epsilon)
        vertices, edges = ref.full_graph(rows)
        source, left, right, target, bottom = ref.explicit(epsilon)
        den = 1+6*epsilon-2*epsilon*epsilon
        other = (3*(1+3*epsilon)/den, -3/den)
        assert len(vertices) == len(edges) == 6 and other in vertices
        dist = {source: 0}
        queue = deque([source])
        while queue:
            x = queue.popleft()
            for edge in edges:
                if x in edge:
                    y = next(iter(edge-{x}))
                    if y not in dist:
                        dist[y] = dist[x]+1
                        queue.append(y)
        assert dist[target] == 3
        assert {x for x in dist if dist[x] <= 2} == {source,left,right,bottom,other}
        score = lambda x: ref.dot(rows[0],x)+ref.dot(rows[5],x)
        full_gap = score(target)-score(source)
        for x in (left,right,bottom,other):
            fraction = (score(x)-score(source))/full_gap
            assert 0 < fraction < 5*epsilon
            checked += 1
    return {'status':'PASS','symbolic_rational_identities':9,'complete_graphs':len(es),
            'radius_two_endpoint_checks':checked,'target_distance_in_each_reference':3,
            'bound':'Every non-source radius-two endpoint has relative gain < 5*e.',
            'scope':'Symbolic identities and exact finite checks supporting the separate written proof; not an additional Lean theorem or Prove2Me verdict.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True)
    args = ap.parse_args()
    result = run()
    result['source_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True))


if __name__ == '__main__':
    main()
