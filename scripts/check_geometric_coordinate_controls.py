#!/usr/bin/env python3
"""Forgery controls and exact retained-fixture replay; not Lean verification."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import test_geometric_coordinate_routes as t

ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True); args=ap.parse_args()
model=t.reference([(0,0),(1,0),(0,1),(1,1)])
u=model['vertices'].index((Q(0),Q(0)))
v,good=t.improving_edge(model,frozenset(range(4)),u,(Q(1),Q(0)))
assert t.verify_record(model,good)
cases=[]
for name,edit in [
    ('zero_support',lambda r:r.update(support=(Q(0),Q(0)))),
    ('wrong_sign_support',lambda r:r.update(support=tuple(-x for x in r['support']))),
    ('not_improving',lambda r:r.update(objective=(Q(0),Q(0)))),
    ('stationary_edge',lambda r:r.update(v=r['u'])),
    ('diagonal_instead_of_edge',lambda r:r.update(v=model['vertices'].index((Q(1),Q(1))))),
    ('nonface_vertex_subset',lambda r:r.update(face=[u,model['vertices'].index((Q(1),Q(1)))])),
    ('missing_endpoint',lambda r:r.update(face=[u])),
    ('truncated_support',lambda r:r.update(support=(Q(0),))),
]:
    r=deepcopy(good); edit(r)
    try: t.verify_record(model,r)
    except (ValueError,AssertionError): cases.append(dict(name=name,rejected=True))
    else: raise AssertionError('accepted forgery: '+name)
for name,operation in [
    ('empty_hull',lambda:t.reference([])),
    ('mixed_dimensions',lambda:t.reference([(0,),(0,1)])),
    ('constant_objective',lambda:t.improving_edge(model,frozenset(range(4)),u,(Q(0),Q(0))))
]:
    try: operation()
    except ValueError: cases.append(dict(name=name,rejected=True))
    else: raise AssertionError('accepted invalid input: '+name)
args.out.write_text(json.dumps(dict(kind='offline_negative_controls_not_hypothesis_necessity_proofs',
                                   controls=cases),indent=2)+'\n')
print('rejected',len(cases),'controls')
