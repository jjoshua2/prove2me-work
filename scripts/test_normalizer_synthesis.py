#!/usr/bin/env python3
"""Exact source-data, spectrum-optimum and original-route regression.

The new normalizers are synthesized from points and row slacks, not supplied.
Uses the unchanged #333 original-edge constructor/consumer for applications.
The formal packet proves finite search completeness, not Python correctness.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import normalizer_synthesis as ns
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old
import test_normalized_slack_routes as route


def models():
    result=list(g.models())
    result += [('pentagon',[(0,0),(3,0),(4,2),(2,4),(-1,2)]),
               ('hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]),
               ('octahedron',[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)])]
    for d in (2,3):
        points=[]
        for bits in product((0,1),repeat=d):
            q=1+sum(2**j*bits[j] for j in range(d))
            points.append(tuple(Q(b,q) for b in bits))
        result.append(('projective_cube'+str(d),points))
    # Same projective cube under nontrivial affine change and reanchoring.
    pts=[]
    for bits in product((0,1),repeat=3):
        q=1+sum(3**j*bits[j] for j in range(3));x=[Q(b,q) for b in bits]
        pts.append((2*x[0]+x[1]+5,-x[0]+3*x[2]-7,x[1]-2*x[2]+1))
    result.append(('affine_projective_cube',pts))
    return result


def run_model(name,points):
    model=g.reference(points);rows=old.h_rows(model);old.validate_h(model,rows)
    C=model['vertices'];anchor=len(C)//2;u=C[anchor];d=len(u)
    normalizers=[];dens=[];stats=[]
    for row in rows:
        s=[row[-1]-g.dot(row[:-1],x) for x in C]
        out=ns.optimize(C,s,anchor);stats.append(ns.audit(C,s,out));normalizers.append(out)
        D=out['records'][out['best']]['slope'];dens.append(tuple(D+[1-g.dot(D,u)]))
    certs=[];edges=shortest=nonshort=0
    for a in range(len(C)):
        distances=old.distances(model,a)
        for b in range(len(C)):
            c=route.produce(model,rows,dens,a,b);route.consume(model,rows,dens,c);certs.append(c)
            L=len(c['path'])-1;edges+=L;shortest+=distances[b];nonshort+=L>distances[b]
    fixture=json.loads(json.dumps(ns.encoded(dict(name=name,points=model['points'],rows=rows,dens=dens,
                                          normalizers=normalizers,routes=certs))))
    saved=(ns.optimize,ns.solve_system,ns.eliminate_equalities,ns.strict_feasible,route.produce,g.improving_edge)
    def disabled(*a,**k):raise RuntimeError('producer disabled during saved replay')
    ns.optimize=ns.solve_system=ns.eliminate_equalities=ns.strict_feasible=route.produce=g.improving_edge=disabled
    try:
        for row,out in zip(rows,fixture['normalizers']):
            ns.audit(C,[row[-1]-g.dot(row[:-1],x) for x in C],out)
        for c in fixture['routes']:route.consume(model,rows,dens,c)
    finally:
        ns.optimize,ns.solve_system,ns.eliminate_equalities,ns.strict_feasible,route.produce,g.improving_edge=saved
    report=dict(name=name,dimension=d,vertices=len(C),original_rows=len(rows),routes=len(certs),edges=edges,
                shortest_edges=shortest,nonshortest_routes=nonshort,
                systems=sum(t['systems'] for t in stats),positive_systems=sum(t['positive_systems'] for t in stats),
                excluded_systems=sum(t['excluded_systems'] for t in stats),
                exhaustive_rows=sum(t['mode']=='exhaustive' for t in stats),
                strictly_reduced_rows=sum(t['minimum_values']<t['raw_values'] for t in stats),
                optimal_weights=[t['minimum_values']-1 for t in stats],
                raw_weights=[t['raw_values']-1 for t in stats])
    return report,fixture


def generic_and_controls():
    cases=[('zero_dimension',[()], [Q(-3)]),
           ('collinear',[(-1,),(0,),(2,),(5,)], [1,2,3,7]),
           ('signed_data',[(0,0),(1,0),(0,1),(1,1),(2,3)], [-2,0,3,4,9]),
           ('no_binary_positive_row',[(0,0),(1,0),(2,1),(1,3),(-1,2)], [0,0,2,9,2]),
           ('tiny_rational_data',[(0,0),(1,0),(0,1),(1,1)], [1,1+Q(1,2**80),2,2+Q(1,2**80)])]
    reports=[];fixtures=[]
    for name,C,s in cases:
        out=ns.optimize(C,s);r=ns.audit(C,s,out)
        reports.append(dict(name=name,**r));fixtures.append(dict(name=name,points=C,values=s,certificate=out))
    C,s=cases[3][1:];good=ns.optimize(C,s)
    infeas=next(i for i,c in enumerate(good['records']) if c['kind']=='infeasible_positive')
    valid=good['best']
    changes=[('false optimum',lambda x:x.update(minimum=1)),
             ('missing exhaustive basis',lambda x:x['records'].pop()),
             ('zero denominator',lambda x:x['records'][valid].update(slope=[-1,0])),
             ('invented pair',lambda x:x['pairs'].append((0,1))),
             ('changed anchored input',lambda x:x.update(anchor=99)),
             ('false early stop',lambda x:x.update(mode='sign_lower_bound')),
             ('negative infeasibility multiplier',lambda x:x['records'][infeas]['dual'].__setitem__(0,Q(-1))),
             ('vanishing infeasibility certificate',lambda x:x['records'][infeas].update(dual=[Q(0)]*len(C))),
             ('incomplete kernel',lambda x:x['records'][infeas]['kernel'].append([Q(0),Q(0)])),
             ('false feasible spectrum',lambda x:x['records'][valid].update(values=[Q(0)]))]
    controls=[]
    for name,edit in changes:
        c=deepcopy(good);edit(c)
        try:ns.audit(C,s,c)
        except (ValueError,AssertionError,IndexError):controls.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    return reports,fixtures,controls


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--only',default='all')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    reports=[];fixtures=[];extras=[];extra_fixtures=[];controls=[]
    if a.only in ('all','generic'):
        extras,extra_fixtures,controls=generic_and_controls()
        print(json.dumps(ns.encoded({'generic':extras,'controls':controls})),flush=True)
    for name,points in models():
        if a.only not in ('all',name):continue
        report,fixture=run_model(name,points);reports.append(report);fixtures.append(fixture)
        print(json.dumps(report),flush=True)
    (a.out/'report.json').write_text(json.dumps(ns.encoded(dict(kind='exact_arithmetic_not_Lean_or_verified_parser',
                models=reports,generic=extras,controls=controls)),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(ns.encoded(dict(models=fixtures,generic=extra_fixtures)),indent=2)+'\n')

if __name__=='__main__':main()
