#!/usr/bin/env python3
"""Exact planar-incidence and original-route tests, not Lean/Python verification.

Finite hull references enumerate supporting rows independently. The inherited
route constructor never reads the reference edge table. A separate consumer
recomputes the nullspace identities, active incidence sets and whole edge slices.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sympy as sp
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old
import test_few_exception_target_routes as few


def require(ok, message):
    if not ok:
        raise ValueError(message)


def incidence(model, rows, v, B):
    few.check_B(model, rows, v, B)
    require(len(B) <= 2, 'more than two exceptions')
    V = model['vertices']; d = len(V[0]); m = len(rows)
    G = old.active(rows, V[v]) - set(B)
    A = sp.Matrix([rows[i][:-1] for i in sorted(G)]) if G else sp.zeros(0, d)
    basis = [tuple(Q(x) for x in z) for z in A.nullspace()]
    r = len(basis)
    D = [x for x in range(len(V)) if G <= old.active(rows, V[x])]
    I = [i for i in range(m) if any(g.dot(rows[i][:-1], z) != 0 for z in basis)]
    by_vertex = [[x, sorted(old.active(rows, V[x]) & set(I))] for x in D]
    by_row = [[i, [x for x in D if i in old.active(rows, V[x])]] for i in I]
    result = dict(target=v, exceptions=sorted(B), good=sorted(G), vertices=D,
                  basis=basis, dimension=r, nonzero_rows=I,
                  vertex_incidences=by_vertex, row_incidences=by_row,
                  incidence_count=sum(len(z) for _, z in by_row),
                  vertex_bound=m+1, route_bound=(m-d)+m)
    audit_incidence(model, rows, result)
    return result


def audit_incidence(model, rows, c):
    """Read-only certificate consumer: does not run the incidence producer."""
    V=model['vertices']; d=len(V[0]); m=len(rows); v=c['target']; B=c['exceptions']
    few.check_B(model, rows, v, B)
    require(len(B) <= 2, 'more than two exceptions')
    G = old.active(rows, V[v]) - set(B)
    D = [x for x in range(len(V)) if G <= old.active(rows, V[x])]
    require(c['good']==sorted(G) and c['vertices']==D, 'incorrect full residual vertex set')
    basis = [tuple(map(Q,z)) for z in c['basis']]
    require(all(len(z)==d for z in basis), 'wrong basis ambient dimension')
    r=len(basis)
    require(c['dimension']==r and r<=len(B), 'incorrect residual dimension')
    require(g.rank(basis)==r, 'dependent motion basis')
    require(g.rank([rows[i][:-1] for i in G])+r==d, 'motion basis incomplete')
    require(all(g.dot(rows[i][:-1],z)==0 for i in G for z in basis), 'not in row kernel')
    I=[i for i in range(m) if any(g.dot(rows[i][:-1],z)!=0 for z in basis)]
    require(c['nonzero_rows']==I, 'incorrect nonzero row restrictions')
    actual_v=[[x,sorted(old.active(rows,V[x]) & set(I))] for x in D]
    actual_r=[[i,[x for x in D if i in old.active(rows,V[x])]] for i in I]
    require(c['vertex_incidences']==actual_v, 'false vertex incidence')
    require(c['row_incidences']==actual_r, 'false row incidence')
    for x, J in actual_v:
        require(len(J)>=r, 'too few incident nonzero original rows')
        restrictions=[[g.dot(rows[i][:-1],z) for z in basis] for i in J]
        require(g.rank(restrictions)==r, 'active restrictions do not separate motions')
    for i, X in actual_r:
        require(len(X)<=2, 'nonzero row has more than two residual extreme points')
        if len(X)>1:
            require(g.rank([g.sub(V[x],V[X[0]]) for x in X])<=1, 'row slice not a line')
    count_v=sum(len(J) for _,J in actual_v); count_r=sum(len(X) for _,X in actual_r)
    require(count_v==count_r==c['incidence_count'], 'incidence double count mismatch')
    if r==2:
        require(2*len(D)<=count_v<=2*len(I)<=2*m, 'planar count failed')
        require(len(D)<=m, 'planar residual vertex bound failed')
    else:
        require(len(D)<=2, 'line residual has too many extreme points')
    if m==0:
        require(len(D)<=1, 'zero-row boundary failed')
    require(c['vertex_bound']==m+1 and c['route_bound']==m-d+m, 'wrong original-input bound')
    require(len(D)<=m+1, 'unified residual bound failed')
    return True


def audit_route(model, rows, c, cert):
    V=model['vertices']; d=len(V[0]); m=len(rows)
    u=cert['u']; v=cert['v']; p=cert['path']; records=cert['records']
    require(v==c['target'] and 0<=u<len(V), 'invalid route endpoints')
    require(cert['displayed_rows']==m and cert['ambient_dimension']==d, 'false input size')
    require(p and p[0]==u and p[-1]==v and all(0<=i<len(V) for i in p), 'false route sequence')
    require(len(records)==len(p)-1, 'incorrect record count')
    T=old.active(rows,V[v]); G=set(c['good']); D=set(c['vertices'])
    score=tuple(sum((rows[i][j] for i in T),Q(0)) for j in range(d))
    prefix=0; terminal=[]; entered=False
    for (x,y),rec in zip(zip(p,p[1:]),records):
        before=old.active(rows,V[x]) & T; after=old.active(rows,V[y]) & T
        require(before<=after, 'target row lost')
        require(rec['before']==sorted(before) and rec['after']==sorted(after), 'false tight set')
        absent=G-before; chosen=rec['chosen_good']
        if absent:
            require(not entered and chosen in absent and chosen in after, 'good acquisition failed')
            f=rows[chosen][:-1]; prefix+=1
        else:
            entered=True
            require(chosen is None and x in D and y in D, 'escaped residual face')
            f=score; terminal.append(x)
        edge=rec['edge']
        require(edge['u']==x and edge['v']==y, 'false edge endpoints')
        require(tuple(map(Q,edge['objective']))==f, 'false objective')
        F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
        require(set(edge['face'])==F, 'incomplete target-lock face')
        g.verify_record(model,edge)
    terminal.append(v)
    require(len(terminal)==len(set(terminal)), 'repeated monotone residual vertex')
    require(prefix==cert['prefix_length'] and prefix<=len(G-old.active(rows,V[u]))<=m-d,
            'original prefix bound failed')
    suffix=len(p)-1-prefix
    require(suffix<=len(D)-1<=m, 'linear residual bound failed')
    require(len(p)-1<=m-d+m, 'linear original bound failed')
    return True


def cases():
    values=old.cases()
    values += [('two_exception_hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],False),
               ('two_roofs',few.roof_points(2,2),False),
               ('three_roofs_exclusion',few.roof_points(1,3),False)]
    for n in (5,8,12):
        poly=[(Q(i),Q(i*i)) for i in range(n)]
        values.append((f'parabolic_polygon_{n}',poly,False))
    poly=[(Q(i),Q(i*i)) for i in range(6)]
    values.append(('polygon_prism',[(x,y,Q(t)) for x,y in poly for t in (0,1)],False))
    return values


def negative_controls(model,rows,c,cert):
    results=[]
    mutations=[
        ('false_dimension', lambda x:x.update(dimension=x['dimension']+1)),
        ('incomplete_vertex_set',lambda x:x.update(vertices=x['vertices'][:-1])),
        ('missing_nonzero_row',lambda x:x.update(nonzero_rows=x['nonzero_rows'][:-1])),
        ('wrong_incidence_total',lambda x:x.update(incidence_count=x['incidence_count']+1)),
        ('understated_vertex_bound',lambda x:x.update(vertex_bound=1)),
        ('zero_motion_basis',lambda x:x.update(basis=[[Q(0)]*len(z) for z in x['basis']])),
        ('oversized_exception_set',lambda x:x.update(exceptions=list(range(3)))),
    ]
    for name,edit in mutations:
        x=deepcopy(c);edit(x)
        try:audit_incidence(model,rows,x)
        except (ValueError,AssertionError): results.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted malformed incidence: '+name)
    for name,edit in [
        ('stationary_edge',lambda x:x['records'][0]['edge'].update(v=x['path'][0])),
        ('wrong_prefix_count',lambda x:x.update(prefix_length=x['prefix_length']+1)),
        ('zero_edge_objective',lambda x:x['records'][0]['edge'].update(objective=(Q(0),Q(0)))),
    ]:
        x=deepcopy(cert);edit(x)
        try:audit_route(model,rows,c,x)
        except (ValueError,AssertionError):results.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted malformed route: '+name)
    return results


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--only',default='all');args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    reports=[];fixtures=[];controls=[]
    for name,points,extra in cases():
        if args.only!='all' and args.only!=name:continue
        model=g.reference(points);rows=old.h_rows(model);V=model['vertices'];d=len(V[0])
        if extra:rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])]
        old.validate_h(model,rows)
        records=[];routes=[];reject=0;edgecount=distcount=nonshortest=nonacq=0
        dims={0:0,1:0,2:0};inc_count=0;planarvertices=0
        for v in range(len(V)):
            B=few.bad_rows(model,rows,v)
            if len(B)>2:reject+=1;continue
            choices=[B]
            expanded=set(B)
            for i in range(len(rows)):
                if len(expanded)>=2:break
                expanded.add(i)
            if expanded!=B:choices.append(expanded)
            for B1 in choices:
                c=incidence(model,rows,v,B1);records.append(c);dims[c['dimension']]+=1
                inc_count+=c['incidence_count'];planarvertices+=len(c['vertices']) if c['dimension']==2 else 0
                for u in range(len(V)):
                    cert=few.produce(model,rows,u,v,c);audit_route(model,rows,c,cert)
                    routes.append(dict(incidence_index=len(records)-1,route=cert))
                    L=len(cert['path'])-1;dist=old.distances(model,u)[v]
                    edgecount+=L;distcount+=dist;nonshortest+=L>dist
                    nonacq+=sum(r['before']==r['after'] for r in cert['records'])
                if name=='two_exception_hexagon' and len(B1)==2 and not controls:
                    source=next(x['route'] for x in routes if x['incidence_index']==len(records)-1 and len(x['route']['path'])>1)
                    controls=negative_controls(model,rows,c,source)
        # Replay serialized-to-JSON-decoded certificates with both producers disabled.
        frozen=json.loads(json.dumps(g.encoded(dict(incidences=records,routes=routes))))
        saved_i=globals()['incidence'];saved_e=g.improving_edge;saved_p=few.produce
        def disabled(*a,**k):raise RuntimeError('constructor disabled')
        globals()['incidence']=g.improving_edge=few.produce=disabled
        try:
            for c in frozen['incidences']:audit_incidence(model,rows,c)
            for z in frozen['routes']:audit_route(model,rows,frozen['incidences'][z['incidence_index']],z['route'])
        finally:globals()['incidence']=saved_i;g.improving_edge=saved_e;few.produce=saved_p
        item=dict(name=name,ambient_dimension=d,vertices=len(V),rows=len(rows),
                  qualifying_targets=len(V)-reject,rejected_targets=reject,incidence_certificates=len(records),
                  residual_dimensions=dims,planar_vertex_occurrences=planarvertices,
                  incidences=inc_count,routes=len(routes),edges=edgecount,shortest_edges=distcount,
                  nonshortest_routes=nonshortest,nonacquiring_steps=nonacq)
        reports.append(item);fixtures.append(dict(name=name,points=model['points'],rows=rows,**frozen))
        print(json.dumps(item),flush=True)
    (args.out/'report.json').write_text(json.dumps(dict(kind='exact_supporting_tests_not_Lean',models=reports),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    (args.out/'negative-controls.json').write_text(json.dumps(dict(controls=controls),indent=2)+'\n')

if __name__=='__main__':main()
