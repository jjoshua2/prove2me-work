#!/usr/bin/env python3
"""Exact original-H references, affine-level tests, and producer-disabled replay."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
from hashlib import sha256
from copy import deepcopy
import argparse, json, random
import sympy as sp
import affine_level_barrier as alg


def dump(p, x):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(alg.serial(x), sort_keys=True, indent=2)+'\n')


def input_data(d, epsilon=Q(1, 4), first=None, last=None, chart=None):
    data = {'dimension': d, 'epsilon': epsilon}
    if chart is not None:
        T = sp.Matrix(chart); inv = T.inv()
        data.update(chart=chart, inverse_chart=[[Q(z) for z in row] for row in inv.tolist()],
                    offset=[Q(i+1, 7) for i in range(d)], row_scales=[Q(2*i+1, i+1) for i in range(2*d)])
    mod = alg.model(data); _, e, T, S, o, scales, A, b = mod
    first = [0]*d if first is None else first
    last = [1]*d if last is None else last
    data.update(start=alg.add(alg.mv(T, alg.vertex(first, e)), o),
                target=alg.add(alg.mv(T, alg.vertex(last, e)), o), A=A, b=b)
    return alg.serial(data)


def reference(d, eps):
    A, b = alg.canonical(d, eps); A = sp.Matrix(A); b = sp.Matrix(b)
    V = {}; tested = 0
    for J in combinations(range(2*d), d):
        tested += 1; B = A[list(J), :]
        if not B.det(): continue
        x = tuple(Q(z) for z in B.inv()*b[list(J), :])
        if all((A*sp.Matrix(x))[i] <= b[i] for i in range(2*d)):
            V[x] = {i for i in range(2*d) if (A*sp.Matrix(x))[i] == b[i]}
    expected = {alg.vertex(bits, eps): bits for bits in product((0, 1), repeat=d)}
    assert set(V) == set(expected)
    edges = set()
    for x, y in combinations(V, 2):
        I = sorted(V[x] & V[y]); rank = A[I, :].rank() if I else 0
        hamming = sum(a != b for a, b in zip(expected[x], expected[y]))
        assert (rank == d-1) == (hamming == 1)
        if rank == d-1: edges.add(frozenset((x, y)))
    return V, expected, edges, tested


def small(folder):
    rng = random.Random(20260916); records = []; totals = dict(active_bases=0, vertices=0,
             original_edges=0, route_pairs=0, route_edges=0, reference_distances=0, old_auditor_replays=0)
    for d, eps in [(1,Q(1,4)), (2,Q(1,4)), (3,Q(1,4)), (4,Q(1,4)),
                   (2,Q(1,3)), (3,Q(1,3)), (4,Q(1,256))]:
        V, bits, edges, n = reference(d, eps)
        pairs = list(product(list(V), repeat=2)); rng.shuffle(pairs)
        pairs = pairs[:80]
        for u, v in pairs:
            data = input_data(d, eps, bits[u], bits[v]); out = alg.construct(data)
            points = [tuple(map(Q, p['point'])) for p in out['certificate']['path']['vertices']]
            assert all(frozenset((x,y)) in edges for x,y in zip(points,points[1:]))
            dist = sum(a != b for a,b in zip(bits[u],bits[v]))
            assert len(points)-1 == dist
            A,b = alg.canonical(d,eps)
            old = alg.audit.verify_path(alg.serial({'A':A,'b':b,'start':u,'target':v}), out['certificate']['path'])
            assert old['original_edges'] == dist and old['original_row_reentries'] == 0
            totals['route_pairs'] += 1; totals['route_edges'] += dist
            totals['reference_distances'] += 1; totals['old_auditor_replays'] += 1
        totals['active_bases'] += n; totals['vertices'] += len(V); totals['original_edges'] += len(edges)
        record = dict(dimension=d, epsilon=str(eps), complete_active_bases=n, vertices=len(V),
                      independent_original_edges=len(edges), route_pairs=len(pairs))
        records.append(record)
        data=input_data(d,eps);dump(folder/f'family_{d}_{eps.denominator}.json', {'input':data,'result':alg.construct(data)})
    return {'status':'PASS','totals':totals,'models':records}


def parallel(folder):
    records=[]
    for d,eps in [(d,Q(1,4)) for d in range(1,13)]+[(8,Q(1,3)),(8,Q(1,2**160))]:
        if d==1: prefixes=[()]
        else: prefixes=list(product((0,1),repeat=d-1))
        lengths=[];coordinates=[]
        for bits in prefixes:
            a,b=alg.vertex((*bits,0),eps),alg.vertex((*bits,1),eps)
            assert a[:-1]==b[:-1] and b[-1]>a[-1]
            lengths.append(b[-1]-a[-1])
            if d>1: coordinates.append(a[-2])
        assert len(set(lengths))==1<<(d-1)
        if d>1:assert len(set(coordinates))==1<<(d-1)
        assert min(lengths)>=1-2*eps and max(lengths)<=1
        records.append({'dimension':d,'epsilon':str(eps),'explicit_parallel_edges':len(lengths),
                        'distinct_lengths':len(set(lengths)),'lower_bound':alg.level_lower_bound(d)})
    return {'status':'PASS','explicit_edge_count':sum(r['explicit_parallel_edges'] for r in records),
            'records':records,'scope':'Finite sanity checks. The all-dimensional/all-real-epsilon count is proved by disjoint recursive intervals.'}


def charts(folder):
    rng=random.Random(814);records=[];tests=0
    for d in range(2,9):
        e=Q(1,4);V=[alg.vertex(bits,e) for bits in product((0,1),repeat=d)]
        charts=[('identity',alg.eye(d))]
        # Deliberately make the last functional constant on HALF of all vertices.
        T=[list(row) for row in alg.eye(d)];T[-1][-2]=-e;charts.append(('half_collapse',T))
        # Dense nonsingular integer matrix: I+u*u^T, plus diagonal scaling.
        u=list(range(1,d+1));T=[[Q(i==j)+Q(u[i]*u[j]) for j in range(d)] for i in range(d)]
        charts.append(('dense',T))
        T=[[Q(0) if i!=j else Q(1,2**(20*i)) for j in range(d)] for i in range(d)]
        charts.append(('ill_scaled',T))
        for name,T in charts:
            data=input_data(d,e,chart=T);out=alg.construct(data);mod=alg.model(data)
            mapped=[alg.add(alg.mv(mod[2],x),mod[4]) for x in V]
            counts=[len({x[i] for x in mapped}) for i in range(d)]
            detecting=[i for i in range(d) if mod[2][i][-1]]
            assert detecting and all(counts[i]*(counts[i]-1)>=1<<d for i in detecting)
            if name=='half_collapse':assert counts[-1]==(1<<(d-1))+1
            # Use the OLD independent original-H path auditor as well.
            old=alg.audit.verify_path({'A':data['A'],'b':data['b'],'start':data['start'],'target':data['target']},out['certificate']['path'])
            assert old['original_edges']==d
            records.append({'dimension':d,'chart':name,'coordinate_level_counts':counts,
                            'detecting_coordinates':detecting,'universal_bound':alg.level_lower_bound(d)})
            tests+=1
            if d in (3,8) and name in ('dense','half_collapse'):
                dump(folder/f'chart_{name}_{d}.json',{'input':data,'result':out})
    # A rectangular embedding adds affine coordinates; it cannot evade detection.
    d=5;e=Q(1,4);V=[alg.vertex(bits,e) for bits in product((0,1),repeat=d)]
    T=[*alg.eye(d),tuple(Q(i+1) for i in range(d)),(Q(0),)*d]
    counts=[len({alg.dot(row,x) for x in V}) for row in T]
    assert all(counts[i]*(counts[i]-1)>=1<<d for i,row in enumerate(T) if row[-1])
    return {'status':'PASS','square_charts':tests,'records':records,
            'injective_embedding':{'dimension':d,'output_dimension':len(T),'coordinate_levels':counts}}


def large(folder, d):
    data=input_data(d);out=alg.construct(data)
    dump(folder/f'large_{d}.json',{'input':data,'result':out})
    # Counts here are formulas checked with integer arithmetic, not enumeration.
    formulas=[]
    for n in (16,32,64,128,256):
        formulas.append({'dimension':n,'facets':2*n,'parallel_edge_count':1<<(n-1),
                         'universal_minimum_some_coordinate_levels':alg.level_lower_bound(n),
                         'diameter':n,'vertices_enumerated':False})
    return {'status':'PASS','executed':out['verified'],'family_formulas':formulas}


def negative(folder):
    data=input_data(4,chart=[[2,1,1,1],[1,2,1,1],[1,1,2,1],[1,1,1,2]])
    out=alg.construct(data);bad=[]
    def reject(name,call):
        try:call()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):bad.append(name);return
        raise AssertionError('forged record accepted: '+name)
    def mutate(name, edit):
        c=deepcopy(out['certificate']);edit(c);reject(name,lambda:alg.verify(data,c))
    mutate('family binding',lambda c:c.update(input_sha256='wrong'))
    mutate('parallel count',lambda c:c.update(parallel_edge_count=2))
    mutate('claimed level bound',lambda c:c.update(universal_coordinate_level_lower_bound=9999))
    mutate('detecting row range',lambda c:c.update(nonzero_last_column_row=4))
    mutate('change endpoint bits',lambda c:c['last_bits'].__setitem__(0,0))
    mutate('missing flip',lambda c:c['flip_order'].pop())
    mutate('repeated flip',lambda c:c['flip_order'].__setitem__(0,1))
    mutate('missing vertex',lambda c:c['path']['vertices'].pop())
    mutate('false vertex inverse',lambda c:c['path']['vertices'][0]['inverse'][0].__setitem__(0,'999'))
    mutate('false shared-row inverse',lambda c:c['path']['edges'][0]['right_inverse'][0].__setitem__(0,'999'))
    mutate('missing facet anchor',lambda c:c['facet_anchors'].pop())
    mutate('false facet anchor',lambda c:c['facet_anchors'][0].__setitem__(0,'999'))
    mutate('false route count',lambda c:c['path'].update(length=3))
    mutate('false prefix level',lambda c:c['target_prefix_levels'][0].__setitem__(1,'9'))
    mutate('missing prefix face',lambda c:c['target_prefix_levels'].pop())
    for eps in (0,Q(1,2),-1):
        reject('invalid epsilon '+str(eps),lambda eps=eps:alg.construct({**data,'epsilon':str(eps)}))
    reject('inexact epsilon',lambda:alg.construct({**data,'epsilon':0.25}))
    reject('singular chart',lambda:alg.construct({**data,'chart':[[0]*4]*4}))
    reject('false inverse chart',lambda:alg.construct({**data,'inverse_chart':alg.eye(4)}))
    reject('unbound original rows',lambda:alg.construct({**data,'b':[0]*8}))
    reject('negative row scale',lambda:alg.construct({**data,'row_scales':[-1]*8}))
    # The nonzero-direction condition is essential: x_1 sees only two levels.
    c=alg.construct(input_data(5))['certificate'];c['nonzero_last_column_row']=0
    reject('functional annihilates parallel edges',lambda:alg.verify(input_data(5),c))
    return {'status':'PASS','negative_controls':bad,'count':len(bad)}


def replay(folder):
    old={n:getattr(alg,n) for n in ('construct','vertex','original_packet','family_anchors')}
    disabled={n:getattr(alg.audit,n) for n in ('inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses','solve')}
    def kill(*args,**kwargs):raise AssertionError('producer was invoked during saved verification')
    count=edges=0
    try:
        for n in old:setattr(alg,n,kill)
        for n in disabled:setattr(alg.audit,n,kill)
        for p in sorted(folder.glob('*.json')):
            data=json.loads(p.read_text())
            assert alg.verify(data['input'],data['result']['certificate'])==data['result']['verified']
            count+=1;edges+=data['result']['verified']['original_edges']
    finally:
        for n,v in old.items():setattr(alg,n,v)
        for n,v in disabled.items():setattr(alg.audit,n,v)
    return {'status':'PASS','saved_records':count,'original_edges_checked':edges,
            'vertex_path_inverse_and_anchor_producers_disabled':True}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','parallel','charts','large16','large32','large64','negative','audit'],required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args();a.fixtures.mkdir(parents=True,exist_ok=True)
    if a.stage.startswith('large'):r=large(a.fixtures,int(a.stage[5:]))
    else:r={'small':small,'parallel':parallel,'charts':charts,'negative':negative,'audit':replay}[a.stage](a.fixtures)
    r['source_sha256']={n:sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in
        ('affine_level_barrier.py','test_affine_level_barrier.py','original_route_exclusion.py')}
    dump(a.out,r);print(a.stage,r.get('totals',r.get('executed',{k:v for k,v in r.items() if k not in ('source_sha256','records','models')})),flush=True)
if __name__=='__main__':main()
