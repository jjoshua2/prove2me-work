#!/usr/bin/env python3
"""Exact finite tests; no sample test is a proof of a universal Lean theorem."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
from typing import Any

from projective_row_block_certificate import certificate, verify_projective_certificate
from row_block_certificate import certificate as row_certificate, dot, inverse, matmul, rank, jsonable


def perspective(x: list[Q], c: list[Q]) -> list[Q]:
    denominator = 1 + dot(c, x)
    if denominator <= 0:
        raise ValueError('positive chart required')
    return [t/denominator for t in x]


def unit_cube(d: int, mixed: bool = False) -> dict[str, Any]:
    eye = [[Q(i == j) for j in range(d)] for i in range(d)]
    source = [[-x for x in row] for row in eye] + eye
    rhs = [Q(0)]*d + [Q(1)]*d
    c = [Q(-1, 4*d) if mixed and i % 2 else Q(i+1, d) for i in range(d)]
    positive = [max(t, Q(0)) for t in c]
    negative = [max(-t, Q(0)) for t in c]
    denom = 1 + sum(positive)
    return {
        'A': [[x+b*y for x, y in zip(row, c)] for row, b in zip(source, rhs)],
        'b': rhs, 'chart_normal': c, 'source_feasible_point': [0]*d,
        'source_positive_balance': [1]*(2*d),
        'source_denominator_weights': positive + negative,
        'target_denominator_weights': [t/denom for t in negative + positive],
    }


def simplex_product(dims: list[int]) -> dict[str, Any]:
    d = sum(dims)
    source = [[Q(-int(i == j)) for j in range(d)] for i in range(d)]
    groups, start = [], 0
    for size in dims:
        group = list(range(start, start+size)); groups.append(group); start += size
        source.append([Q(j in group) for j in range(d)])
    rhs = [Q(0)]*d + [Q(1)]*len(dims)
    c = [Q(j+1, d+1) for j in range(d)]
    highs = [max(c[j] for j in group) for group in groups]
    lows = [Q(0)]*d
    for group, high in zip(groups, highs):
        for j in group: lows[j] = high-c[j]
    denom = 1+sum(highs)
    return {
        'A': [[x+b*y for x, y in zip(row, c)] for row,b in zip(source,rhs)],
        'b': rhs, 'chart_normal': c, 'source_feasible_point': [0]*d,
        'source_positive_balance': [1]*len(source),
        'source_denominator_weights': c+[0]*len(dims),
        'target_denominator_weights': [t/denom for t in lows+highs],
    }


def exact_vertices(a: list[list[Q]], b: list[Q]) -> set[tuple[Q, ...]]:
    d = len(a[0]); out = set()
    for rows in combinations(range(len(a)), d):
        chosen = [a[i] for i in rows]
        if rank(chosen) != d: continue
        inv = inverse(chosen)
        x = [dot(r, [b[i] for i in rows]) for r in inv]
        if all(dot(row,x) <= bound for row,bound in zip(a,b)):
            out.add(tuple(x))
    return out


def main() -> None:
    counts = dict(certificates=0, indecomposable_normal_examples=0, vertex_enumerations=0,
                  vertex_checks=0, graph_pairs=0, graph_edges=0, segment_checks=0,
                  negative_controls=0, affine_reparameterizations=0)
    samples = []
    for d in range(1, 13):
        for mixed in (False, True):
            data = unit_cube(d, mixed)
            result = certificate(data); counts['certificates'] += 1
            assert result['verified']['ordinary_edge_bound_conditional_on_transport_and_small_excess'] == d
            assert len(result['verified']['source_factors']) == d
            a, b, c = data['A'], data['b'], data['chart_normal']
            # Unmodified affine block detection sees one component, since a
            # transformed upper normal has all coordinates nonzero in the lower-row basis.
            target_balance = [1+d*t for t in c] + [Q(1)]*d
            direct = row_certificate({'A':a,'b':b,'feasible_point':[0]*d,
                                      'positive_balance':target_balance})
            assert len(direct['verified']['factors']) == 1
            counts['indecomposable_normal_examples'] += 1
            if d >= 4:
                assert direct['verified']['ordinary_edge_bound_using_existing_small_excess_theorem'] is None
            if d in (4,12) and not mixed:
                samples.append({'dimension':d,'old_linear_blocks':direct['verified']['factors'],
                                'new_bound':d,'shortest_cut_support_at_most':2,
                                'support_deficit_at_least':d-2})
            if d <= 6:
                vertices = [list(v) for v in product((Q(0),Q(1)), repeat=d)]
                images = [perspective(v,c) for v in vertices]
                assert len(set(map(tuple,images))) == len(images)
                for x,y in zip(vertices,images):
                    assert perspective(y,[-t for t in c]) == x
                    assert all(dot(row,y) <= bound for row,bound in zip(a,b))
                    active = [i for i,(row,bound) in enumerate(zip(a,b)) if dot(row,y)==bound]
                    assert rank([a[i] for i in active]) == d
                    for i in range(2*d):
                        unsheared = [a[i][j]-b[i]*c[j] for j in range(d)]
                        assert b[i]-dot(a[i],y) == (b[i]-dot(unsheared,x))/(1+dot(c,x))
                    counts['vertex_checks'] += 1
                if d <= 5:
                    assert exact_vertices(a,b) == set(map(tuple,images))
                    counts['vertex_enumerations'] += 1
                actives = [{i for i,(row,bound) in enumerate(zip(a,b)) if dot(row,y)==bound}
                           for y in images]
                graph = [set() for _ in images]
                for i,j in combinations(range(len(images)),2):
                    common = sorted(actives[i] & actives[j])
                    adjacent = rank([a[t] for t in common]) == d-1
                    hamming = sum(x != y for x,y in zip(vertices[i],vertices[j]))
                    assert adjacent == (hamming==1)
                    if adjacent:
                        graph[i].add(j); graph[j].add(i); counts['graph_edges'] += 1
                for i in range(len(images)):
                    dist={i:0}; todo=deque([i])
                    while todo:
                        p=todo.popleft()
                        for q in graph[p]:
                            if q not in dist: dist[q]=dist[p]+1; todo.append(q)
                    for j in range(len(images)):
                        assert dist[j] == sum(x!=y for x,y in zip(vertices[i],vertices[j]))
                        counts['graph_pairs'] += 1
                for t in (Q(0),Q(1,5),Q(1,2),Q(4,5),Q(1)):
                    for i in range(len(vertices)):
                        x,y=vertices[i],vertices[-i-1]
                        z=[(1-t)*p+t*q for p,q in zip(x,y)]
                        dz=1+dot(c,z); dx=1+dot(c,x); dy=1+dot(c,y)
                        alpha=(1-t)*dx/dz; beta=t*dy/dz
                        assert alpha+beta==1 and min(alpha,beta)>=0
                        assert perspective(z,c)==[alpha*p+beta*q for p,q in zip(perspective(x,c),perspective(y,c))]
                        if 0<t<1: assert min(alpha,beta)>0
                        counts['segment_checks'] += 1
            if d <= 8:
                # Nonorthogonal rational coordinate changes must not break the certificate.
                L=[[Q(int(i==j))+ (Q(1,3) if j==i+1 else 0) for j in range(d)] for i in range(d)]
                Li=inverse(L); changed=deepcopy(data)
                changed['A']=matmul(data['A'],Li)
                changed['chart_normal']=matmul([c],Li)[0]
                assert certificate(changed)['verified']['ordinary_edge_bound_conditional_on_transport_and_small_excess']==d
                counts['affine_reparameterizations'] += 1
    for dims in ([2,2], [1,2,3], [3,3,3], [1]*10, [2]*5, [5,4,3]):
        result=certificate(simplex_product(list(dims)))
        assert result['verified']['ordinary_edge_bound_conditional_on_transport_and_small_excess']==len(dims)
        assert sorted(f['dimension'] for f in result['verified']['source_factors']) == sorted(dims)
        counts['certificates'] += 1
    good=unit_cube(4); cert=certificate(good)['certificate']
    bads=[]
    bad=deepcopy(good);bad['target_denominator_weights']=[0]*8;bads.append((bad,cert))
    bad=deepcopy(good);bad['source_denominator_weights'][0]=-1;bads.append((bad,cert))
    bad=deepcopy(good);bad['A'][4][0]+=Q(1,10);bads.append((bad,cert))
    bad=deepcopy(good);bad['chart_normal'][0]=0.1;bads.append((bad,cert))
    bad=deepcopy(good);bad['keep']=list(range(8));bads.append((bad,cert))
    badcert=deepcopy(cert);badcert['row_block_certificate']['inverse_basis'][0][0]+=1;bads.append((good,badcert))
    badcert=deepcopy(cert);badcert['row_block_certificate']['row_blocks'][0].append(4);bads.append((good,badcert))
    for data, candidate in bads:
        try: verify_projective_certificate(data,candidate)
        except (ValueError,TypeError): counts['negative_controls'] += 1
        else: raise AssertionError('corrupt certificate was accepted')
    # Source [0,1], c=-2 crosses infinity; exact normal multipliers give margin -1.
    crossing={'A':[[-1],[-1]],'b':[0,1],'chart_normal':[-2],
              'source_feasible_point':[0],'source_positive_balance':[1,1],
              'source_denominator_weights':[0,2],'target_denominator_weights':[2,0]}
    try: certificate(crossing)
    except ValueError: counts['negative_controls'] += 1
    else: raise AssertionError('chart crossing infinity was accepted')
    # Genuinely coupled source: truncate a cube by sum x <= d-1/2.
    truncated=unit_cube(4);c=truncated['chart_normal']
    truncated['A'].append([1+Q(7,2)*t for t in c]);truncated['b'].append(Q(7,2))
    truncated['source_positive_balance']=[2]*4+[1]*5
    truncated['source_denominator_weights'].append(0)
    truncated['target_denominator_weights'].append(0)
    residual=certificate(truncated)['verified']
    assert residual['ordinary_edge_bound_conditional_on_transport_and_small_excess'] is None
    assert len(residual['unresolved_source_factors'])==1
    counts['negative_controls'] += 1
    root=Path(__file__).resolve().parents[1]
    paths=list((root/'Solutions').glob('*.lean'))+list((root/'scripts').glob('*.py'))
    receipt={'status':'PASS','counts':counts,'stress_test_examples':samples,
             'scope':'Finite exact rational checks only; no Lean compilation or Prove2Me verdict.',
             'helper_provenance':'Repository row_block_certificate.py at blob c402d2bb993a0e9147b942ff3d914ae0d3f6548b; used functions copied locally for execution, no changes proposed to repository helper.',
             'source_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}}
    output=root/'research/PROJECTIVE_ROW_BLOCK_CHECK_2026-09-12.json'
    output.write_text(json.dumps(jsonable(receipt),indent=2,sort_keys=True)+'\n')
    fixture=root/'research/projective_cube_4d_input.json'
    fixture.write_text(json.dumps(jsonable(good),indent=2)+'\n')
    print(json.dumps(jsonable(receipt),indent=2,sort_keys=True))


if __name__=='__main__': main()
