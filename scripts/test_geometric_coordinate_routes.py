#!/usr/bin/env python3
"""Exact finite-hull regression, not a Lean compiler or a verified Python parser.

Facet discovery is exhaustive in an independently checked intrinsic coordinate
chart. The edge constructor uses normalized contrasts, not the reference graph.
All arithmetic is rational; the small reference models deliberately include
redundant generators, nonsimple vertices and lower-dimensional hulls.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from math import gcd, lcm
from pathlib import Path
import argparse
import json
import random
import sympy as sp


def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Q(0))


def sub(a, b):
    return tuple(x-y for x,y in zip(a,b))


def rank(rows):
    return sp.Matrix(rows).rank() if rows else 0


def primitive(row):
    vals=[Q(x) for x in row]
    den=lcm(*(x.denominator for x in vals)) if vals else 1
    ints=[int(x*den) for x in vals]
    g=0
    for x in ints:
        g=gcd(g,abs(x))
    return tuple(x//g for x in ints) if g else tuple(ints)


def reference(points):
    points=sorted(set(tuple(Q(x) for x in p) for p in points))
    if not points:
        raise ValueError('empty hull has no requested endpoints')
    d=len(points[0])
    if any(len(p)!=d for p in points):
        raise ValueError('mixed dimensions')
    origin=points[0]
    diffs=[sub(p,origin) for p in points]
    _, cols=sp.Matrix(diffs).rref() if d else (None, ())
    r=len(cols)
    # Pivot coordinate projection is injective on the entire affine hull.
    projected=[tuple(p[j] for j in cols) for p in points]
    assert rank(diffs)==rank([sub(x,projected[0]) for x in projected])
    assert len(set(projected))==len(points)
    if r==0:
        return dict(points=points, vertices=points, rows=[], edges=set(),
                    faces={frozenset({0})}, dimension=0, bases=0, nonsimple=0)
    facets={}
    bases=0
    for I in combinations(range(len(points)),r):
        bases+=1
        ns=sp.Matrix([(*projected[i],Q(1)) for i in I]).nullspace()
        if len(ns)!=1:
            continue
        a=tuple(Q(x) for x in ns[0][:-1]); b=-Q(ns[0][-1])
        slacks=[b-dot(a,p) for p in projected]
        if min(slacks)<0 and max(slacks)>0:
            continue
        if not any(slacks):
            continue
        if max(slacks)<=0:
            a=tuple(-x for x in a); b=-b
        full=[Q(0)]*d
        for j,z in zip(cols,a): full[j]=z
        row=primitive((*full,b))
        facets[row]=row
    rows=sorted(facets)
    active=[{i for i,row in enumerate(rows) if dot(row[:-1],p)==row[-1]} for p in points]
    verts=[p for p,I in zip(points,active) if rank([rows[i][:-1] for i in I])==r]
    assert verts
    tight=[{i for i,row in enumerate(rows) if dot(row[:-1],p)==row[-1]} for p in verts]
    edges=set()
    for i,j in combinations(range(len(verts)),2):
        common=tight[i]&tight[j]
        if rank([rows[k][:-1] for k in common])==r-1:
            # Whole supporting intersection, not just a feasible chord.
            maximizers={k for k,p in enumerate(verts)
                        if all(dot(rows[t][:-1],p)==rows[t][-1] for t in common)}
            assert maximizers=={i,j}
            edges.add((i,j))
    facets_v=[frozenset(k for k,p in enumerate(verts) if dot(row[:-1],p)==row[-1]) for row in rows]
    faces={frozenset(range(len(verts)))}
    for A in facets_v:
        faces|={F&A for F in tuple(faces) if F&A}
    return dict(points=points,vertices=verts,rows=rows,edges=edges,faces=faces,
                dimension=r,bases=bases,nonsimple=sum(len(I)>r for I in tight))


def improving_edge(model, F, u, objective):
    """Construct an improving exposed edge in the actual retained face.

The inherited original facet normals strictly expose u relative to F. Contrast
regularization then selects the entire one-dimensional support face. The
reference edge table is intentionally not read here.
"""
    vertices=model['vertices']; points=model['points']; rows=model['rows']
    facepoints=[p for p in points if all(dot(row[:-1],p)==row[-1] for row in rows
                if all(dot(row[:-1],vertices[i])==row[-1] for i in F))]
    origin=vertices[u]
    if not any(dot(objective,sub(p,origin))>0 for p in facepoints):
        raise ValueError('no better point in retained face')
    active=[row for row in rows if dot(row[:-1],origin)==row[-1]]
    h=tuple(-sum((Q(row[j]) for row in active),Q(0)) for j in range(len(origin)))
    D=[p for p in facepoints if p!=origin]
    assert all(dot(h,sub(p,origin))>0 for p in D)
    contrasts=[]
    for p in D:
        for z in D:
            dp=sub(p,origin); dz=sub(z,origin)
            s=tuple(dot(h,dp)*y-dot(h,dz)*x for x,y in zip(dp,dz))
            if any(s): contrasts.append(s)
    contrasts=sorted(set(contrasts))
    d=len(origin)
    for T in range(len(contrasts)*max(0,d-1)+2):
        k=tuple(Q(T**j) for j in range(d))
        if all(dot(k,s)!=0 for s in contrasts): break
    else: raise AssertionError('finite polynomial-root bound failed')
    eps=min([Q(1)]+[abs(dot(objective,s))/(2*(abs(dot(k,s))+1))
                    for s in contrasts if dot(objective,s)!=0])
    g=tuple(x+eps*y for x,y in zip(objective,k))
    assert all(dot(g,s)!=0 for s in contrasts)
    assert all((dot(g,s)>0)==(dot(objective,s)>0) for s in contrasts if dot(objective,s)!=0)
    M=max(dot(g,sub(p,origin))/dot(h,sub(p,origin)) for p in D)
    q=tuple(x-M*y for x,y in zip(g,h))
    tied=[p for p in D if dot(q,sub(p,origin))==0]
    endpoint=max(tied,key=lambda p:dot(h,sub(p,origin)))
    assert dot(objective,sub(endpoint,origin))>0
    Dv=sub(endpoint,origin)
    for p in facepoints:
        assert dot(q,sub(p,origin))<=0
        if dot(q,sub(p,origin))==0:
            t=dot(h,sub(p,origin))/dot(h,Dv)
            assert 0<=t<=1
            assert sub(p,origin)==tuple(t*z for z in Dv)
    v=vertices.index(endpoint)
    if v not in F: raise AssertionError('endpoint outside retained original face')
    return v, dict(u=u,v=v,face=sorted(F),objective=objective,support=q,
                   separator=h,eps=eps,contrast_count=len(contrasts))


def route(model, u, v, saved):
    V=model['vertices']; d=len(V[0]); F=frozenset(range(len(V)))
    levels=[sorted({x[j] for x in V}) for j in range(d)]
    K=[len(s)-1 for s in levels]
    def walk_to(F,x,j,up):
        p=[x]
        target=(max if up else min)(V[i][j] for i in F)
        objective=tuple(Q((1 if up else -1) if k==j else 0) for k in range(d))
        while V[p[-1]][j]!=target:
            z,record=improving_edge(model,F,p[-1],objective)
            saved.append(record); p.append(z)
            if len(p)>len(levels[j]): raise AssertionError('rank budget exceeded')
        return p
    def rec(F,u,v,j):
        if u==v: return [u]
        if j==d: raise AssertionError('coordinates failed to separate vertices')
        up=levels[j].index(V[u][j])+levels[j].index(V[v][j])>K[j]
        a=walk_to(F,u,j,up); b=walk_to(F,v,j,up)
        assert len(a)+len(b)-2<=K[j]
        t=V[a[-1]][j]
        F1=frozenset(i for i in F if V[i][j]==t)
        assert F1 in model['faces']
        mid=rec(F1,a[-1],b[-1],j+1)
        return a[:-1]+mid+b[-2::-1]
    p=rec(F,u,v,0)
    assert p[0]==u and p[-1]==v and len(p)-1<=sum(K)
    return p,K


def verify_record(model, record):
    """Independent certificate consumer: no contrast or neighbor construction."""
    V=model['vertices']; F=frozenset(record['face']); u=record['u']; v=record['v']
    if u==v or u not in F or v not in F or F not in model['faces']:
        raise ValueError('invalid endpoints/face')
    q=tuple(Q(x) for x in record['support']); f=tuple(Q(x) for x in record['objective'])
    if len(q)!=len(V[0]) or len(f)!=len(V[0]): raise ValueError('wrong functional dimension')
    if dot(f,V[v])<=dot(f,V[u]): raise ValueError('not improving')
    maximum=max(dot(q,V[i]) for i in F)
    maximizers={i for i in F if dot(q,V[i])==maximum}
    if maximizers!={u,v}: raise ValueError('support face is not the whole requested edge')
    if tuple(sorted((u,v))) not in model['edges']:
        raise ValueError('not an original edge')
    return True


def models():
    out=[('point0',[()]), ('point3',[(2,3,5)]),
         ('segment_redundant',[(0,0),(1,2),(2,4),(3,6)]),
         ('square_redundant',[(0,0),(1,0),(0,1),(1,1),(Q(1,2),Q(1,2)),(Q(1,2),0)]),
         ('pyramid_nonsimple',[(0,0,0),(1,0,0),(1,1,0),(0,1,0),(Q(1,2),Q(1,2),1)]),
         ('cube3',list(product(range(2),repeat=3))),
         ('hypersimplex4', [x for x in product(range(2),repeat=4) if sum(x)==2]),
         ('simplex4',[(0,)*4]+[tuple(int(i==j) for j in range(4)) for i in range(4)]),
         ('rational_polygon',[(0,0),(3,0),(4,1),(3,3),(0,4),(-1,2),(1,1)]),
         ('tiny_gap',[(0,0),(1,0),(1,Q(1,2**80)),(0,1)])]
    rng=random.Random(320283)
    for i in range(4):
        pts=sorted(rng.sample(list(product(range(2),repeat=4)),8))
        out.append((f'zero_one_random{i}',pts))
    return out


def encoded(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:encoded(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [encoded(v) for v in x]
    return x


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--model',default='all'); args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    results=[]; fixtures=[]
    for name,points in models():
        if args.model!='all' and name!=args.model: continue
        model=reference(points); V=model['vertices']; saved=[]; counts=dict(routes=0,edges=0,shortest_edges=0,nonshortest=0,local_checks=0)
        nbr=[set() for _ in V]
        for a,b in model['edges']: nbr[a].add(b); nbr[b].add(a)
        distances=[]
        for u in range(len(V)):
            dist={u:0}; queue=[u]
            for x in queue:
                for y in nbr[x]:
                    if y not in dist: dist[y]=dist[x]+1; queue.append(y)
            distances.append(dist)
            assert len(dist)==len(V)
        for F in sorted(model['faces'],key=lambda x:(len(x),sorted(x))):
            for j in range(len(V[0])):
                for u in sorted(F):
                    for sign in [-1,1]:
                        if not any(sign*V[v][j]>sign*V[u][j] for v in F): continue
                        f=tuple(Q(sign if k==j else 0) for k in range(len(V[0])))
                        v,rec=improving_edge(model,F,u,f)
                        verify_record(model,rec); counts['local_checks']+=1
        for u in range(len(V)):
            for v in range(len(V)):
                p,K=route(model,u,v,saved)
                for a,b in zip(p,p[1:]): assert tuple(sorted((a,b))) in model['edges']
                counts['routes']+=1; counts['edges']+=len(p)-1
                counts['shortest_edges']+=distances[u][v]
                counts['nonshortest']+=int(len(p)-1>distances[u][v])
                if all(all(x in (0,1) for x in z) for z in model['points']): assert len(p)-1<=len(V[0])
        for rec in saved: verify_record(model,rec)
        # Disable production before consuming the saved certificates a second time.
        production=globals()['improving_edge']
        globals()['improving_edge']=lambda *a,**k: (_ for _ in ()).throw(RuntimeError('producer disabled'))
        for rec in saved: verify_record(model,rec)
        globals()['improving_edge']=production
        result=dict(name=name,generators=len(model['points']),vertices=len(V),dimension=model['dimension'],
                    ambient_dimension=len(V[0]),facets=len(model['rows']),reference_edges=len(model['edges']),
                    faces=len(model['faces']),active_system_candidates=model['bases'],nonsimple_vertices=model['nonsimple'],
                    redundant_generators=len(model['points'])-len(V),**counts,saved_certificates=len(saved))
        results.append(result)
        fixtures.append(dict(name=name,points=model['points'],vertices=V,rows=model['rows'],records=saved))
        print(json.dumps(result),flush=True)
    report=dict(kind='exact_rational_supporting_tests_not_Lean_verification',models=results)
    (args.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(encoded(fixtures),indent=2)+'\n')

if __name__=='__main__': main()
