#!/usr/bin/env python3
"""Exact original-H affine-roof regression. Not Lean-extracted software.

The small independent reference enumerates ALL full active systems in the given
H-description, including explicit affine-hull equations for lower-dimensional
bases. Saved edge consumers verify original inequalities, active rank and the
ENTIRE line parameter interval. No auxiliary projected edge is accepted.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import comb
from pathlib import Path
import random
import sympy as sp
import test_geometric_coordinate_routes as base


def dot(a,b): return sum((x*y for x,y in zip(a,b)),F(0))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))

def solve(rows, rhs):
    """Exact independent square elimination; returns None for a singular system."""
    n=len(rows)
    if not n: return ()
    a=[list(map(F,r))+[F(v)] for r,v in zip(rows,rhs)]
    for j in range(n):
        q=next((q for q in range(j,n) if a[q][j]),None)
        if q is None:return None
        a[j],a[q]=a[q],a[j]; p=a[j][j]
        a[j]=[v/p for v in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                t=a[i][j];a[i]=[v-t*w for v,w in zip(a[i],a[j])]
    return tuple(r[-1] for r in a)

def matrix_rank(rows,n):
    a=[list(map(F,r)) for r in rows]; p=0
    for j in range(n):
        q=next((q for q in range(p,len(a)) if a[q][j]),None)
        if q is None:continue
        a[p],a[q]=a[q],a[p];v=a[p][j];a[p]=[x/v for x in a[p]]
        for i in range(p+1,len(a)):
            if a[i][j]:
                v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[p])]
        p+=1
        if p==n:break
    return p

def full_vertices(rows,n):
    found=set(); systems=0; nonsingular=0
    for I in combinations(range(len(rows)),n):
        systems+=1
        v=solve([rows[i][:-1] for i in I],[rows[i][-1] for i in I])
        if v is None:continue
        nonsingular+=1
        if all(dot(r[:-1],v)<=r[-1] for r in rows):found.add(v)
    return found,systems,nonsingular

def base_rows(points):
    ref=base.reference(points);n=len(points[0]);origin=tuple(map(F,points[0]))
    rows=[tuple(map(F,r)) for r in ref['rows']]
    if n:
        differences=[sub(p,origin) for p in points]
        for vec in sp.Matrix(differences).nullspace():
            r=tuple(F(v) for v in vec);b=dot(r,origin)
            rows.extend([(*r,b),(*(-v for v in r),-b)])
    return ref,rows

def model(name,points,k,tiny=False):
    points=sorted(set(tuple(map(F,p)) for p in points)); n=len(points[0])
    ref,D=base_rows(points)
    A=[tuple(F((-1)**(i+j)*(i+j+1),2**(i+1)) for i in range(n)) for j in range(k)]
    margin=F(1,2**80) if tiny else F(1,3)
    c=[margin-min(dot(a,p) for p in points) for a in A]
    rows=[(*r[:-1],*(F(0) for _ in range(k)),r[-1]) for r in D]
    for j,a in enumerate(A):
        e=tuple(F(int(j==q)) for q in range(k))
        rows.append((*(-v for v in a),*e,c[j]))
        rows.append((*(F(0) for _ in range(n)),*(-v for v in e),F(0)))
    return dict(name=name,base=ref,D=D,n=n,k=k,A=A,c=c,rows=rows)

def corner(M,x,bits):
    return tuple(x)+tuple(F(bit)*(c+dot(a,x)) for bit,c,a in zip(bits,M['c'],M['A']))

def classify(M,z):
    n,k=M['n'],M['k'];x=tuple(z[:n]);y=z[n:]
    if x not in M['base']['vertices']:raise ValueError('not an actual base vertex')
    bits=[]
    for j,(a,c) in enumerate(zip(M['A'],M['c'])):
        h=c+dot(a,x)
        if h<=0:raise ValueError('nonpositive fiber height')
        if y[j]==0:bits.append(0)
        elif y[j]==h:bits.append(1)
        else:raise ValueError('intermediate fiber value is not a vertex')
    return x,tuple(bits)

def vertex_check(M,z):
    rows=M['rows'];N=M['n']+M['k']
    if len(z)!=N or any(dot(r[:-1],z)>r[-1] for r in rows):raise ValueError('infeasible point')
    active=[r[:-1] for r in rows if dot(r[:-1],z)==r[-1]]
    if matrix_rank(active,N)!=N:raise ValueError('active rank does not certify an actual vertex')
    return True

def edge_check(M,u,v):
    vertex_check(M,u);vertex_check(M,v)
    if u==v:raise ValueError('degenerate edge')
    d=sub(v,u);rows=M['rows'];N=len(u)
    common=[r[:-1] for r in rows if dot(r[:-1],u)==r[-1]==dot(r[:-1],v)]
    if matrix_rank(common,N)!=N-1:raise ValueError('common supporting slice is not a line')
    lower=[];upper=[]
    for r in rows:
        s=r[-1]-dot(r[:-1],u);a=dot(r[:-1],d)
        if a>0:upper.append(s/a)
        elif a<0:lower.append(s/a)
        elif s<0:raise ValueError('empty line section')
    if not lower or not upper or max(lower)!=0 or min(upper)!=1:
        raise ValueError('segment is not the entire original support slice')
    return True

def route(M,u,v):
    x,a=classify(M,u);y,b=classify(M,v)
    out=[u];state=list(a)
    for j in range(M['k']):
        if state[j]!=b[j]:state[j]=b[j];out.append(corner(M,x,state))
    V=M['base']['vertices'];saved=[]
    path,K=base.route(M['base'],V.index(x),V.index(y),saved)
    out.extend(corner(M,V[i],b) for i in path[1:])
    if out[-1]!=v or len(out)-1>M['n']+M['k']:raise AssertionError('route count/end failure')
    return out

def candidates():
    return [model('point_d0_k0',[()],0),model('point_d0_k3',[()],3),
            model('point_embedded',[(1,0)],1),
            model('segment_no_roofs',[(0,),(1,)],0),
            model('trapezoid_signed',[(0,),(1,)],1),
            model('segment_two_roofs',[(0,),(1,)],2),
            model('segment_three_roofs',[(0,),(1,)],3),
            model('triangle_one_roof',[(0,0),(1,0),(0,1)],1),
            model('triangle_two_roofs',[(0,0),(1,0),(0,1)],2),
            model('square_two_roofs',list(product([0,1],repeat=2)),2),
            model('lower_dim_segment_roofs',[(0,0),(1,1)],2),
            model('nonsimple_octahedral_base',[p for p in product([0,1],repeat=3) if sum(p) in (1,2)],1),
            model('tiny_height',list(product([0,1],repeat=2)),1,True)]

def asjson(obj):
    if isinstance(obj,F):return str(obj)
    if isinstance(obj,dict):return {k:asjson(v) for k,v in obj.items() if k!='base'}
    if isinstance(obj,(list,tuple)):return [asjson(v) for v in obj]
    return obj

def run_small(out):
    reports=[];fixtures=[];rng=random.Random(325324)
    for M in candidates():
        V=M['base']['vertices'];n,k=M['n'],M['k'];N=n+k
        labelled=[(x,b) for x in V for b in product([0,1],repeat=k)]
        expected={corner(M,x,b) for x,b in labelled}
        actual,systems,ns=full_vertices(M['rows'],N)
        assert actual==expected,(M['name'],len(actual),len(expected))
        vertices=sorted(actual);edges=set()
        for i,j in combinations(range(len(vertices)),2):
            try:edge_check(M,vertices[i],vertices[j])
            except ValueError:continue
            edges.add((i,j))
        # Independently check exactly base-graph times cube adjacency on all pairs.
        for i,j in combinations(range(len(vertices)),2):
            x,a=classify(M,vertices[i]);y,b=classify(M,vertices[j])
            product_edge=(x==y and sum(s!=t for s,t in zip(a,b))==1) or (a==b and tuple(sorted((V.index(x),V.index(y)))) in M['base']['edges'])
            assert product_edge==((i,j) in edges)
        pairs=list(product(range(len(vertices)),repeat=2))
        if len(pairs)>100:pairs=rng.sample(pairs,100)+[(0,0)]
        adj=[set() for _ in vertices]
        for i,j in edges:adj[i].add(j);adj[j].add(i)
        distances=[]
        for i in range(len(vertices)):
            d={i:0};queue=[i]
            for x in queue:
                for y in adj[x]:
                    if y not in d:d[y]=d[x]+1;queue.append(y)
            assert len(d)==len(vertices);distances.append(d)
        records=[];total=shortest=nonshort=0
        for i,j in pairs:
            p=route(M,vertices[i],vertices[j]);length=len(p)-1
            for u,v in zip(p,p[1:]):edge_check(M,u,v)
            assert length<=n+k and length<=len(M['D'])+k
            total+=length;shortest+=distances[i][j];nonshort+=length>distances[i][j]
            records.append(p)
        producer=globals()['route'];globals()['route']=lambda *a,**kw: (_ for _ in ()).throw(RuntimeError('producer disabled'))
        for p in records:
            for u,v in zip(p,p[1:]):edge_check(M,u,v)
        globals()['route']=producer
        report=dict(name=M['name'],n=n,k=k,dimension=M['base']['dimension']+k,rows=len(M['rows']),
                    base_vertices=len(V),vertices=len(vertices),edges=len(edges),full_active_systems=systems,
                    nonsingular_systems=ns,routes=len(records),edge_occurrences=total,shortest_total=shortest,
                    nonshortest=nonshort,base_nonsimple_vertices=M['base']['nonsimple'])
        reports.append(report);fixtures.append(dict(model=M,routes=records,vertices=vertices))
        print(json.dumps(report),flush=True)
    result={'kind':'exact_original_H_supporting_checks_not_Lean_verification','models':reports}
    (out/'small-report.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'small-fixtures.json').write_text(json.dumps(asjson(fixtures),indent=2)+'\n')
    return candidates()

def controls(out):
    M=model('square',[(0,),(1,)],1);u=corner(M,(F(0),),(0,));v=corner(M,(F(1),),(0,))
    checks=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,AssertionError):checks.append({'name':name,'rejected':True})
        else:raise AssertionError('control accepted: '+name)
    reject('stationary edge',lambda:edge_check(M,u,u))
    reject('two-bit diagonal',lambda:edge_check(M,u,corner(M,(F(1),),(1,))))
    reject('intermediate fiber point',lambda:classify(M,(F(0),M['c'][0]/2)))
    reject('infeasible roof point',lambda:vertex_check(M,(F(0),M['c'][0]+1)))
    reject('interior base point',lambda:classify(M,(F(1,2),F(0))))
    reject('wrong ambient dimension',lambda:vertex_check(M,(F(0),)))
    bad=deepcopy(M);bad['c'][0]=F(0)
    reject('zero fiber height',lambda:classify(bad,u))
    bad2=deepcopy(M);bad2['c'][0]=-1
    reject('negative fiber height',lambda:classify(bad2,u))
    # The strict positivity premise is necessary for bit-label injectivity.
    assert corner(bad,(F(0),),(0,))==corner(bad,(F(0),),(1,))
    (out/'negative-controls.json').write_text(json.dumps({'kind':'malformed_controls_and_boundary_example','checks':checks,'zero_height_label_collision':True},indent=2)+'\n')
    print('negative controls',len(checks),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--stage',choices=['small','controls'],default='small');args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    if args.stage=='small':run_small(args.out)
    else:controls(args.out)
