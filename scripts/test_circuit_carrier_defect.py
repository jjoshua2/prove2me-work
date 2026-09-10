#!/usr/bin/env python3
"""Exact rational carrier-defect regressions; not a universal or Lean proof.
Vertices use exhaustive bases. Edges use the number of vertices in the common
face, independently of rank. Circuit supports are checked by neutral kernels.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
from itertools import combinations, product
import json
from math import gcd, lcm
from pathlib import Path
from typing import Iterable, Sequence
Vector = tuple[Q, ...]

def dot(x: Sequence[Q], y: Sequence[Q]) -> Q:
    return sum((a*b for a,b in zip(x,y,strict=True)), Q(0))

def rref(rows: Iterable[Sequence[Q]], d: int):
    a = [list(map(Q,row)) for row in rows]
    piv = []
    for j in range(d):
        k = next((k for k in range(len(piv),len(a)) if a[k][j]),None)
        if k is None: continue
        i = len(piv)
        a[i],a[k] = a[k],a[i]
        scale = a[i][j]
        a[i] = [x/scale for x in a[i]]
        for k in range(len(a)):
            if k != i:
                scale = a[k][j]
                a[k] = [x-scale*y for x,y in zip(a[k],a[i],strict=True)]
        piv.append(j)
    return a,piv

def rank(rows,d): return len(rref(rows,d)[1])

def nullspace(rows,d):
    a,piv = rref(rows,d)
    out=[]
    for j in range(d):
        if j in piv: continue
        v=[Q(0)]*d
        v[j]=Q(1)
        for i,p in enumerate(piv): v[p]=-a[i][j]
        out.append(tuple(v))
    return out

def primitive(v):
    den=lcm(*(x.denominator for x in v))
    ns=[int(x*den) for x in v]
    div=gcd(*ns)
    if not div: raise ValueError('zero direction')
    sign=1 if next(x for x in ns if x)>0 else -1
    return tuple(Q(sign*x//div) for x in ns)

class Polytope:
    def __init__(self,name,a,b):
        self.name=name
        self.a=tuple(tuple(map(Q,row)) for row in a)
        self.b=tuple(map(Q,b))
        self.n,self.d=len(self.a),len(self.a[0])
        assert len(self.b)==self.n and rank(self.a,self.d)==self.d
        vs=set()
        for inds in combinations(range(self.n),self.d):
            red,piv=rref([(*self.a[i],self.b[i]) for i in inds],self.d)
            if len(piv)==self.d:
                v=tuple(row[-1] for row in red)
                if self.feasible(v): vs.add(v)
        self.vertices=tuple(sorted(vs))
        assert vs and rank([tuple(v[j]-self.vertices[0][j] for j in range(self.d))
                            for v in self.vertices[1:]],self.d)==self.d
        # Exact boundedness: every signed coordinate functional is a
        # nonnegative combination of describing rows.
        for j in range(self.d):
            for sign in (-1,1):
                assert self.in_row_cone(tuple(Q(sign if k==j else 0) for k in range(self.d)))
        self.active={v:self.tight(v) for v in self.vertices}
        self.graph={v:set() for v in self.vertices}
        for x,y in combinations(self.vertices,2):
            if len(self.face_vertices(self.active[x]&self.active[y]))==2:
                self.graph[x].add(y); self.graph[y].add(x)
        self.distances={v:self.bfs(v) for v in self.vertices}
        assert all(len(ds)==len(vs) for ds in self.distances.values())
        dirs=set()
        for inds in combinations(range(self.n),self.d-1):
            basis=nullspace([self.a[i] for i in inds],self.d)
            if len(basis)==1: dirs.add(primitive(basis[0]))
        self.circuits=tuple(sorted(dirs))
        for g in self.circuits:
            neutral=[row for row in self.a if not dot(row,g)]
            assert rank(neutral,self.d)==self.d-1
            # Killing any additional supported row leaves only the zero vector.
            for row in self.a:
                if dot(row,g): assert rank([*neutral,row],self.d)==self.d
    def in_row_cone(self,e):
        for inds in combinations(range(self.n),self.d):
            red,piv=rref([[*(self.a[i][j] for i in inds),e[j]] for j in range(self.d)],self.d)
            if len(piv)==self.d and all(row[-1]>=0 for row in red): return True
        return False
    def feasible(self,x): return all(dot(row,x)<=rhs for row,rhs in zip(self.a,self.b,strict=True))
    def tight(self,x): return frozenset(i for i,row in enumerate(self.a) if dot(row,x)==self.b[i])
    def face_vertices(self,inds):
        inds=tuple(inds)
        return tuple(v for v in self.vertices if all(dot(self.a[i],v)==self.b[i] for i in inds))
    def bfs(self,x,allowed=None):
        ds={x:0}; todo=deque([x])
        while todo:
            u=todo.popleft()
            for v in sorted(self.graph[u]):
                if v not in ds and (allowed is None or v in allowed):
                    ds[v]=ds[u]+1; todo.append(v)
        return ds
    def step(self,x,g):
        ts=[(self.b[i]-dot(row,x))/dot(row,g) for i,row in enumerate(self.a) if dot(row,g)>0]
        assert ts
        t=min(ts)
        if t<=0: return None
        y=tuple(xx+t*gg for xx,gg in zip(x,g,strict=True))
        assert self.feasible(y)
        assert any(dot(row,g)>0 and dot(row,y)==rhs for row,rhs in zip(self.a,self.b,strict=True))
        return y
    def carrier(self,x,y):
        g=tuple(yy-xx for xx,yy in zip(x,y,strict=True))
        assert any(g) and self.feasible(x) and self.feasible(y)
        common=self.tight(x)&self.tight(y)
        active_neutral=frozenset(i for i in self.tight(x) if not dot(self.a[i],g))
        assert common==active_neutral
        r=rank([self.a[i] for i in common],self.d)
        h=self.d-r; kappa=max(0,self.d-1-r)
        assert kappa+1==h
        basis=nullspace([self.a[i] for i in common],self.d)
        m=sum(any(dot(row,w) for w in basis) for row in self.a)
        assert m<=self.n-self.d+h
        vs=self.face_vertices(common)
        assert vs and h==rank([tuple(v[j]-vs[0][j] for j in range(self.d)) for v in vs[1:]],self.d)
        return h,kappa,m,common

def box(d):
    return Polytope(f'box_{d}',[tuple(sign if j==k else 0 for j in range(d))
                               for k in range(d) for sign in (-1,1)],[0,1]*d)
def simplex(d):
    return Polytope(f'simplex_{d}',[tuple(-int(j==k) for j in range(d)) for k in range(d)]
                    +[(1,)*d],[0]*d+[1])
def hexagon(extra=0):
    a=[(-1,-1),(0,-1),(1,-1),(1,1),(0,1),(-1,1)]
    rows=[(*row,*((0,)*extra)) for row in a]
    for k in range(extra):
        for sign in (-1,1): rows.append((0,0,*(sign if j==k else 0 for j in range(extra))))
    return Polytope(f'hexagon_times_box_{extra}',rows,[0,1,3,3,1,0]+[0,1]*extra)

def run():
    ps=[box(d) for d in range(1,5)]+[simplex(d) for d in range(2,5)]+[hexagon(d) for d in range(3)]
    ps += [Polytope('octahedron',list(product((-1,1),repeat=3)),[1]*8),
           Polytope('redundant_square',[(-1,0),(1,0),(0,-1),(0,1),(1,1),(0,0)],[0,1,0,1,2,5])]
    totals=dict.fromkeys(['commuting_step_swaps','vertex_pairs','maximal_steps','vertex_start_steps','nonvertex_start_steps',
                         'nonvertex_end_steps','zero_defect_vertex_start_steps','rounded_walks',
                         'rounded_walks_with_nonvertex_checkpoints'],0)
    summaries=[]
    for p in ps:
        counts=dict.fromkeys(totals,0)
        for x,y in combinations(p.vertices,2):
            _,kappa,_,_=p.carrier(x,y)
            assert (y in p.graph[x])==(kappa==0)
            counts['vertex_pairs']+=1
        center=tuple(sum(v[j] for v in p.vertices)/len(p.vertices) for j in range(p.d))
        seeds=set(p.vertices)|{center}
        seeds|={tuple((x[j]+y[j])/2 for j in range(p.d)) for x,y in combinations(p.vertices,2)}
        dirs=[tuple(sign*q for q in g) for g in p.circuits for sign in (-1,1)]
        for x in sorted(seeds):
            for g in dirs:
                y=p.step(x,g)
                if y is None: continue
                h,kappa,m,_=p.carrier(x,y)
                counts['maximal_steps']+=1
                vx,vy=x in p.graph,y in p.graph
                counts['vertex_start_steps' if vx else 'nonvertex_start_steps']+=1
                counts['nonvertex_end_steps']+=int(not vy)
                if vx:
                    assert (vy and y in p.graph[x])==(kappa==0)
                    counts['zero_defect_vertex_start_steps']+=int(kappa==0)
                for hh in dirs:
                    if not all(dot(row,g)==0 or dot(row,hh)==0 for row in p.a):
                        continue
                    z=p.step(y,hh)
                    if z is None: continue
                    w=p.step(x,hh)
                    assert w is not None
                    assert w==tuple(x[j]+z[j]-y[j] for j in range(p.d))
                    assert p.step(w,g)==z
                    counts['commuting_step_swaps']+=1
                if vx and vy:
                    assert 2*kappa+p.d+1<=p.n
                    assert p.distances[x][y]<=m*2**max(0,kappa-2)
        for start in p.vertices:
            for offset in range(min(8,len(dirs))):
                w=[start]; carriers=[]; budgets=[]
                for j in range(5):
                    options=[p.step(w[-1],g) for g in dirs]
                    options=[y for y in options if y is not None]
                    y=options[(offset+3*j)%len(options)]
                    h,kappa,m,common=p.carrier(w[-1],y)
                    w.append(y); carriers.append(set(p.face_vertices(common)))
                    budgets.append(m*2**max(0,kappa-2))
                # Final feasible point is rounded to a vertex of its minimal
                # face. This tests the stronger face-covered-chain assembly,
                # not a claim that every generated walk ended at a vertex.
                rounded=[x if x in p.graph else p.face_vertices(p.tight(x))[0] for x in w]
                length=0
                for j,face in enumerate(carriers):
                    assert rounded[j] in face and rounded[j+1] in face
                    dist=p.bfs(rounded[j],face)[rounded[j+1]]
                    assert dist<=budgets[j]
                    length+=dist
                assert p.distances[rounded[0]][rounded[-1]]<=length<=sum(budgets)
                counts['rounded_walks']+=1
                counts['rounded_walks_with_nonvertex_checkpoints']+=int(any(x not in p.graph for x in w[1:-1]))
        for key,val in counts.items(): totals[key]+=val
        summaries.append({'name':p.name,'dimension':p.d,'rows':p.n,'vertices':len(p.vertices),
                          'circuits_up_to_sign':len(p.circuits),**counts})
    triangle=simplex(2)
    tx,ty,tz=(Q(0),Q(1)),(Q(0),Q(0)),(Q(1),Q(0))
    tg,th=(Q(0),Q(-1)),(Q(1),Q(0))
    assert triangle.step(tx,tg)==ty and triangle.step(ty,th)==tz
    assert all(a*b==0 for a,b in zip(tg,th,strict=True))
    assert not triangle.feasible((Q(1),Q(1)))
    assert not all(dot(row,tg)==0 or dot(row,th)==0 for row in triangle.a)
    p=hexagon(); x,y=(Q(0),Q(0)),(Q(3),Q(0))
    assert p.step(x,(Q(1),Q(0)))==y and p.carrier(x,y)[:2]==(2,1) and p.distances[x][y]==3
    return {'evidence_level':'exact finite rational regression, not Lean verification','totals':totals,
            'coordinate_support_swap_obstruction':{'polytope':'x>=0,y>=0,x+y<=1',
                'original_walk':[['0','1'],['0','0'],['1','0']],
                'swapped_intermediate':['1','1'],'swapped_intermediate_feasible':False},
            'product_carrier_barrier':product_carrier_barrier(),'polytopes':summaries,'hexagon_obstruction':{'source':['0','0'],'target':['3','0'],
            'all_neutral_rank':1,'active_neutral_rank':0,'active_defect':1,
            'common_face_dimension':2,'maximal_circuit_steps':1,'edge_distance':3}}

def product_carrier_barrier():
    """An exact family: short circuit routes can have linearly growing active
    defect even in products of one fixed hexagon. Large products use exact
    blockwise ranks; graph BFS is independently performed only for k<=4.
    """
    p=hexagon()
    u=(Q(1),Q(-1)); mid=(Q(5,2),Q(1,2)); v=(Q(3),Q(0))
    enter=(Q(1),Q(1)); leave=(Q(1),Q(-1)); zero=(Q(0),Q(0))
    assert p.step(u,enter)==mid and p.step(mid,leave)==v
    assert u in p.graph and v in p.graph and mid not in p.graph
    assert p.distances[u][v]==2
    results=[]
    for k in range(1,33):
        current=[u]*k; defects=[]; dimensions=[]; effective=[]; minimal_rows=[]; exact_face_cost=[]
        for phase in ('enter','leave'):
            for moving in range(k):
                nxt=current.copy()
                g=enter if phase=='enter' else leave
                nxt[moving]=p.step(current[moving],g)
                assert nxt[moving] is not None
                r_active=0; r_all=0; m=0; m_min=0; true_face_diameter=0
                for block in range(k):
                    direction=g if block==moving else zero
                    common=p.tight(current[block])&p.tight(nxt[block])
                    r_active+=rank([p.a[i] for i in common],2)
                    neutral=[row for row in p.a if not dot(row,direction)]
                    r_all+=rank(neutral,2)
                    basis=nullspace([p.a[i] for i in common],2)
                    m+=sum(any(dot(row,w) for w in basis) for row in p.a)
                    # Independent graph diameter of each factor face.
                    face=set(p.face_vertices(common))
                    true_face_diameter+=max(max(p.bfs(q,face).values()) for q in face)
                    m_min+={1:0,2:2,6:6}[len(face)]
                assert r_all==2*k-1
                h=2*k-r_active; kappa=2*k-1-r_active
                assert h==kappa+1
                expected=(moving+1) if phase=='enter' else (k-moving-1)
                assert kappa==expected
                assert true_face_diameter==(moving+3 if phase=='enter' else k-moving)
                defects.append(kappa); dimensions.append(h); effective.append(m)
                exact_face_cost.append(true_face_diameter); minimal_rows.append(m_min)
                current=nxt
        assert current==[v]*k and max(defects)==k and len(defects)==2*k
        assert max(dimensions)==k+1 and sum(exact_face_cost)==k*k+3*k
        larman_cost=sum(m*2**max(0,q-2) for m,q in zip(effective,defects,strict=True))
        assert larman_cost>=(4*k+2)*2**max(0,k-2)
        minimal_larman_cost=sum(m*2**max(0,q-2) for m,q in zip(minimal_rows,defects,strict=True))
        assert minimal_larman_cost>=(2*k+4)*2**max(0,k-2)
        scheduled=[u]*k; scheduled_defects=[]
        for block in range(k):
            for direction in (enter,leave):
                nxt=scheduled.copy(); nxt[block]=p.step(scheduled[block],direction)
                r=sum(rank([p.a[i] for i in p.tight(scheduled[j])&p.tight(nxt[j])],2)
                      for j in range(k))
                scheduled_defects.append(2*k-1-r)
                scheduled=nxt
        assert scheduled==[v]*k and scheduled_defects==[1,0]*k
        bfs_distance=None
        if k<=4:
            start=(u,)*k; target=(v,)*k
            ds={start:0}; todo=deque([start])
            while todo and target not in ds:
                state=todo.popleft()
                for block in range(k):
                    for neighbor in p.graph[state[block]]:
                        ns=state[:block]+(neighbor,)+state[block+1:]
                        if ns not in ds: ds[ns]=ds[state]+1; todo.append(ns)
            bfs_distance=ds[target]
            assert bfs_distance==2*k
        results.append({'k':k,'dimension':2*k,'rows':6*k,'circuit_route_length':2*k,
            'maximum_active_defect':k,'maximum_carrier_dimension':k+1,
            'blockwise_schedule_maximum_defect':max(scheduled_defects),
            'sum_effective_row_larman_budgets':larman_cost,
            'sum_minimal_product_facet_larman_budgets':minimal_larman_cost,
            'sum_exact_product_carrier_diameters':sum(exact_face_cost),
            'endpoint_distance_product_formula':2*k,'endpoint_distance_explicit_bfs':bfs_distance,
            'defect_sequence':defects})
    return {'rank_verification':'exact rational 2D blocks, direct-sum ranks',
            'graph_verification':'full Cartesian graph BFS for k=1..4; product formula for larger k',
            'instances':results}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(run(),indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text,encoding='utf-8')
    print(text)
if __name__=='__main__': main()
