#!/usr/bin/env python3
"""Exact graph certificate for the posted Q28 polar.

First run enumerate_q28.cpp in this directory. This script uses exact SymPy
rational linear algebra for active-set ranks and an integer encoding for all
coordinates. No floating-point predicates are used.
"""
from __future__ import annotations
import itertools, json
from collections import Counter, deque
from pathlib import Path
import sympy as sp

HERE = Path(__file__).resolve().parent
A = [
[18,0,0,0,1],[-18,0,0,0,1],[0,0,30,0,1],[0,0,-30,0,1],
[0,0,0,30,1],[0,0,0,-30,1],[0,5,0,25,1],[0,5,0,-25,1],
[0,-5,0,25,1],[0,-5,0,-25,1],[0,0,18,18,1],[0,0,18,-18,1],
[0,0,-18,18,1],[0,0,-18,-18,1],[0,0,18,0,-1],[0,0,-18,0,-1],
[0,30,0,0,-1],[0,-30,0,0,-1],[30,0,0,0,-1],[-30,0,0,0,-1],
[25,0,0,5,-1],[25,0,0,-5,-1],[-25,0,0,5,-1],[-25,0,0,-5,-1],
[18,18,0,0,-1],[18,-18,0,0,-1],[-18,18,0,0,-1],[-18,-18,0,0,-1]]

def dot(a, b): return sum(x*y for x,y in zip(a,b))

def bfs(adj, sources):
    ds=[None]*len(adj); prev=[None]*len(adj); q=deque(sources)
    for s in sources: ds[s]=0
    while q:
        x=q.popleft()
        for y in adj[x]:
            if ds[y] is None:
                ds[y]=ds[x]+1; prev[y]=x; q.append(y)
    return ds, prev

def main():
    rows=[list(map(int,s.split())) for s in (HERE/'vertices_raw.txt').read_text().splitlines()]
    vertices=[]
    for r in rows:
        nums,den,basis=r[:5],r[5],r[6:]
        assert den>0
        assert all(dot(a, nums)<=den for a in A)
        active=[i for i,a in enumerate(A) if dot(a, nums)==den]
        assert set(basis)<=set(active)
        assert sp.Matrix([A[i] for i in basis]).det()!=0
        vertices.append({'numerators':nums,'denominator':den,'basis':basis,'active_rows':active})
    N=len(vertices); graph=[[] for _ in range(N)]; edges=[]
    # For distinct vertices of a full-dimensional H-polytope, a segment is an
    # edge iff the common active row normals have rank d-1 (=4 here).
    for x,y in itertools.combinations(range(N),2):
        common=sorted(set(vertices[x]['active_rows']) & set(vertices[y]['active_rows']))
        if len(common)<4: continue
        rk=sp.Matrix([A[i] for i in common]).rank()
        assert rk<5
        if rk==4:
            graph[x].append(y);graph[y].append(x);edges.append([x,y])
    u=next(i for i,v in enumerate(vertices) if v['numerators']==[0,0,0,0,v['denominator']])
    v=next(i for i,w in enumerate(vertices) if w['numerators']==[0,0,0,0,-w['denominator']])
    ds,prev=bfs(graph,[u]); assert all(d is not None for d in ds)
    assert ds[v]==6
    assert all(abs(ds[x]-ds[y])<=1 for x,y in edges)
    path=[]; x=v
    while x is not None: path.append(x);x=prev[x]
    path.reverse()
    dl,_=bfs(graph,graph[u]); link_min=min(dl[x] for x in graph[v]); assert link_min==4
    for i,z in enumerate(vertices):z['level_from_u']=ds[i]
    # Quotient by independent sign changes in the first four coordinates.
    def orbit_key(z):
        return tuple(abs(t) for t in z['numerators'][:4])+tuple(z['numerators'][4:])+ (z['denominator'],)
    keys=sorted({orbit_key(z) for z in vertices}); key_to_id={k:i for i,k in enumerate(keys)}
    orbit_ids=[key_to_id[orbit_key(z)] for z in vertices]
    orbits=[]
    for k in keys:
        ids=[i for i,z in enumerate(vertices) if orbit_key(z)==k]
        assert len(set(ds[i] for i in ids))==1
        orbits.append({'numerators':list(k[:5]),'denominator':k[5],
                       'vertex_ids':ids,'level_from_u':ds[ids[0]]})
    quotient_edges=sorted({tuple(sorted([orbit_ids[x],orbit_ids[y]])) for x,y in edges})
    summary={'vertex_count':N,'edge_count':len(edges),'u_index':u,'v_index':v,
      'apex_distance':ds[v], 'layers_from_u':dict(sorted(Counter(ds).items())),
      'apex_neighbor_counts':[len(graph[u]),len(graph[v])],
      'distance_between_apex_neighbor_sets':link_min,'six_edge_path_indices':path,
      'sign_orbit_count':len(orbits),'quotient_edge_count':len(quotient_edges)}
    data={'status':'Exact external computation; not a Lean-checked proof',
      'source_definition':'https://prove2.me/theorems/c44f1578-cc0e-4f73-b0c0-c71adf68e576',
      'target':'Hirsch.q28_polar_no_length_five_walk','A':A,'b':[1]*28,
      'summary':summary,'vertices':vertices,'edges':edges,
      'sign_orbits':orbits,'sign_quotient_edges':quotient_edges}
    (HERE/'q28_certificate.json').write_text(json.dumps(data,indent=2)+'\n')
    (HERE/'q28_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print('Sign orbits (id, numerators, denominator, level, multiplicity)')
    for i,o in enumerate(orbits):print(i,o['numerators'],o['denominator'],o['level_from_u'],len(o['vertex_ids']))
    print('Quotient edges:',quotient_edges)

if __name__=='__main__':main()
