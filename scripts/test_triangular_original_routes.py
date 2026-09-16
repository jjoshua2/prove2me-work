#!/usr/bin/env python3
"""Exact support/rank checks for the separate all-real Lean route theorem.
Finite tests are not a substitute for compilation or kernel verification.
"""
from collections import deque
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import argparse, hashlib, json
import sympy as sp


def point(e, bits):
    previous = Q(0); out = []
    for bit in reversed(bits):
        previous = 1-e*previous if bit else e*previous
        out.append(previous)
    return tuple(reversed(out))


def rows(e, d):
    out = []
    for i in range(d):
        out.extend([(tuple(Q(-1 if j == i else 0) for j in range(d)), Q(0)),
                    (tuple(Q(1 if j == i else 0) for j in range(d)), Q(1))])
    for i in range(d-1):
        out.extend([(tuple(Q(-1) if j == i else e if j == i+1 else Q(0) for j in range(d)), Q(0)),
                    (tuple(Q(1) if j == i else e if j == i+1 else Q(0) for j in range(d)), Q(1))])
    return out


def dot(a, x):
    return sum((a0*x0 for a0, x0 in zip(a, x)), Q(0))


def route(a, b):
    current = list(a); out = [tuple(current)]
    for i in range(len(a)):
        if current[i] != b[i]:
            current[i] = b[i]; out.append(tuple(current))
    return out


def run():
    counts = dict(models=0, active_bases=0, independent_vertices=0,
                  point_vertices=0, original_edges=0, endpoint_pairs=0,
                  route_edge_occurrences=0, full_support_checks=0,
                  common_face_checks=0, rank_checks=0)
    cases = []; chain = hashlib.sha256(); saved = []
    for e in (Q(1,4), Q(1,3), Q(1,2**40)):
        for d in range(5):
            words = list(product((False,True), repeat=d))
            V = {word:point(e,word) for word in words}; H=rows(e,d)
            assert len(set(V.values())) == 2**d
            assert all(dot(a,x) <= b for x in V.values() for a,b in H)
            active = {w:{i for i,(a,b) in enumerate(H) if dot(a,V[w]) == b} for w in words}
            if d <= 3:
                found = set()
                if d == 0: found.add(())
                for J in combinations(range(len(H)),d) if d else []:
                    counts['active_bases'] += 1
                    M=sp.Matrix([H[j][0] for j in J])
                    if M.det()==0: continue
                    x=tuple(Q(z) for z in M.inv()*sp.Matrix([H[j][1] for j in J]))
                    if all(dot(a,x)<=b for a,b in H):found.add(x)
                assert found == set(V.values())
                counts['independent_vertices'] += len(found)
            graph={w:set() for w in words}
            for a,b in combinations(words,2):
                J=sorted(active[a]&active[b]);rank=sp.Matrix([H[j][0] for j in J]).rank() if J else 0
                counts['rank_checks'] += 1
                isedge=rank==d-1
                if isedge:
                    graph[a].add(b);graph[b].add(a)
                    f=tuple(sum((H[j][0][k] for j in J),Q(0)) for k in range(d))
                    cap=sum((H[j][1] for j in J),Q(0))
                    top={w for w in words if dot(f,V[w])==cap}
                    assert top=={a,b}
                    assert all(dot(f,x)<=cap for x in V.values())
                    counts['full_support_checks'] += len(V)
            edges=sum(map(len,graph.values()))//2
            counts['original_edges'] += edges
            for a in words:
                dist={a:0};queue=deque([a])
                while queue:
                    x=queue.popleft()
                    for y in graph[x]:
                        if y not in dist:dist[y]=dist[x]+1;queue.append(y)
                assert len(dist)==len(V)
                for b in words:
                    path=route(a,b)
                    assert path[0]==a and path[-1]==b and len(path)-1==dist[b]<=d
                    assert all(y in graph[x] for x,y in zip(path,path[1:]))
                    common=active[a]&active[b]
                    for w in path:
                        assert common<=active[w];counts['common_face_checks'] += 1
                    counts['endpoint_pairs'] += 1
                    counts['route_edge_occurrences'] += len(path)-1
                    chain.update(json.dumps([[str(z) for z in V[w]] for w in path],separators=(',',':')).encode())
            counts['models'] += 1;counts['point_vertices'] += len(V)
            cases.append(dict(epsilon=str(e),dimension=d,vertices=len(V),edges=edges,
                              all_ordered_pairs=len(V)**2,full_active_basis_inventory=d<=3))
    # The route needs real edges, not arbitrary segments between extreme points.
    e=Q(1,4);d=2;H=rows(e,d);x=point(e,(False,False));y=point(e,(True,True))
    I=[a for a,b in H if dot(a,x)==b==dot(a,y)]
    rank=sp.Matrix(I).rank() if I else 0
    assert rank<d-1
    # Upper parameter boundary merges branch choices and invalidates the proof's
    # strict vertical-gap argument; this does not assert the route theorem is false there.
    boundary=point(Q(1,2),(False,True))==point(Q(1,2),(True,True))
    assert boundary
    return dict(status='PASS',counts=counts,cases=cases,route_chain_sha256=chain.hexdigest(),
        negative_controls=[{'kind':'two_bit_diagonal_not_edge','dimension':2,'common_active_rank':rank},
          {'kind':'boundary_branch_collision','epsilon':'1/2','equal_points':boundary}],
        scope='Exact finite original-H and whole-support checks. BFS shortestness is tested but not asserted in the public Lean target. No all-real proof by sampling.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    report=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
