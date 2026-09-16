#!/usr/bin/env python3
"""Finite semantic checks for the standalone Lean construction, not Lean verification."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product, combinations
from collections import deque
from pathlib import Path
import hashlib, json, random

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT/'research/publication_packets/coordinate_extreme_routes'


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def admissible_faces(points):
    todo = [frozenset(range(len(points)))]; faces = set(todo)
    for F in todo:
        for j in range(len(points[0])):
            for value in (min(points[x][j] for x in F), max(points[x][j] for x in F)):
                T = frozenset(x for x in F if points[x][j] == value)
                if T not in faces:
                    faces.add(T); todo.append(T)
    return faces


def validate(points, graph, faces):
    require(len(set(points)) == len(points), 'coordinates fail to separate vertices')
    require(all(x in graph[y] for x in graph for y in graph[x]), 'asymmetric relation')
    require(frozenset(range(len(points))) in faces, 'root face absent')
    moves = 0
    for F in faces:
        for j in range(len(points[0])):
            low, high = min(points[x][j] for x in F), max(points[x][j] for x in F)
            for value in (low, high):
                require(frozenset(x for x in F if points[x][j] == value) in faces,
                        'coordinate-extreme face closure fails')
            for x in F:
                if points[x][j] > low:
                    require(any(y in F and points[y][j] < points[x][j] for y in graph[x]),
                            'no improving downward neighbor')
                    moves += 1
                if points[x][j] < high:
                    require(any(y in F and points[x][j] < points[y][j] for y in graph[x]),
                            'no improving upward neighbor')
                    moves += 1
    return moves


def ranked_route(points, graph, F, u, v, coords, rank, width, stats):
    if not coords:
        require(u == v, 'fixed coordinates did not identify the endpoint')
        return [u]
    j, *rest = coords
    sign = -1 if rank[j][points[u][j]] + rank[j][points[v][j]] <= width[j] else 1
    goal = (min if sign < 0 else max)(points[x][j] for x in F)
    def descend(start):
        path = [start]
        while points[path[-1]][j] != goal:
            x = path[-1]
            candidates = [y for y in graph[x] if y in F and sign*(points[y][j]-points[x][j]) > 0]
            require(bool(candidates), 'local hypothesis failed')
            path.append(min(candidates))
        charge = abs(rank[j][points[start][j]] - rank[j][goal])
        require(len(path)-1 <= charge, 'integer-rank descent failed')
        return path, charge
    p, a = descend(u); q, b = descend(v)
    require(a+b <= width[j], 'joint rank cost exceeded coordinate width')
    stats['phases'] += 1; stats['charged_ranks'] += a+b
    T = frozenset(x for x in F if points[x][j] == goal)
    mid = ranked_route(points, graph, T, p[-1], q[-1], rest, rank, width, stats)
    return p[:-1] + mid + list(reversed(q[:-1]))


def affine(points, seed):
    rng = random.Random(seed); d=len(points[0])
    # Integer elementary row additions give an invertible dense chart.
    M = [[Q(i==j) for j in range(d)] for i in range(d)]
    if d > 1:
        for _ in range(4*d):
            i,j = rng.sample(range(d),2); c=Q(rng.choice([-2,-1,1,2]))
            M[i] = [a+c*b for a,b in zip(M[i],M[j])]
    shift=[Q(rng.randrange(-8,9),7) for _ in range(d)]
    return [tuple(sum(a*b for a,b in zip(row,x))+t for row,t in zip(M,shift)) for x in points]


def models():
    # Explicit graph families. The test's local hypotheses are checked afresh,
    # rather than inferred from the geometric name.
    out=[]
    for d in range(1,5):
        for maxlevel in ([1,2] if d<4 else [1]):
            values=[Q(i*i+2*i, 7) for i in range(maxlevel+1)]
            points=list(product(values,repeat=d)); index={x:i for i,x in enumerate(points)}
            graph={i:set() for i in range(len(points))}
            for i,x in enumerate(points):
                for j in range(d):
                    k=values.index(x[j])
                    for nk in [k-1,k+1]:
                        if 0<=nk<len(values):
                            y=list(x);y[j]=values[nk];graph[i].add(index[tuple(y)])
            out.append((f'grid_{d}_{maxlevel}',points,graph))
            if maxlevel==1:
                out.append((f'affine_cube_{d}',affine(points,89+d),graph))
    for n in range(3,10):
        pts=[(Q(i),Q(i*i)) for i in range(n)]
        graph={i:{(i-1)%n,(i+1)%n} for i in range(n)}
        out.append((f'polygon_{n}',pts,graph))
        out.append((f'affine_polygon_{n}',affine(pts,n),graph))
    for d in range(2,5):
        pts=[tuple(Q(0) for _ in range(d))]+[tuple(Q(i==j) for i in range(d)) for j in range(d)]
        graph={i:set(range(len(pts)))-{i} for i in range(len(pts))}
        out.append((f'simplex_{d}',affine(pts,d+101),graph))
        pts=[tuple(Q(s*(i==j)) for i in range(d)) for j in range(d) for s in (-1,1)]
        graph={i:{j for j,y in enumerate(pts) if j!=i and any(a+b for a,b in zip(pts[i],y))} for i in range(len(pts))}
        out.append((f'crosspolytope_{d}',affine(pts,d+103),graph))
    out.append(('zero_dimension',[()],{0:set()}))
    return out


def bfs(graph, start, allowed):
    D={start:0};q=deque([start])
    while q:
        x=q.popleft()
        for y in graph[x]:
            if y in allowed and y not in D:
                D[y]=D[x]+1;q.append(y)
    return D


def main():
    totals=dict(models=0,admissible_faces=0,local_moves_checked=0,routes=0,
                edges=0,shortest_edges=0,nonshortest_routes=0,phases=0,charged_ranks=0)
    records=[]
    for name,points,graph in models():
        faces=admissible_faces(points); moves=validate(points,graph,faces)
        d=len(points[0]); levels=[sorted({x[j] for x in points}) for j in range(d)]
        rank=[{v:i for i,v in enumerate(L)} for L in levels]; width=[len(L)-1 for L in levels]
        F=frozenset(range(len(points)))
        cases=[(F,u,v) for u in F for v in F]
        # Also test nontrivial initial faces and zero-route membership.
        cases += [(T,min(T),max(T)) for T in sorted(faces,key=lambda T:(len(T),sorted(T))) if T!=F]
        stats={'phases':0,'charged_ranks':0}; edges=best=nonshort=0
        for T,u,v in cases:
            fixed=[j for j in range(d) if len({points[x][j] for x in T})==1]
            free=[j for j in range(d) if j not in fixed]
            path=ranked_route(points,graph,T,u,v,free,rank,width,stats)
            require(path[0]==u and path[-1]==v and all(x in T for x in path), 'wrong face or endpoints')
            require(all(y in graph[x] for x,y in zip(path,path[1:])), 'not a graph walk')
            require(len(path)-1<=sum(width[j] for j in free), 'sum-width bound failed')
            dist=bfs(graph,u,T)[v];L=len(path)-1
            edges+=L;best+=dist;nonshort+=L>dist
        record={'name':name,'vertices':len(points),'faces':len(faces),'local_moves':moves,
                'routes':len(cases),'edges':edges,'shortest_edges':best,'nonshortest':nonshort,
                'coordinate_levels':list(map(len,levels)),'global_bound':sum(width)}
        records.append(record)
        totals['models']+=1;totals['admissible_faces']+=len(faces);totals['local_moves_checked']+=moves
        totals['routes']+=len(cases);totals['edges']+=edges;totals['shortest_edges']+=best
        totals['nonshortest_routes']+=nonshort
        for k in stats:totals[k]+=stats[k]
    countermodels=[]
    def rejects(name, points, graph, faces):
        try:validate(points,graph,faces)
        except ValueError:countermodels.append(name)
        else:raise AssertionError(f'failed countermodel {name}')
    rejects('no_local_improvement',[(Q(0),),(Q(1),)],{0:set(),1:set()},
            {frozenset([0,1]),frozenset([0]),frozenset([1])})
    rejects('noninjective_coordinates',[(Q(0),),(Q(0),)],{0:set(),1:set()},
            {frozenset([0,1])})
    rejects('asymmetric_edges',[(Q(0),),(Q(1),)],{0:{1},1:set()},
            {frozenset([0,1]),frozenset([0]),frozenset([1])})
    rejects('missing_extreme_face',[(Q(0),),(Q(1),)],{0:{1},1:{0}},
            {frozenset([0,1])})
    source=(PACKET/'solution.lean').read_text()
    start=source.index('theorem solution\n');end=source.index(' := by',start)
    theorem=source[start:end].replace('theorem solution','theorem Hirsch.finite_coordinate_extreme_route_bound',1)
    target=json.loads((PACKET/'problem.json').read_text())
    require(target['formal_statement']==theorem+' := by sorry\n','target/solution signature drift')
    require(target['preamble']=='import Mathlib\nopen scoped BigOperators\nset_option autoImplicit false','nonminimal target preamble')
    import re
    require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source),'forbidden source token')
    out={'status':'PASS','scope':'Finite semantic/signature regression, NOT Lean compilation or verification.',
         'totals':totals,'records':records,'assumption_countermodels':countermodels,
         'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
         'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'public_type_exactly_matches_solution':True}
    (ROOT/'research/COORDINATE_EXTREME_ROUTE_CHECK.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(totals,indent=2))
    print('countermodels',countermodels)

if __name__=='__main__':main()
