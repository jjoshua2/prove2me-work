#!/usr/bin/env python3
"""Actual ordinary-edge routes for many monotone cuts of a feedback box.

Input B>=0,b>0, weights w>0 with Bw<w, cuts>=0, bounds>=0, and actual
rational clipped vertices start,target. Only the two minimal P-faces containing
the endpoints are enumerated. Their dimensions equal the active restricted
cut ranks and are at most rank(cuts), even with arbitrarily many cuts.

Exact geometry/route checking, not Lean proof-term generation. Local basis
search is explicitly capped. No global vertex enumeration is used by route().
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
from hirsch_exact_geometry import *


def model(data: dict[str, Any]) -> dict[str, Any]:
    B, b, cuts, bounds = matrix(data['B']), vector(data['b']), matrix(data['cuts']), vector(data['bounds'])
    d = len(b)
    require(d > 0 and len(B) == d and all(len(row) == d for row in B), 'B/b shape')
    require(len(cuts) == len(bounds) and all(len(row) == d for row in cuts), 'Cut shape')
    require(all(x >= 0 for row in B for x in row) and all(x > 0 for x in b), 'Feedback signs')
    require(all(x >= 0 for row in cuts for x in row) and all(x >= 0 for x in bounds), 'Cuts must be monotone')
    w = vector(data['weights'])
    require(len(w) == d and all(x > 0 for x in w), 'Positive supersolution needed')
    require(all(dot(row, w) < value for row, value in zip(B, w)), 'Feedback is not strictly contractive')
    base = [[-x for x in row] for row in eye(d)]+[[Q(i == j)-B[i][j] for j in range(d)] for i in range(d)]
    return {'B': B, 'b': b, 'w': w, 'cuts': cuts, 'bounds': bounds,
            'd': d, 'q': len(cuts), 'cut_rank': rank(cuts),
            'A': base+cuts, 'rhs': [Q(0)]*d+b+bounds}


def policy_vertex(B: Matrix, b: Vector, upper: list[int]) -> Vector:
    d = len(b); S = set(upper)
    a = [[Q(i == j)-(B[i][j] if i in S else Q(0)) for j in range(d)] for i in range(d)]
    return solve(a, [b[i] if i in S else Q(0) for i in range(d)])


def face_geometry(m: dict[str, Any], x: Vector, supplied: dict[str, Any] | None = None) -> dict[str, Any]:
    B, b, d = m['B'], m['b'], m['d']
    active = verify_vertex(m['A'], m['rhs'], x)
    lower = [i for i in range(d) if i in active]
    upper = [i for i in range(d) if d+i in active]
    require(not set(lower)&set(upper), 'Opposite box rows both active')
    free = [i for i in range(d) if i not in lower and i not in upper]; h = len(free)
    if upper:
        M = [[Q(i == j)-B[i][j] for j in upper] for i in upper]
        if supplied is None:
            R = inverse(M)
        else:
            R = matrix(supplied['upper_inverse'])
            require(len(R) == len(upper) and all(len(row) == len(upper) for row in R), 'Schur inverse shape')
            require(matmul(M,R) == eye(len(upper)) and matmul(R,M) == eye(len(upper)), 'False Schur inverse')
        require(all(v >= 0 for row in R for v in row), 'Principal inverse must be nonnegative')
    else:
        R=[]
        if supplied is not None: require(supplied['upper_inverse'] == [], 'Wrong empty inverse')
    origin = [Q(0)]*d
    E = [[Q(0)]*h for _ in range(d)]
    for j, i in enumerate(free): E[i][j]=Q(1)
    for k, i in enumerate(upper):
        origin[i]=dot(R[k], [b[j] for j in upper])
        E[i]=[dot(R[k], [B[j][f] for j in upper]) for f in free]
    childB = [[B[i][j]+sum((B[i][u]*E[u][k] for u in upper), Q(0))
               for k,j in enumerate(free)] for i in free]
    childb = [b[i]+dot(B[i],origin) for i in free]
    childcuts = [[sum((row[i]*E[i][k] for i in range(d)),Q(0)) for k in range(h)] for row in m['cuts']]
    childbounds = [rhs-dot(row,origin) for row,rhs in zip(m['cuts'],m['bounds'])]
    childA = [[-x for x in row] for row in eye(h)]+[[Q(i==j)-childB[i][j] for j in range(h)] for i in range(h)]+childcuts
    childrhs = [Q(0)]*h+childb+childbounds
    require(all(v >= 0 for row in E for v in row), 'Face chart is not order preserving')
    require(all(dot(row,origin) <= rhs for row,rhs in zip(m['A'],m['rhs'])), 'Minimal face anchor not feasible')
    cutids = [j for j in range(m['q']) if 2*d+j in active]
    restricted_rank = rank([childcuts[j] for j in cutids])
    require(restricted_rank == h and h <= m['cut_rank'], 'Active cut rank does not span the free face')
    require(all(v >= 0 for v in childbounds), 'Negative cut bound at the anchor')
    if h:
        wf=[m['w'][i] for i in free]
        require(all(v>0 for v in childb) and all(v>=0 for row in childB for v in row), 'Reduced feedback signs')
        require(all(dot(row,wf)<wf[i] for i,row in enumerate(childB)), 'Lost Schur contraction')
    cert={'lower':lower,'upper':upper,'free':free,'upper_inverse':R,'origin':origin,'linear':E,
          'child_B':childB,'child_b':childb,'child_cuts':childcuts,'child_bounds':childbounds,
          'active_cut_indices':cutids,'active_restricted_cut_rank':restricted_rank}
    if supplied is not None:
        require(supplied==cert, 'Face certificate identities do not match original rows')
    return {'certificate':cert,'A':childA,'rhs':childrhs,'dimension':h}


def anchor_budget(h: int, q: int) -> int:
    if h == 0: return 0
    if h == 1: return 1
    if h == 2: return (q+4)//2  # A polygon graph is a cycle.
    return (2*h+q)*2**max(h-3,0)


def lift(chart: dict[str,Any], y: Vector) -> Vector:
    return [o+dot(row,y) for o,row in zip(chart['origin'],chart['linear'])]


def anchor_route(m: dict[str,Any], x: Vector, max_bases: int) -> dict[str,Any]:
    f=face_geometry(m,x); c=f['certificate']; h=f['dimension']
    if h==0:
        path=[x]
        require(x==c['origin'],'Zero-dimensional face mismatch')
        count=1
    else:
        vv=vertices(f['A'],f['rhs'],max_bases=max_bases); adj=graph(f['A'],vv)
        local=shortest_path(adj,tuple(x[i] for i in c['free']),tuple(Q(0) for _ in range(h)))
        path=[lift(c,list(y)) for y in local]; count=len(vv)
    require(len(path)-1<=anchor_budget(h,m['q']),'Local route exceeds proved Larman/interval budget')
    return {'face':c,'vertices':path,'local_vertices_enumerated':count,
            'theoretical_anchor_budget':anchor_budget(h,m['q'])}


def route(data: dict[str,Any], *, max_local_bases: int=200000) -> dict[str,Any]:
    m=model(data); start,target=vector(data['start']),vector(data['target'])
    require(len(start)==len(target)==m['d'],'Endpoint dimension mismatch')
    left,right=anchor_route(m,start,max_local_bases),anchor_route(m,target,max_local_bases)
    S=set(left['face']['upper']); T=set(right['face']['upper']); current=set(S)
    points=[policy_vertex(m['B'],m['b'],sorted(current))]; signatures=[sorted(current)]
    for i in sorted(S-T):
        current.remove(i); points.append(policy_vertex(m['B'],m['b'],sorted(current))); signatures.append(sorted(current))
    for i in sorted(T-S):
        current.add(i); points.append(policy_vertex(m['B'],m['b'],sorted(current))); signatures.append(sorted(current))
    allpoints=left['vertices']+points[1:]+list(reversed(right['vertices']))[1:]
    cert={'left':left,'right':right,'middle_signatures':signatures,'middle_vertices':points,'vertices':allpoints}
    return {'certificate':cert,'verified':verify_route(data,cert)}


def verify_route(data: dict[str,Any], cert: dict[str,Any]) -> dict[str,Any]:
    """Recheck geometry and each ORIGINAL-Q edge; do not call enumeration/router."""
    m=model(data); start,target=vector(data['start']),vector(data['target'])
    faces=[]; anchor_lengths=[]
    for key,x in [('left',start),('right',target)]:
        section=cert[key]
        supplied=section['face']
        # Normalize rational strings independently of discovery.
        normalized={k: matrix(v) if k in ('upper_inverse','linear','child_B','child_cuts') else
                    vector(v) if k in ('origin','child_b','child_bounds') else v for k,v in supplied.items()}
        f=face_geometry(m,x,normalized); c=f['certificate']; faces.append(c)
        points=[vector(v) for v in section['vertices']]
        require(bool(points) and points[0]==x and points[-1]==c['origin'],'Wrong anchor endpoints')
        for p in points:
            require(p==lift(c,[p[i] for i in c['free']]),'Anchor walk leaves the same parent face')
            verify_vertex(m['A'],m['rhs'],p)
        for p,q in zip(points,points[1:]): verify_edge(m['A'],m['rhs'],p,q)
        budget=anchor_budget(f['dimension'],m['q'])
        require(len(points)-1<=budget and section['theoretical_anchor_budget']==budget,'Bad anchor budget')
        anchor_lengths.append(len(points)-1)
    signatures=cert['middle_signatures']; middle=[vector(x) for x in cert['middle_vertices']]
    S,T=set(faces[0]['upper']),set(faces[1]['upper'])
    require(bool(signatures) and len(signatures)==len(middle),'Middle shape')
    require(set(signatures[0])==S and set(signatures[-1])==T,'Middle signature endpoints')
    for sig,p in zip(signatures,middle):
        require(isinstance(sig,list) and len(sig)==len(set(sig)) and all(type(i)is int and 0<=i<m['d'] for i in sig),'Bad signature')
        active=verify_vertex(m['A'],m['rhs'],p)
        require(all(m['d']+i in active if i in sig else i in active for i in range(m['d'])),'Wrong middle vertex signature')
    for a,b,p,q in zip(signatures,signatures[1:],middle,middle[1:]):
        require(len(set(a)^set(b))==1,'Middle step is not a single label change')
        verify_edge(m['A'],m['rhs'],p,q)
    require(len(middle)-1==len(S^T),'Middle length does not equal anchor Hamming distance')
    points=[vector(x) for x in cert['vertices']]
    expected=[vector(x) for x in cert['left']['vertices']]+middle[1:]+[vector(x) for x in reversed(cert['right']['vertices'])][1:]
    require(points==expected and points[0]==start and points[-1]==target,'Bad three-part assembly')
    for p,q in zip(points,points[1:]): verify_edge(m['A'],m['rhs'],p,q)
    h1,h2=len(faces[0]['free']),len(faces[1]['free'])
    pair_budget=anchor_budget(h1,m['q'])+len(S^T)+anchor_budget(h2,m['q'])
    s=m['cut_rank']
    uniform=m['d']+2*anchor_budget(s,m['q'])
    require(len(points)-1<=pair_budget<=uniform,'Final bound failed')
    return {'ordinary_edges':len(points)-1,'dimension':m['d'],'cuts':m['q'],'global_cut_rank':s,
            'endpoint_face_dimensions':[h1,h2],'anchor_edges':anchor_lengths,'middle_edges':len(S^T),
            'pair_budget':pair_budget,'uniform_rank_budget':uniform,
            'global_vertices_enumerated':0,
            'scope':'Actual rational edge certificate, not a Lean/platform verdict; routes need not be shortest.'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path);parser.add_argument('--output',type=Path)
    parser.add_argument('--max-local-bases',type=int,default=200000)
    args=parser.parse_args()
    try:
        result=route(json.loads(args.input.read_text()),max_local_bases=args.max_local_bases)
        text=json.dumps(jsonable(result),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:
        parser.exit(2,f'Not certified: {exc}\n')


if __name__=='__main__':main()
