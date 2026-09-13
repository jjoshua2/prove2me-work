#!/usr/bin/env python3
"""Finite fork certificates for overlapping coherent gain cycles.

An opposite-sign gain graph is accepted exactly when every NONDIRECTED simple
cycle has gain one. The certificate does not list simple cycles: for every two
arcs entering or leaving the same vertex, it certifies the balanced corridor
between their other endpoints after that vertex is removed. A corridor's outside
components attach at most once, so no simple path can leave and return.

The global path/cycle transport bound and positive-cone proof yield the stated
classical diameter consequence, not a runtime bound for the reused shadow search.
All route witnesses are checked against the unchanged original inequalities.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib, json
from gain_lattice_certificate import parse_rows, rat, dot, serial, require, gain_inverse, gain_kernel
from coherent_gain_cones import (edges, forest_data, forest_scale, DSU,
    certify_structure as certify_basis_structure, cone_witness as isolated_basis_center)


def matrix_hash(A):
    return hashlib.sha256(json.dumps(serial(A),separators=(',',':')).encode()).hexdigest()


def adjacency(d,E,removed=None):
    G=[[] for _ in range(d)]
    for r,(u,v,g) in E.items():
        if u==removed or v==removed:continue
        G[u].append((v,r,g));G[v].append((u,r,1/g))
    return G


def forks(d,E):
    incoming=[[] for _ in range(d)];outgoing=[[] for _ in range(d)]
    for r,(u,v,g) in E.items():
        outgoing[u].append((r,v,g));incoming[v].append((r,u,1/g))
    for v in range(d):
        for group in (incoming[v],outgoing[v]):
            for a,b in combinations(sorted(group),2):
                yield v,a,b


def reachable(G,start,allowed=None):
    seen={start};todo=[start]
    while todo:
        u=todo.pop()
        for v,_,_ in G[u]:
            if v not in seen and (allowed is None or v in allowed):seen.add(v);todo.append(v)
    return seen


def corridor(G,s,t):
    """Union of blocks on the block-cut path, using edge-ID aware Tarjan DFS.
    A parallel-edge block is retained; a zero-length corridor is a singleton.
    This routine is discovery only. Its output has a separate separator verifier.
    """
    if s==t:return {s}
    n=len(G);tin=[-1]*n;low=[-1]*n;stack=[];blocks=[];clock=0
    def visit(u,parent_edge=None):
        nonlocal clock
        tin[u]=low[u]=clock;clock+=1
        for v,r,_ in G[u]:
            if r==parent_edge:continue
            if tin[v]<0:
                stack.append((r,u,v));visit(v,r);low[u]=min(low[u],low[v])
                if low[v]>=tin[u]:
                    vertices=set()
                    while True:
                        k,a,b=stack.pop();vertices.update((a,b))
                        if k==r:break
                    blocks.append(vertices)
            elif tin[v]<tin[u]:
                stack.append((r,u,v));low[u]=min(low[u],tin[v])
    visit(s)
    if tin[t]<0:return set()
    tree=[[] for _ in range(n+len(blocks))]
    for k,block in enumerate(blocks,n):
        for u in block:tree[u].append(k);tree[k].append(u)
    parent={s:None};todo=deque([s])
    while todo and t not in parent:
        u=todo.popleft()
        for v in tree[u]:
            if v not in parent:parent[v]=u;todo.append(v)
    require(t in parent,'block corridor discovery failed')
    out={s,t};u=t
    while u is not None:
        if u>=n:out.update(blocks[u-n])
        u=parent[u]
    return out


def balanced_potentials(G,H,root):
    p={root:Q(1)};todo=[root]
    while todo:
        u=todo.pop()
        for v,_,g in G[u]:
            if v not in H:continue
            value=p[u]*g
            if v not in p:p[v]=value;todo.append(v)
            else:require(p[v]==value,'unbalanced cycle in a fork corridor')
    require(set(p)==H,'disconnected corridor')
    return p


def certify_forks(d,E):
    removed_graphs={};out=[]
    for v,(r,s,gs),(t,u,gu) in forks(d,E):
        if v not in removed_graphs:removed_graphs[v]=adjacency(d,E,v)
        G=removed_graphs[v];H=corridor(G,s,u)
        if H:
            p=balanced_potentials(G,H,s)
            require(gs*p[u]==gu*p[s],'fork endpoint gains do not cancel')
        else:p={}
        nodes=sorted(H)
        out.append({'vertex':v,'rows':[r,t],'corridor':nodes,'potentials':[p[x] for x in nodes]})
    return out


def verify_forks(d,E,certificates):
    """No Tarjan, no simple-cycle search, and no potential discovery.
    Connectivity/separators and every original induced gain equation are checked.
    """
    require(isinstance(certificates,list),'fork certificates must be a list')
    expected=list(forks(d,E));require(len(certificates)==len(expected),'missing fork occurrence')
    graphs={};sizes=[];detached=0
    for (v,(r,s,gs),(t,u,gu)),c in zip(expected,certificates):
        require(type(c['vertex']) is int and c['vertex']==v and c['rows']==[r,t]
                and all(type(i)is int for i in c['rows']),'changed fork identity/order')
        ns=c['corridor'];raw=c['potentials']
        require(isinstance(ns,list) and len(ns)==len(set(ns)) and all(type(x)is int and 0<=x<d and x!=v for x in ns),'invalid corridor nodes')
        require(len(raw)==len(ns),'corridor potential shape')
        if v not in graphs:graphs[v]=adjacency(d,E,v)
        G=graphs[v];H=set(ns)
        if not H:
            require(u not in reachable(G,s),'false disconnected-fork certificate');detached+=1;continue
        require(s in H and u in H and reachable(G,s,H)==H,'corridor missing or disconnecting endpoints')
        p=dict(zip(ns,map(rat,raw)));require(all(x>0 for x in p.values()),'nonpositive corridor potential')
        for a in H:
            for b,_,g in G[a]:
                if b in H:require(p[b]==g*p[a],'false balanced-corridor row identity')
        require(gs*p[u]==gu*p[s],'uncancelled fork cycle')
        unseen=set(range(d))-H-{v}
        while unseen:
            root=next(iter(unseen));component=reachable(G,root,unseen)
            attached={b for a in component for b,_,_ in G[a] if b in H}
            require(len(attached)<=1,'outside component attaches twice; hidden path not covered')
            unseen-=component
        sizes.append(len(H))
    return {'forks':len(expected),'disconnected_forks':detached,'balanced_corridors':len(sizes),
            'corridor_vertex_occurrences':sum(sizes)}


def normalize_rows(A,s):
    out=[];row_scale=[]
    for a in A:
        b=tuple(x*y for x,y in zip(a,s));m=max(map(abs,b),default=Q(0)) or Q(1)
        out.append(tuple(x/m for x in b));row_scale.append(m)
    return out,row_scale


def certify_structure(Araw):
    A=parse_rows(Araw);d=len(A[0]);E,F,_,_=forest_data(A);s=forest_scale(d,E,F)
    N,_=normalize_rows(A,s);EN=edges(N)
    factors=sorted((max(g,1/g) for _,_,g in EN.values()),reverse=True)
    gamma=Q(1)
    for x in factors[:d]:gamma*=x
    c={'matrix_sha256':matrix_hash(A),'forest_rows':F,'diagonal':s,
       'forks':certify_forks(d,EN),'transport_bound':gamma}
    c=serial(c);return {'certificate':c,'verified':verify_structure(Araw,c)}


def verify_structure(Araw,c):
    A=parse_rows(Araw);d=len(A[0]);E=edges(A);s=list(map(rat,c['diagonal']))
    require(c['matrix_sha256']==matrix_hash(A),'matrix identity mismatch')
    require(len(s)==d and all(x>0 for x in s),'invalid global diagonal')
    F=c['forest_rows'];require(isinstance(F,list) and len(F)==len(set(F)) and all(type(r)is int and r in E for r in F),'invalid forest IDs')
    uf=DSU(d)
    for r in F:
        u,v,g=E[r];require(uf.join(u,v),'cyclic forest');require(g*s[u]==s[v],'forest gain identity failed')
    require(all(uf.find(u)==uf.find(v) for u,v,_ in E.values()),'forest does not span')
    N,_=normalize_rows(A,s);EN=edges(N);stats=verify_forks(d,EN,c['forks'])
    gamma=Q(1)
    for x in sorted((max(g,1/g) for _,_,g in EN.values()),reverse=True)[:d]:gamma*=x
    require(rat(c['transport_bound'])==gamma,'false path/cycle transport bound')
    return {'status':'PASS','dimension':d,'original_rows':len(A),'binary_rays':len(E),**stats,
            'transport_bound':str(gamma),'normal_width_squared':str(1/(4*gamma**4*d**3)),
            'full_row_rank':gain_kernel(A,d)['rank'],
            'classical_safe_diameter':256*d**3 if gamma<=2 and gain_kernel(A,d)['rank']==d else None,
            'scope':'Finite fork certificate for all nondirected cycles, not a Lean verdict or a bound on the deterministic sampler.'}


def basis_center(Araw,basis,gamma):
    """Reuse the old construction ONLY on a single basis, whose components
    are trees or unicyclic. The ambient graph may have arbitrary cycle overlap.
    The basis gauge is transported back before a global-metric width is claimed.
    """
    A=parse_rows(Araw);d=len(A[0]);gamma=rat(gamma)
    require(len(basis)==d and len(set(basis))==d and all(type(i)is int and 0<=i<len(A) for i in basis),'bad basis')
    B=[A[i] for i in basis];sc=certify_basis_structure(B)['certificate']
    diagonal=list(map(rat,sc['diagonal']));uf=DSU(d)
    for u,v,_ in edges(B).values():uf.join(u,v)
    components={}
    for i in range(d):components.setdefault(uf.find(i),[]).append(i)
    for ns in components.values():
        lo=min(diagonal[i] for i in ns)
        for i in ns:diagonal[i]/=lo
    require(max(diagonal)/min(diagonal)<=gamma,'basis gauge exceeds inherited transport')
    sc['diagonal']=serial(diagonal)
    local=isolated_basis_center(B,sc,list(range(d)))
    center=tuple(rat(x)/t for x,t in zip(local['center'],diagonal))
    c=serial({'basis':list(basis),'center':center,'width_squared':1/(4*gamma**4*d**3)})
    verify_cone(Araw,c,gamma)
    return c


def verify_cone(Araw,c,gamma):
    A=parse_rows(Araw);d=len(A[0]);B=c['basis'];gamma=rat(gamma)
    require(gamma>=1 and len(B)==d and len(set(B))==d and all(type(i)is int and 0<=i<len(A) for i in B),'invalid cone basis')
    inv,_=gain_inverse([A[i] for i in B]);center=tuple(map(rat,c['center']))
    require(len(center)==d and dot(center,center)>0,'zero/wrong cone center')
    width=rat(c['width_squared']);require(width==1/(4*gamma**4*d**3),'false cone width')
    margins=[]
    for j in range(d):
        u=tuple(inv[i][j] for i in range(d));m=dot(u,center)
        require(m>0 and m*m>=width*dot(u,u)*dot(center,center),'positive cone ball inequality failed')
        margins.append(m*m/(dot(u,u)*dot(center,center)))
    return {'minimum_squared_margin':str(min(margins)),
            'maximum_inverse_entry':str(max(abs(x) for row in inv for x in row))}


def normalized_problem(data,structure):
    A=parse_rows(data['A']);s=list(map(rat,structure['diagonal']));N,m=normalize_rows(A,s)
    b=list(map(rat,data['b']));require(len(b)==len(A),'RHS count mismatch')
    start=list(map(rat,data['start']));end=list(map(rat,data['end']))
    require(len(start)==len(s)==len(end),'endpoint shape')
    return {'A':N,'b':[x/y for x,y in zip(b,m)],
            'start':[x/y for x,y in zip(start,s)],'end':[x/y for x,y in zip(end,s)]}


def construct_route(data):
    from gain_shadow_extension import construct,GainModel
    require('gain_base' not in data,'this criterion requires no common gain base')
    structure=certify_structure(data['A'])['certificate'];gamma=rat(structure['transport_bound'])
    problem=normalized_problem(data,structure);out=construct(problem);model=GainModel(problem)
    c=out['certificate'];cones=[];face_forks=[]
    if model.h:
        face_forks=certify_forks(model.h,edges(model.A))
        bases={tuple(c['source_basis']),tuple(c['target_basis']),tuple(c['final_basis'])}
        bases|={tuple(step['basis']) for step in c['basis_steps']}
        for B in sorted(bases):cones.append(basis_center(model.A,B,gamma))
    packet=serial({'structure':structure,'face_forks':face_forks,'route_certificate':c,'basis_cones':cones})
    return {'certificate':packet,'verified':verify_route(data,packet)}


def verify_route(data,packet):
    from gain_shadow_extension import verify,GainModel
    parent=verify_structure(data['A'],packet['structure']);gamma=rat(parent['transport_bound'])
    problem=normalized_problem(data,packet['structure']);res=verify(problem,packet['route_certificate'])
    model=GainModel(problem,discover=False);c=packet['route_certificate']
    if model.h:
        stats=verify_forks(model.h,edges(model.A),packet['face_forks'])
        required={tuple(c['source_basis']),tuple(c['target_basis']),tuple(c['final_basis'])}
        required|={tuple(step['basis']) for step in c['basis_steps']};seen=set();largest=Q(0);margin=None
        for w in packet['basis_cones']:
            B=tuple(w['basis']);require(B not in seen,'duplicate cone evidence');seen.add(B)
            v=verify_cone(model.A,w,gamma);largest=max(largest,rat(v['maximum_inverse_entry']))
            z=rat(v['minimum_squared_margin']);margin=z if margin is None else min(margin,z)
        require(seen==required,'missing/extra basis cone')
    else:
        require(not packet['basis_cones'] and not packet['face_forks'],'spurious point certificates')
        stats={'forks':0};largest=Q(0);margin=None
    A=parse_rows(data['A']);b=list(map(rat,data['b']));s=list(map(rat,packet['structure']['diagonal']))
    route=[tuple(rat(x)*t for x,t in zip(p,s)) for p in c['route']]
    require(route[0]==tuple(map(rat,data['start'])) and route[-1]==tuple(map(rat,data['end'])),'original endpoints changed')
    evaluations=0
    for x in route:
        require(all(dot(a,x)<=z for a,z in zip(A,b)),'original feasibility failed');evaluations+=len(A)
    for x,y in zip(route,route[1:]):
        common=[a for a,z in zip(A,b) if dot(a,x)==z==dot(a,y)]
        require(gain_kernel(common,len(s))['rank']==len(s)-1,'original shared rank is not an edge')
    bound=0 if model.h==0 else (256*model.h**3 if gamma<=2 else None)
    return {'status':'PASS','dimension':model.d,'intrinsic_dimension':model.h,'rows':model.m,
            'edges':res['edges'],'basis_pivots':res['pivots'],'stationary_pivots':res['stationary_pivots'],
            'original_feasibility_evaluations':evaluations,'forks':parent['forks'],'face_forks':stats['forks'],
            'transport_bound':str(gamma),'verified_basis_cones':len(packet['basis_cones']),
            'largest_visited_inverse':str(largest),'minimum_squared_cone_margin':None if margin is None else str(margin),
            'classical_safe_diameter':bound,'sample_within_bound':None if bound is None else res['edges']<=bound,
            'original_route':serial(route),'scope':'Exact original-H edges and cone certificates; the deterministic sampler is not the classical expected-length distribution.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path);p.add_argument('--output',type=Path)
    args=p.parse_args()
    try:
        data=json.loads(args.input.read_text());out=verify_route(data,json.loads(args.certificate.read_text())) if args.certificate else construct_route(data)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No certificate: {exc}\n')
if __name__=='__main__':main()
