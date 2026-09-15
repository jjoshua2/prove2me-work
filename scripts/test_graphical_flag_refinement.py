#!/usr/bin/env python3
"""Exact graph-refinement tests, independent literal subdivisions and H graphs.

No classical theorem is claimed new or Lean-verified. Reports preserve graph
search limits, original/final route counts, nonshortest results, and failures
of the sparse certificate class. Reference graphs are test-only data.
"""
from __future__ import annotations
from itertools import combinations, permutations, product
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random, time
import sympy as sp
import graphical_flag_refinement as G

ROOT=Path(__file__).resolve().parents[1]


def subsets(n):return [frozenset(S) for k in range(n+1) for S in combinations(range(n),k)]


def maximal_faces(K):
    faces=[S for S in subsets(K.n) if K.ask(S)]
    return [S for S in faces if not any(S<T for T in faces)]


def maxcliques(adj):
    out=[]
    def go(R,P,X):
        if not P and not X:out.append(frozenset(R));return
        pivot=max(P|X,key=lambda u:len(P&adj[u])) if P|X else None
        for v in sorted(P-(adj[pivot] if pivot is not None else set())):
            go(R|{v},P&adj[v],X&adj[v]);P=P-{v};X=X|{v}
    go(set(),set(adj),set());return out


def literal_refinement(F,R):
    """Independently subdivide every connected original face, largest first.
    No graphical nested-face formula is used by this operation.
    """
    current=list(F);steps=0
    for S in sorted((S for S in R.vertices if len(S)>1),key=lambda s:(-len(s),tuple(sorted(s)))):
        z=R.index[S];nextfaces=[]
        G.require(any(S<=X for X in current),'requested stellar face disappeared')
        for X in current:
            if S<=X:nextfaces.extend((X-{i})|{z} for i in S)
            else:nextfaces.append(X)
        current=G.old.ordered(nextfaces);steps+=1
    return current,steps


def abstract_stage():
    start=time.monotonic();n=4;pool=[S for S in subsets(n) if len(S)>=2];edgepool=list(combinations(range(n),2))
    counts={'complexes':0,'complex_graph_pairs':0,'literal_stellar_steps':0,
            'flag_cases':0,'nonflag_cases':0,'pure_carrier_edges':0,'registry_face_tests':0,
            'search_optimum_crosschecks':0}
    for mask in range(1<<len(pool)):
        H=[S for j,S in enumerate(pool) if mask>>j&1]
        if G.old.ordered(H)!=G.old.minimal(H):continue
        K=G.old.Complex(n,H);F=maximal_faces(K);counts['complexes']+=1
        pure=len(set(map(len,F)))==1;d=len(F[0]);best2=None
        for edge_mask in range(1<<len(edgepool)):
            edges=[list(e) for j,e in enumerate(edgepool) if edge_mask>>j&1]
            R=G.GraphicalRefinement(K,edges);actual,ns=literal_refinement(F,R)
            counts['literal_stellar_steps']+=ns;counts['complex_graph_pairs']+=1
            expected=[]
            for face in F:
                V=[i for i,S in enumerate(R.vertices) if S<=face]
                adj={i:{j for j in V if j!=i and R.compatible(R.vertices[i],R.vertices[j])} for i in V}
                expected.extend(maxcliques(adj))
            expected=G.old.ordered(expected)
            expected=[S for S in expected if not any(S<T for T in expected)]
            G.require(expected==G.old.ordered(actual),'nested formula differs from literal stellar subdivision')
            direct_registry=[S for S in subsets(n) if S and K.ask(S) and len(G.components(R.adj,S))==1]
            G.require(set(direct_registry)==set(R.vertices),'incomplete connected-face registry')
            counts['registry_face_tests']+=len(direct_registry)
            adj={i:{j for j in range(len(R.vertices)) if j!=i and R.ask({i,j})} for i in range(len(R.vertices))}
            cliques=maxcliques(adj);isflag=all(any(C<=X for X in actual) for C in cliques)
            G.require(isflag==(not G.check_criterion(K,R.adj)),'two-component flag equivalence failed')
            counts['flag_cases']+=isflag;counts['nonflag_cases']+=not isflag
            if isflag and max(map(len,R.adj))<=2:
                best2=min(best2,len(R.vertices)) if best2 is not None else len(R.vertices)
            if pure:
                for X,Y in combinations(actual,2):
                    if len(X&Y)==d-1:
                        U=R.carrier(X,d);V=R.carrier(Y,d)
                        G.require(U==V or len(U&V)==d-1,'adjacent carriers not equal/adjacent')
                        counts['pure_carrier_edges']+=1
        _,search=G.search_sparse_graph(K,2,100000)
        G.require(search['status']=='complete' and search['best_refined_vertices']==best2,'graph optimization incomplete/incorrect')
        counts['search_optimum_crosschecks']+=1
    return {'status':'PASS','stage':'abstract',**counts,'seconds':round(time.monotonic()-start,4)},None,[]


def reference(A,b):
    d=len(A[0]);n=len(A);V={};systems=0
    for ids in combinations(range(n),d):
        systems+=1;M=sp.Matrix([A[i] for i in ids])
        if M.det()==0:continue
        x=tuple(Q(str(z)) for z in M.inv()*sp.Matrix([b[i] for i in ids]))
        if G.old.old.basis.feasible(A,b,x):V[x]=frozenset(G.old.old.basis.active_rows(A,b,x))
    G.require(V and all(len(F)==d for F in V.values()),'non-simple reference model')
    for i in range(n):
        X=[x for x,F in V.items() if i in F]
        avg=tuple(sum(x[j] for x in X)/len(X) for j in range(d))
        G.require(G.old.old.basis.active_rows(A,b,avg)==[i],'not a genuine original facet')
        G.require(sp.Matrix([[x[j]-X[0][j] for j in range(d)] for x in X[1:]]).rank()==d-1,'wrong original facet dimension')
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    G.require(all(len(ns)==d for ns in adj.values()),'wrong original graph degree')
    dist={}
    for u in V:
        dd={u:0};q=deque([u])
        while q:
            x=q.popleft()
            for y in adj[x]:
                if y not in dd:dd[y]=dd[x]+1;q.append(y)
        G.require(len(dd)==len(V),'disconnected original graph');dist[u]=dd
    NF=[]
    for size in range(2,d+2):
        for ids in combinations(range(n),size):
            S=frozenset(ids)
            if not any(N<=S for N in NF) and not any(S<=F for F in V.values()):NF.append(S)
    return V,adj,dist,G.old.Complex(n,NF),systems


def simplex(d):return [[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(1)]*d],[Q(0)]*d+[Q(1)]


def cyclic(n):
    pts=[[Q(i)**j for j in range(1,5)] for i in range(n)]
    c=[sum(x[j] for x in pts)/n for j in range(4)]
    return [[x[j]-c[j] for j in range(4)] for x in pts],[Q(1)]*n


def plateau():
    pts=json.loads((ROOT/'fixtures/mixed_absorption_plateau.json').read_text())['points'];d=len(pts[0]);n=len(pts)
    c=[sum(Q(x[j]) for x in pts)/n for j in range(d)]
    return [[Q(x[j])-c[j] for j in range(d)] for x in pts],[Q(1)]*n


def exhaustive_flat_partitions(K):
    """Independent complete set-partition comparison with #260, at n<=10.
    No graph optimizer, beam search, or branch-bound pruning is used. Count
    every partition once in restricted-growth order and check every nonface.
    """
    G.require(K.n<=10,'explicit flat-partition enumeration cap')
    n=K.n;nf=[sum(1<<i for i in N) for N in K.missing]
    face=[not any(mask & N == N for N in nf) for mask in range(1<<n)]
    cost=[0]*(1<<n)
    for mask in range(1,1<<n):
        t=mask
        while t:
            cost[mask]+=face[t];t=(t-1)&mask
    count=valid=0;best=None;witness=None
    def scan(i,blocks):
        nonlocal count,valid,best,witness
        if i<n:
            for j in range(len(blocks)):
                scan(i+1,blocks[:j]+[blocks[j]|(1<<i)]+blocks[j+1:])
            scan(i+1,blocks+[1<<i]);return
        count+=1
        if any(sum(bool(B&N) for B in blocks)>2 for N in nf):return
        valid+=1;v=sum(cost[B] for B in blocks)
        if best is None or v<best:
            best=v;witness=[[j for j in range(n) if B>>j&1] for B in blocks]
    scan(0,[])
    return {'all_partitions_examined':count,'valid_partitions':valid,
            'minimum_flat_refined_vertices':best,'optimal_partition':witness,
            'scope':'Complete enumeration of #260 flat partitions, not all possible refinements.'}


def geometry_stage():
    start=time.monotonic();rows=[];saved=[];fixtures=[]
    models=[('simplex3',*simplex(3),0),('cyclic4_6',*cyclic(6),10),
            ('cyclic4_7',*cyclic(7),12),('cyclic4_8',*cyclic(8),12),
            ('plateau5_10_from_263',*plateau(),12)]
    for name,A,b,cap in models:
        V,adj,dist,K,systems=reference(A,b);d=len(A[0]);m=len(A)
        edges,search=G.search_sparse_graph(K,2,50000)
        G.require(edges is not None,'expected sparse graphical certificate not found')
        R=G.GraphicalRefinement(K,edges);pairs=list(combinations(V,2))
        random.Random(265+m).shuffle(pairs);pairs=pairs[:cap] if cap else pairs
        row={'model':name,'dimension':d,'original_facets':m,'original_vertices':len(V),
             'original_edges':sum(map(len,adj.values()))//2,'independent_square_systems':systems,
             'auxiliary_edges':edges,'graph_search':search,'refined_vertices':len(R.vertices),
             'all_pairs_bound':len(R.vertices)-d,'flat_partition_comparison':exhaustive_flat_partitions(K),'pairs':0,'new_route_edges':0,'raw_258_edges':0,
             'shortest_edges':0,'nonshortest':0,'refined_edges':0,'stationary_steps':0,
             'original_reentries':0,'LP_maximizations':0,'LP_pivots':0}
        for j,(u,v) in enumerate(pairs):
            data={'A':A,'b':b,'start':u,'target':v};out=G.construct(data,edges)
            result=out['verified'];old=G.old.old.construct(data)['verified']
            points={F:x for x,F in V.items()};P=[points[frozenset(F)] for F in out['certificate']['refinement']['original_path']]
            G.require(all(y in adj[x] for x,y in zip(P,P[1:])),'nonedge in independent original reference')
            row['pairs']+=1;row['new_route_edges']+=result['original_edges'];row['raw_258_edges']+=old['original_edges']
            row['shortest_edges']+=dist[u][v];row['nonshortest']+=result['original_edges']>dist[u][v]
            row['refined_edges']+=result['refined_edges'];row['stationary_steps']+=result['stationary_steps']
            row['original_reentries']+=result['original_reentries']
            row['LP_maximizations']+=out['discovery']['LP_maximizations'];row['LP_pivots']+=out['discovery']['internal_LP_pivots']
            if j==0 or (result['original_edges']>dist[u][v] and len(fixtures)<10):
                fixtures.append({'model':name,'input':G.old.old.serial(data),'output':out,
                                 'BFS_distance':dist[u][v],'raw_258_edges':old['original_edges']})
                saved.append((data,out))
        rows.append(row);print('geometry',row,flush=True)
    return {'status':'PASS','stage':'geometry','models':rows,'seconds':round(time.monotonic()-start,4)},fixtures,saved


def obstruction_stage():
    start=time.monotonic();rows=[]
    for n in (9,):
        H=[T for T in combinations(range(n),3) if all((a-b)%n not in (1,n-1) for a,b in combinations(T,2))]
        K=G.old.Complex(n,H);order,out=G.find_order(K,True,100000)
        G.require(order is None and out['status']=='exhausted','cyclic-nine cycle search did not prove exhaustion')
        rows.append({'cyclic_four_vertices':n,'auxiliary_type':'Hamiltonian cycle',**out})
    # Exact all-size algebra is in the note; these are finite arithmetic checks.
    density=[]
    for n in range(11,101):
        need=n*(n-1)//2-(n*n)//4;available=2*n
        G.require(need>available,'density obstruction failed')
        density.append({'n':n,'required_union_edges':need,'maximum_cycle_plus_degree_two_edges':available})
    # Real plateau. The optimal graph found independently has connected faces
    # of size <=2, so its subdivisions are all at original edges and commute.
    A,b=plateau();V,_,_,K,_=reference(A,b);edges,s=G.search_sparse_graph(K,2,10000);R=G.GraphicalRefinement(K,edges)
    G.require(s['optimal_within_degree_limit'] and max(map(len,R.vertices))==2,'expected commuting certificate')
    terminal=None;perms=0;weight_histograms={};increases=0;max_peak=0;strict_orders=0;neutral_steps=0
    for order in permutations(edges):
        J=K;weights=[sum(len(N)-2 for N in J.high())]
        for E in order:
            J=G.old.stellar(J,E);weights.append(sum(len(N)-2 for N in J.high()))
        G.require(not J.high(),'a permutation of commuting original-edge subdivisions did not flagify')
        # Compare final complexes after canonically naming each new vertex by
        # its subdivided original edge, not by chronology.
        names={i:(i,) for i in range(K.n)}
        for j,E in enumerate(order):names[K.n+j]=tuple(sorted(E))
        canon=tuple(sorted(tuple(sorted(names[i] for i in N)) for N in J.missing))
        if terminal is None:terminal=canon
        G.require(canon==terminal,'commuting final complex depends on edge order')
        perms+=1;inc=sum(a<b for a,b in zip(weights,weights[1:]));increases+=inc;max_peak=max(max_peak,max(weights))
        strict_orders+=all(a>b for a,b in zip(weights,weights[1:]));neutral_steps+=sum(a==b for a,b in zip(weights,weights[1:]))
        key=tuple(weights);weight_histograms[key]=weight_histograms.get(key,0)+1
    commuting={'model':'original_263_plateau','edges':edges,'refined_vertices':len(R.vertices),
       'original_facet_count':K.n,'all_pairs_original_edge_bound':len(R.vertices)-5,
       'all_edge_orders_checked':perms,'increasing_steps_across_orders':increases,
       'strictly_decreasing_full_orders':strict_orders,'neutral_step_occurrences':neutral_steps,
       'maximum_weight_along_orders':max_peak,'initial_weight':sum(len(N)-2 for N in K.high()),
       'distinct_weight_trajectories':len(weight_histograms),'graph_search':s,
       'sample_weight_sequences':[{'weights':list(w),'orders':c} for w,c in sorted(weight_histograms.items())[:12]]}
    return {'status':'PASS','stage':'obstructions','cycle_order_exhaustions':rows,'density_cases':density,
       'commuting_plateau':commuting,'seconds':round(time.monotonic()-start,4)},None,[]


def negative_controls(saved):
    failures=[]
    def reject(name,f):
        try:f()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):failures.append(name)
        else:raise AssertionError('forged data passed: '+name)
    data,out=saved[0];c=out['certificate']
    for name,edit in [('wrong_graph',lambda x:x['refinement'].update(auxiliary_edges=[])),
       ('missing_tube',lambda x:x['refinement']['connected_faces'].pop()),
       ('wrong_refined_path',lambda x:x['refinement']['refined_path'].pop()),
       ('missing_original_vertices',lambda x:x.update(vertices=[])),
       ('wrong_input_binding',lambda x:x.update(problem_sha256='00')),
       ('incomplete_nonfaces',lambda x:x['minimal_nonfaces'].pop()),
       ('missing_intersection_answers',lambda x:x.update(intersections=[])),
       ('invalid_degree_label',lambda x:x['refinement']['auxiliary_edges'][0].__setitem__(0,True))]:
        bad=deepcopy(c);edit(bad);reject(name,lambda bad=bad:G.verify(data,bad))
    K=G.old.Complex(4,[{0,1,2,3}])
    reject('nonflag_sparse_graph',lambda:G.route(K,frozenset({0,1,2}),frozenset({1,2,3}),3,[]))
    reject('registry_cap',lambda:G.GraphicalRefinement(K,[[0,1]],4))
    # Crossing intervals need to be excluded, not accepted merely because the
    # union is an original face. This guards the nestedness condition.
    K=G.old.Complex(4,[{0,1,2,3}]);R=G.GraphicalRefinement(K,[[0,1],[1,2],[2,3]])
    G.require(not R.ask({R.index[frozenset({0,1})],R.index[frozenset({1,2})]}),'crossing intervals became a face')
    old=(G.old.old.lp.ExactLP,G.old.old.basis.invert,G.old.old.basis.basis_packet,G.old.old.Discovery)
    def blocked(*a,**k):raise AssertionError('consumer invoked geometric discovery')
    G.old.old.lp.ExactLP=G.old.old.basis.invert=G.old.old.basis.basis_packet=G.old.old.Discovery=blocked
    try:
        for d,o in saved:G.require(G.verify(d,json.loads(json.dumps(o['certificate'])))==o['verified'],'search-disabled audit mismatch')
    finally:G.old.old.lp.ExactLP,G.old.old.basis.invert,G.old.old.basis.basis_packet,G.old.old.Discovery=old
    return {'negative_controls':failures,'search_disabled_audits':len(saved)}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['abstract','geometry','obstructions'],required=True);a=p.parse_args()
    report,fixture,saved=abstract_stage() if a.stage=='abstract' else geometry_stage() if a.stage=='geometry' else obstruction_stage()
    if saved:report.update(negative_controls(saved))
    report['scope']='Written graphical flag criterion and exact tests; no Lean or Prove2Me verdict'
    report['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'scripts').glob('*.py')) if not p.name.startswith('_')}
    (ROOT/f'research/GRAPHICAL_FLAG_{a.stage.upper()}_TESTS.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    if fixture is not None:(ROOT/f'fixtures/graphical_flag_{a.stage}.json').write_text(json.dumps(fixture,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
