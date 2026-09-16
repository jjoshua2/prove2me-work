#!/usr/bin/env python3
"""Route-union checks, including shorter-than-each shadows and adverse controls.

Cyclic-polars reuse #267's family as a control, not a new diameter theorem.
Small graphs are independently enumerated; larger cyclic comparison paths
are checked directly from the ORIGINAL rows without enumerating the graph.
"""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,time
import certified_rational_shadow as s
import certified_shadow_union as union
import test_certified_rational_shadow as ref
ROOT=Path(__file__).resolve().parents[1]


def cyclic(k):
    d=2*k;n=4*k+1
    points=[tuple(Q(t**j)for j in range(1,d+1))for t in range(n)]
    sums=[sum(p[j]for p in points)for j in range(d)]
    A=tuple(tuple(n*p[j]-sums[j]for j in range(d))for p in points);b=(Q(n),)*n
    def vertex(I):return tuple(s.dot(row,[b[i]for i in I])for row in s.inverse([A[i]for i in I]))
    path=[vertex(list(range(1+j,d+1+j)))for j in range(d+1)]
    for j,x in enumerate(path):
        s.audit_vertex(A,b,s.vertex_packet(A,b,x))
        s.require(s.active(A,b,x)==list(range(1+j,d+1+j)),'cyclic block not a simple original vertex')
    edges=[s.edge_packet(A,b,x,y)for x,y in zip(path,path[1:])]
    for x,y,c in zip(path,path[1:],edges):s.audit_edge(A,b,x,y,c)
    # A squared/distinct consecutive-root polynomial exposes each block;
    # Vandermonde independence proves the classical cyclic construction is
    # simplicial, hence these polars are simple. Disjoint endpoint active sets
    # require at least d exchanges. These d checked edges attain that bound.
    return {'A':A,'b':b,'start':path[0],'target':path[-1]}, {'path':path,'edges':edges,'simple_facet_exchange_lower_bound':d}


def family():
    records=[]
    for k in(2,3,4):
        data,comparison=cyclic(k);begin=time.monotonic()
        baseline=s.construct(data);r=union.construct(data,[[k-1,0],[k+1,0]]);z=r['verified']
        expected={2:([5,5],4),3:([8,8],6),4:([13,13],10)}[k]
        s.require(z['individual_shadow_edges']==expected[0]and z['selected_original_edges']==expected[1],'cyclic union count changed')
        s.require(z['selected_original_edges']>=2*k,'false global lower bound')
        graph=None
        if k==2:
            A,b,V,G,work=ref.reference(data['A'],data['b'])
            path=[tuple(map(Q,x))for x in z['path']]
            s.require(all(y in G[x]for x,y in zip(path,path[1:])),'reference rejects spliced route')
            s.require(ref.distances(G,tuple(data['start']))[tuple(data['target'])]==2*k,'reference distance')
            graph={'vertices':len(V),'edges':sum(map(len,G.values()))//2,'square_systems':work}
        record={key:value for key,value in z.items()if key!='path'}
        record.update(default_shadow_edges=baseline['verified']['original_edges'],
            independent_original_shortest_distance=2*k,global_shortest_certified=z['selected_original_edges']==2*k,
            max_endpoint_objective_bits=max(s.verify(data,c)['endpoint_objective_max_bits']for c in r['certificate']['shadows']),
            independent_full_graph=graph,seconds=round(time.monotonic()-begin,3),discovery=r['discovery'])
        records.append(record);print('cyclic',2*k,record['default_shadow_edges'],z['individual_shadow_edges'],z['selected_original_edges'],flush=True)
        ref.dump(ROOT/f'fixtures/shadow_union_cyclic{2*k}.json',{'input':data,**r,'default_shadow':baseline,'separate_shortest_route':comparison})
    return records


def small():
    records=[];pairs=edges=original_optima=0
    for name in('pentagon','octahedron3','embedded_square','redundant_cube'):
        A,b,V,G,work=ref.reference(*ref.models()[name]);pts=sorted(V);selected=[(pts[0],pts[-1]),(pts[1],pts[-2])]
        for u,v in selected:
            data={'A':A,'b':b,'start':u,'target':v};rot=[[0,0],[1,0],[0,1]]
            r=union.construct(data,rot);z=r['verified'];path=[tuple(map(Q,x))for x in z['path']]
            s.require(all(y in G[x]for x,y in zip(path,path[1:])),'small spliced original nonedge')
            shortest=ref.distances(G,u)[v]
            s.require(shortest<=z['selected_original_edges'],'beats full BFS distance')
            Gsub=union.union_graph([[tuple(map(Q,x))for x in s.verify(data,c)['path']]for c in r['certificate']['shadows']])
            s.require(ref.distances(Gsub,u)[v]==z['selected_original_edges'],'independent union BFS mismatch')
            records.append({'model':name,'start':u,'target':v,'shadow_edges':z['individual_shadow_edges'],
                'selected':z['selected_original_edges'],'original_shortest':shortest,'common_original_rows':z['locked_original_rows']})
            pairs+=1;edges+=z['selected_original_edges'];original_optima+=shortest
    return {'pairs':pairs,'original_edges':edges,'BFS_edges':original_optima,'records':records}


def negative():
    data,_=cyclic(2);r=union.construct(data,[[1,0],[3,0]]);cert=r['certificate'];names=[]
    def bad(name,edit):
        c=deepcopy(cert);edit(c)
        try:union.verify(data,c)
        except(ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('invalid union accepted: '+name)
    bad('changed_hash',lambda c:c.update(problem_sha256='bad'))
    bad('empty_shadows',lambda c:c.update(shadows=[]))
    bad('unseen_diagonal',lambda c:c.update(path=[c['path'][0],c['path'][-1]]))
    bad('omitted_potential_vertex',lambda c:c['distance_potential'].pop())
    bad('nonzero_start_distance',lambda c:next(r for r in c['distance_potential']if r['point']==c['path'][0]).update(distance=1))
    bad('false_target_distance',lambda c:next(r for r in c['distance_potential']if r['point']==c['path'][-1]).update(distance=0))
    bad('false_edge_potential',lambda c:next(r for r in c['distance_potential']if r['point']not in(c['path'][0],c['path'][-1])).update(distance=99))
    bad('floating_distance',lambda c:c['distance_potential'][0].update(distance=0.0))
    bad('corrupted_component',lambda c:c['shadows'][0]['queries'].pop())
    saved=[]
    def forbidden(*a,**k):raise AssertionError('auditor used discovery/BFS')
    for obj,name in[(s.lp,'ExactLP'),(s,'inverse'),(s,'independent_rows'),(s,'rank_packet'),(union,'deque')]:
        saved.append((obj,name,getattr(obj,name)));setattr(obj,name,forbidden)
    try:s.require(union.verify(data,cert)==r['verified'],'search-disabled union verification mismatch')
    finally:
        for obj,name,f in saved:setattr(obj,name,f)
    point={'A':[[1,0],[-1,0],[0,1],[0,-1]],'b':[0,0,0,0],'start':[0,0],'target':[0,0]}
    zero=union.construct(point,[[0,0],[1,0]])['verified']
    s.require(zero['selected_original_edges']==0 and zero['union_vertices']==1,'zero-step union endpoint handling')
    return {'rejected':len(names),'names':names,'LP_rank_inverse_BFS_disabled':True,'zero_step_union_checked':True}


def main():
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(250000)
    files=['certified_rational_shadow.py','certified_shadow_union.py','test_certified_rational_shadow.py','test_certified_shadow_union.py','exact_farkas_lp.py']
    out={'status':'PASS','family':family(),'small':small(),'negative':negative(),
         'source_sha256':{f'scripts/{n}':hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest()for n in files},
         'scope':'Original-edge routes and shortest-in-discovered-union certificates; no universal bound or Lean/Prove2Me verification.'}
    ref.dump(ROOT/'research/SHADOW_UNION_CHECK.json',out)
if __name__=='__main__':main()
