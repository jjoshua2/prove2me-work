#!/usr/bin/env python3
"""Exact direct-route regression, with independent finite vertex graphs.
The reference enumerator is a TEST ONLY. The producer sees A,b,u,v and budget.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from collections import deque
from pathlib import Path
from copy import deepcopy
import hashlib,json,random,time,argparse
import sympy as sp
import original_route_bmc as R

ROOT=Path(__file__).resolve().parents[1]


def cube(d,duplicate=False):
    A=[[Q(s*(i==j)) for j in range(d)] for i in range(d) for s in(-1,1)]
    b=[Q(0),Q(1)]*d
    if duplicate:A+=[[2*x for x in A[0]]];b+=[Q(0)]
    return A,b


def pyramid(duplicate=False):
    A=[[1,0,1],[-1,0,1],[0,1,1],[0,-1,1],[0,0,-1]];b=[1,1,1,1,0]
    if duplicate:A.append([0,0,-2]);b.append(0)
    return [list(map(Q,r)) for r in A],list(map(Q,b))


def cross(d):
    return [list(map(Q,s)) for s in product((-1,1),repeat=d)],[Q(1)]*(2**d)


def birkhoff(n):
    """Eliminate last row/column exactly; (n-1)^2 coordinates, n^2 inequalities."""
    d=(n-1)**2;A=[];b=[]
    for i in range(n-1):
        for j in range(n-1):
            r=[Q(0)]*d;r[i*(n-1)+j]=-1;A.append(r);b.append(Q(0))
    for i in range(n-1):A.append([Q(k//(n-1)==i) for k in range(d)]);b.append(Q(1))
    for j in range(n-1):A.append([Q(k%(n-1)==j) for k in range(d)]);b.append(Q(1))
    A.append([-Q(1)]*d);b.append(Q(2-n))
    V=[tuple(Q(p[i]==j) for i in range(n-1) for j in range(n-1)) for p in permutations(range(n))]
    return A,b,V


def moment(d,m):
    V=[[Q(i**j) for j in range(1,d+1)] for i in range(m)]
    mean=[sum(v[j] for v in V)/m for j in range(d)]
    return [[v[j]-mean[j] for j in range(d)] for v in V],[Q(1)]*m


def reference(A,b,known=None):
    """Independent SymPy elimination/rank; no producer inverse or rank routines."""
    d=len(A[0]);count=0;V={}
    if known is not None:
        candidates=known
    else:
        candidates=[]
        for I in combinations(range(len(A)),d):
            count+=1;M=sp.Matrix([A[i] for i in I])
            if M.det()==0:continue
            x=tuple(Q(str(z)) for z in M.inv()*sp.Matrix([b[i] for i in I]));candidates.append(x)
    for x in candidates:
        if all(sum(a*t for a,t in zip(r,x))<=rhs for r,rhs in zip(A,b)):
            V[tuple(x)]=[i for i,r in enumerate(A) if sum(a*t for a,t in zip(r,x))==b[i]]
    R.require(V,'empty reference graph')
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        J=sorted(set(V[x])&set(V[y]));rank=sp.Matrix([A[j] for j in J]).rank() if J else 0
        if rank==d-1:adj[x].append(y);adj[y].append(x)
    D={}
    for u in V:
        dist={u:0};q=deque([u])
        while q:
            x=q.popleft()
            for y in adj[x]:
                if y not in dist:dist[y]=dist[x]+1;q.append(y)
        R.require(len(dist)==len(V),'disconnected reference')
        D[u]=dist
    return V,adj,D,count


def selected_pairs(V,cap=6):
    pairs=list(combinations(V,2));random.Random(268+len(V)).shuffle(pairs)
    return pairs[:cap]


def outcome(data,L,backend,timeout,round_cap=100):
    r=R.solve(data,L,timeout,round_cap,backend=backend)
    return r


def klee_walkup(capped=False):
    """Borgwardt--Stephen--Yusun, arXiv:1611.08039v2, p17: negate >= rows.
    The eight-row polyhedron is UNBOUNDED. Our cap is a separately checked
    nine-row bounded control, not silently added to the producer input.
    """
    A=[[6,3,0,-1],[3,6,-1,0],[35,45,-6,-3],[45,35,-3,-6],
       [-1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1]]
    b=[1,1,8,8,0,0,0,0]
    if capped:A.append([1,1,1,1]);b.append(19)
    return list(map(lambda a:list(map(Q,a)),A)),list(map(Q,b))


def entry_ledger(A,b,c):
    sets=[{i for i,a in enumerate(A) if R.dot(a,list(map(Q,p['point'])))==b[i]} for p in c['vertices']]
    # The simple-case identity is applied ONLY after all visited active sets
    # have exactly d genuine rows; redundant/nonsimple inputs use rank instead.
    if not all(len(F)==len(A[0]) for F in sets):return None
    seen=set(sets[0]);last=sets[0];reentries=[]
    for j,F in enumerate(sets[1:],1):
        R.require(len(F-last)==len(last-F)==1,'not a simple facet exchange')
        reentries.extend({'step':j,'facet':i} for i in (F-last)&seen)
        seen|=F;last=F
    R.require(len(c['edges'])==len(seen)-len(A[0])+len(reentries),'facet-entry identity')
    return {'active_sets':[sorted(F) for F in sets],'distinct_facets':len(seen),'reentries':reentries}


def main():
    started=time.monotonic();B=R.Z3Backend();models=[];certs=[];queries=[];bad_controls=[]
    methods={'inverse':R.solve_inverse,'lazy':R.solve}
    def execute(data,L,method,timeout=5000):
        out=methods[method](data,L,timeout_ms=timeout,backend=B)
        if 'final_smt' in out:
            R.require(hashlib.sha256(out['final_smt'].encode()).hexdigest()==out['smt_sha256'],'SMT export hash mismatch')
        return out
    def save(name,data,out,**extra):
        if out['status']=='SAT_CERTIFIED':
            R.require(R.verify(data,out['certificate'])==out['verified'],'positive readback changed')
            certs.append({'name':name,'input':R.serial(data),'output':out,**extra})
    cases=[('cube3',*cube(3),None),('pyramid3',*pyramid(),None),
       ('pyramid_redundant_base',*pyramid(True),None),('crosspolytope3',*cross(3),None),
       ('crosspolytope4',*cross(4),[tuple(Q(s*(i==j)) for j in range(4)) for i in range(4) for s in(-1,1)]),
       ('cyclic_polar4_9',*moment(4,9),None),('birkhoff3',*birkhoff(3)[:2],None)]
    for name,A,b,known in cases:
        V,adj,dist,count=reference(A,b,known);pairs=selected_pairs(V,6)
        if name.startswith('pyramid'):pairs+=[(tuple(map(Q,[-1,-1,0])),tuple(map(Q,[1,1,0])))]
        row={'name':name,'dimension':len(A[0]),'input_rows':len(A),'vertices':len(V),
           'reference_edges':sum(map(len,adj.values()))//2,'reference_square_systems':count,
           'reference_vertex_source':'coordinate family plus independent rank graph' if known is not None else 'complete exact active-basis enumeration',
           'pairs':len(pairs),'methods':{}}
        for method in methods:
            stats={'sat_routes':0,'solver_unsat_below_BFS':0,'unknown':0,'rank_exclusions':0,'edges':0,
               'overdetermined_vertex_visits':0,'max_solver_calls_per_query':0}
            for u,v in pairs:
                data={'A':A,'b':b,'start':u,'target':v};n=dist[u][v]
                neg=execute(data,n-1,method);pos=execute(data,n,method)
                stats['solver_unsat_below_BFS']+=neg['status']=='UNSAT_SOLVER'
                stats['unknown']+=sum(o['status']=='UNKNOWN' for o in (neg,pos))
                R.require(neg['status']!='SAT_CERTIFIED','route shorter than independent BFS')
                R.require(pos['status']!='UNSAT_SOLVER','solver excludes a reference route')
                stats['rank_exclusions']+=sum(len(o.get('row_dependence_cuts',[])) for o in (neg,pos))
                stats['max_solver_calls_per_query']=max(stats['max_solver_calls_per_query'],len(neg.get('rounds',[1])),len(pos.get('rounds',[1])))
                if pos['status']=='SAT_CERTIFIED':
                    path=[tuple(map(Q,z['point'])) for z in pos['certificate']['vertices']]
                    R.require(pos['verified']['original_edges']==n and all(y in adj[x] for x,y in zip(path,path[1:])),'certificate not shortest original reference path')
                    stats['sat_routes']+=1;stats['edges']+=n;stats['overdetermined_vertex_visits']+=pos['verified']['overdetermined_vertex_visits']
                    save(name+'_'+method,data,pos,BFS_shortest=n)
                queries.append({'name':name,'method':method,'budget':n-1,'output':neg})
            row['methods'][method]=stats
        models.append(row);print('model',row,flush=True)
    # Nonsimple genuine-facet trap: shared-row COUNT is not shared-row RANK.
    A,b,V=birkhoff(4);u=tuple(Q(i==j) for i in range(3) for j in range(3))
    perm=(1,0,3,2);v=tuple(Q(perm[i]==j) for i in range(3) for j in range(3))
    data={'A':A,'b':b,'start':u,'target':v};common=[i for i in range(len(A)) if R.dot(A[i],u)==b[i] and R.dot(A[i],v)==b[i]]
    rank=sp.Matrix([A[i] for i in common]).rank();R.require(len(common)==8 and rank==7,'rank trap missing')
    initial=B.solve(R.encoding(A,b,u,v,1),3000);R.require(initial['status']=='sat','uncorrected trap not reproduced')
    VV,adj,dist,_=reference(A,b,V);R.require(dist[u][v]==2,'Birkhoff reference')
    special={'dimension':9,'genuine_facets':16,'reference_permutation_vertices':24,'common_tight_rows':common,
      'common_rank':int(rank),'uncorrected_count_only_budget_one':'SAT','independent_shortest':2,'methods':{}}
    negative_dependencies=[]
    for method in methods:
        neg=execute(data,1,method);pos=execute(data,2,method)
        R.require(neg['status']=='UNSAT_SOLVER' and pos['status']=='SAT_CERTIFIED','rank trap not resolved')
        R.require(pos['verified']['original_edges']==2,'Birkhoff route length')
        special['methods'][method]={'budget_one':neg['status'],'budget_two':pos['status'],'edges':2,
                                   'rank_exclusions':len(neg.get('row_dependence_cuts',[]))}
        if method=='lazy':negative_dependencies=neg['row_dependence_cuts']
        queries.append({'name':'birkhoff4_rank_trap','method':method,'budget':1,'output':neg})
        save('birkhoff4_'+method,data,pos,BFS_shortest=2)
    print('Birkhoff4',special,flush=True)
    # A classical forced-reentry example and a bounded nine-facet counterpart.
    klee=[]
    for capped in (False,True):
        A,b=klee_walkup(capped);V,adj,dist,count=reference(A,b)
        u=(Q(0),)*4;v=(Q(1),Q(1),Q(8),Q(8));R.require(dist[u][v]==5,'Klee-Walkup distance')
        R.require(all(len(J)==4 for J in V.values()),'simple model expected')
        anchors=[]
        for i in range(len(A)):
            X=[x for x,J in V.items() if i in J]
            # A finite-vertex average works for these specific rows; tested
            # directly, not presumed valid on every unbounded polyhedron.
            mean=tuple(sum(x[j] for x in X)/len(X) for j in range(4))
            R.require([j for j in range(len(A)) if R.dot(A[j],mean)==b[j]]==[i],'not a unique-tight-row facet anchor')
            anchors.append(R.serial(mean))
        if not capped:R.require(all(R.dot(a,[Q(0),Q(0),Q(1),Q(0)])<=0 for a in A),'unbounded recession witness')
        row={'name':'capped_Klee_Walkup' if capped else 'unbounded_Klee_Walkup','dimension':4,'genuine_facets':len(A),
          'bounded':capped,'vertices':len(V),'edges_in_reference':sum(map(len,adj.values()))//2,'exact_square_systems':count,
          'BFS_distance':5,'facet_anchors':anchors,'methods':{}}
        for method in methods:
            data={'A':A,'b':b,'start':u,'target':v};neg=execute(data,4,method);pos=execute(data,5,method)
            R.require(neg['status']=='UNSAT_SOLVER' and pos['status']=='SAT_CERTIFIED','Klee query failed')
            log=entry_ledger(A,b,pos['certificate']);R.require(pos['verified']['original_edges']==5,'Klee count')
            if not capped:R.require(len(log['reentries'])>=1,'impossible nonrevisiting U4 route')
            row['methods'][method]={'budget4':neg['status'],'budget5':pos['status'],'facet_entry_ledger':log}
            queries.append({'name':row['name'],'method':method,'budget':4,'output':neg})
            save(row['name']+'_'+method,data,pos,BFS_shortest=5,facet_entry_ledger=log)
        klee.append(row);print('Klee-Walkup',row['name'],row['vertices'],flush=True)
    # Larger originals: no reference graph is built for these calls.
    stress=[]
    for d in (5,8,12,16):
        A,b=cube(d);data={'A':A,'b':b,'start':[Q(0)]*d,'target':[Q(1)]*d}
        method='inverse' if d<=8 else 'lazy';o=execute(data,d,method,10000)
        rr={'name':f'cube{d}','dimension':d,'rows':2*d,'method':method,'budget':d,'status':o['status'],
          'known_vertices':2**d,'reference_graph_enumerated':False,'rank_exclusions':len(o.get('row_dependence_cuts',[]))}
        if o['status']=='SAT_CERTIFIED':R.require(o['verified']['original_edges']==d,'cube source-facet lower bound');save(rr['name'],data,o,shortest_by_source_facet_drop=d)
        stress.append(rr)
    A,b,_=birkhoff(5);p=(1,0,3,2,4)
    data={'A':A,'b':b,'start':[Q(i==j) for i in range(4) for j in range(4)],'target':[Q(p[i]==j) for i in range(4) for j in range(4)]}
    J=[i for i,a in enumerate(A) if R.dot(a,data['start'])==b[i]==R.dot(a,data['target'])]
    rank=int(sp.Matrix([A[i] for i in J]).rank());R.require(rank<15,'chosen B5 pair adjacent')
    o=execute(data,2,'inverse',10000)
    stress.append({'name':'birkhoff5','dimension':16,'rows':25,'method':'inverse','budget':2,'status':o['status'],
      'encoding_bytes':o.get('encoding_bytes'),'common_tight_rank':rank,'reference_graph_enumerated':False})
    if o['status']=='SAT_CERTIFIED':R.require(o['verified']['original_edges']==2,'B5 shortest by nonadjacency');save('birkhoff5',data,o,shortest_by_exact_nonadjacency=True)
    # Hard original cyclic inputs from #267: a short route is known, but this
    # unrestricted solver may time out. An UNKNOWN must not be read as distance.
    for k in (3,4,8):
        d=2*k;A,b=moment(d,4*k+1)
        def vertex_from_rows(I):
            inv=R.right_inverse([A[i] for i in I],d)
            return [sum(row) for row in inv]
        data={'A':A,'b':b,'start':vertex_from_rows(range(1,2*k+1)),
              'target':vertex_from_rows(range(2*k+1,4*k+1))}
        o=R.solve(data,d,timeout_ms=2000,round_cap=10,backend=B)
        R.require(o['status']!='UNSAT_SOLVER','known cyclic route rejected')
        stress.append({'name':f'cyclic_polar_{d}_{4*k+1}','dimension':d,'rows':4*k+1,
          'method':'lazy','budget':d,'status':o['status'],'reason':o.get('reason'),
          'timeout_ms_per_round':2000,'completed_rounds':len(o.get('rounds',[])),
          'known_short_route_from_prior_construction':d,'reference_graph_enumerated':False})
        save('cyclic_hard_'+str(d),data,o,known_prior_upper_bound=d)
        if o['status']=='UNKNOWN':queries.append({'name':'cyclic_hard_'+str(d),'budget':d,'output':o})
    # Geometry-preserving transformations need not preserve solver tie choices.
    A,b=pyramid();u=[Q(-1),Q(-1),Q(0)];v=[Q(1),Q(1),Q(0)]
    T=sp.Matrix([[1,2,1],[0,1,1],[1,0,1]]);Ti=T.inv();h=[Q(2),Q(-3),Q(1)]
    AA=[[sum(a[j]*Q(str(Ti[j,k])) for j in range(3)) for k in range(3)] for a in A]
    bb=[rhs+R.dot(a,h) for rhs,a in zip(b,AA)]
    transform=lambda x:[sum(Q(int(T[i,j]))*x[j] for j in range(3))+h[i] for i in range(3)]
    transformed=[]
    for scale in (False,True):
        weights=[Q(i+2,i+1) if scale else Q(1) for i in range(len(A))]
        data={'A':[[w*z for z in a] for w,a in zip(weights,AA)],'b':[w*z for w,z in zip(weights,bb)],'start':transform(u),'target':transform(v)}
        for method in methods:
            o=execute(data,2,method);R.require(o['status']=='SAT_CERTIFIED' and o['verified']['original_edges']==2,'affine shortest existence changed')
            transformed.append({'positive_row_scaling':scale,'method':method,'edges':2});save('affine_pyramid_'+str(scale)+'_'+method,data,o)
    edgecases=[('stationary',{'A':[[1],[-1]],'b':[1,0],'start':[0],'target':[0]},0),
      ('interval',{'A':[[1],[-1]],'b':[1,0],'start':[0],'target':[1]},1),
      ('embedded_segment',{'A':[[1,0],[-1,0],[0,1],[0,-1]],'b':[1,0,0,0],'start':[0,0],'target':[1,0]},1)]
    for name,data,L in edgecases:
        for method in methods:
            r=execute(data,L,method);R.require(r['status']=='SAT_CERTIFIED','edge-case failure');save(name+'_'+method,data,r)
    # All resource-limit outcomes are explicitly distinct from UNSAT.
    class Unknown:
        version='test-double'
        def solve(self,*args):return {'status':'unknown','reason':'test resource limit'}
    for method in methods:
        r=methods[method](certs[0]['input'],3,backend=Unknown());R.require(r['status']=='UNKNOWN' and not r['independent_negative_proof'],'unknown mislabeled')
    r=R.solve_inverse(certs[0]['input'],3,encoding_cap=1);R.require(r['status']=='UNKNOWN','encoding cap mislabeled')
    A,b=pyramid(True);u=[Q(-1),Q(-1),Q(0)];v=[Q(1),Q(1),Q(0)]
    phantom_data={'A':A,'b':b,'start':u,'target':v};mocked={**{f'x_0_{i}':x for i,x in enumerate(u)},**{f'x_1_{i}':x for i,x in enumerate(v)}}
    for t,I in [(0,[1,3,4]),(1,[0,2,4])]:
        for i in range(6):mocked[f'v_{t}_{i}']=i in I
    for i in range(6):mocked[f'e_0_{i}']=i in [4,5]
    class Phantom:
        version='dependent-test-double'
        def solve(self,*args):return {'status':'sat','model':mocked}
    r=R.solve(phantom_data,1,round_cap=1,backend=Phantom());R.require(r['status']=='UNKNOWN' and len(r['row_dependence_cuts'])==1,'round cap mislabeled')
    originals=(R.row_reduce,R.right_inverse,R.Z3Backend,R.solve,R.solve_inverse)
    def disabled(*args,**kwargs):raise AssertionError('positive verifier invoked discovery')
    R.row_reduce=R.right_inverse=R.Z3Backend=R.solve=R.solve_inverse=disabled
    try:
        for c in certs:R.verify(c['input'],json.loads(json.dumps(c['output']['certificate'])))
        for c in negative_dependencies:R.audit_dependency(birkhoff(4)[0],c)
    finally:R.row_reduce,R.right_inverse,R.Z3Backend,R.solve,R.solve_inverse=originals
    target=next(c for c in certs if c['name']=='cube3_inverse');c0=target['output']['certificate'];inp=target['input']
    def reject(name,fn):
        try:fn()
        except(ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):bad_controls.append(name)
        else:raise AssertionError('accepted forged claim '+name)
    for name,mut in [('wrong_vertex',lambda c:c['vertices'][0]['point'].__setitem__(0,'99')),
      ('bad_vertex_inverse',lambda c:c['vertices'][0]['right_inverse'][0].__setitem__(0,'99')),
      ('bad_edge_inverse',lambda c:c['edges'][0]['right_inverse'][0].__setitem__(0,'99')),
      ('repeated_edge_label',lambda c:c['edges'][0].update(shared_rows=[0,0])),
      ('wrong_input_binding',lambda c:c.update(problem_sha256='00')),('insufficient_budget',lambda c:c.update(budget=0)),
      ('bool_row_index',lambda c:c['vertices'][0]['basis'].__setitem__(0,True)),
      ('float_coordinate',lambda c:c['vertices'][0]['point'].__setitem__(0,0.0))]:
        bad=deepcopy(c0);mut(bad);reject(name,lambda bad=bad:R.verify(inp,bad))
    dep=deepcopy(negative_dependencies[0]);dep['coefficients'][0]='999'
    reject('forged_dependency_cut',lambda:R.audit_dependency(birkhoff(4)[0],dep))
    reject('nonvertex_endpoint',lambda:R.solve_inverse({'A':[[1],[-1]],'b':[1,0],'start':['1/2'],'target':[1]},1))
    reject('boolean_budget',lambda:R.solve_inverse(inp,True))
    report={'status':'PASS','solver_version':B.version,'sympy_test_version':sp.__version__,
      'scope':'Exact fixed-budget formulation and independently audited positive routes; solver UNSAT is not a verified proof.',
      'models':models,'birkhoff4_rank_trap':special,'klee_walkup':klee,'stress':stress,'affine_comparisons':transformed,
      'edge_cases':[x[0] for x in edgecases],'search_disabled_positive_audits':len(certs),'negative_controls':bad_controls,
      'unknown_controls':['solver_unknown_inverse','solver_unknown_lazy','encoding_cap','rank_round_cap'],
      'total_saved_routes':len(certs),'negative_queries_saved':len(queries),'seconds':time.monotonic()-started,
      'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/'research/ORIGINAL_ROUTE_BMC_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'fixtures/original_route_bmc_examples.json').write_text(json.dumps({'routes':certs,'negative_queries':queries},indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
