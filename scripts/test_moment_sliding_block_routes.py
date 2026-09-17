#!/usr/bin/env python3
"""Independent rational interpretation checks, NOT Lean verification.
The producer multiplies root polynomials; small reference graphs instead solve
all original square row systems. Large graphs are not enumerated.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import hashlib,json

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/publication_packets/moment_sliding_block_routes'

def require(ok,msg):
    if not ok: raise ValueError(msg)

def exact(x):
    require(type(x) in (int,str,F),'exact rational only')
    return F(x)

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(z) for z in x]
    return x

def setup(k,a,start,length):
    require(type(k)is int and k>0,'positive half-dimension required')
    require(type(start)is int and type(length)is int and start>=0 and length>=0,'invalid route indices')
    a=tuple(map(exact,a));m=len(a);d=2*k
    require(all(x<y for x,y in zip(a,a[1:])),'strict parameter ordering required')
    require(d<m and start+length+d<=m,'block does not fit original labels')
    means=[sum(t**j for t in a)/m for j in range(1,d+1)]
    A=[tuple(t**j-means[j-1] for j in range(1,d+1)) for t in a]
    return a,A

def coefficients(roots):
    p=[F(1)]
    for r in roots:
        q=[F(0)]*(len(p)+1)
        for j,v in enumerate(p):q[j]-=r*v;q[j+1]+=v
        p=q
    return p

def eval_poly(p,t):
    out=F(0)
    for c in reversed(p):out=out*t+c
    return out

def construct(k,a,start,length):
    a,A=setup(k,a,start,length);m=len(a);d=2*k;V=[]
    for shift in range(start,start+length+1):
        p=coefficients(a[shift:shift+d]);h=sum(eval_poly(p,t) for t in a)/m
        require(h>0,'root mean is not positive')
        V.append({'point':[-c/h for c in p[1:]],'coefficients':p,'mean':h})
    return serial({'format':'moment-sliding-block-v1','k':k,'parameters':a,
                   'start':start,'length':length,'vertices':V})

def verify(c):
    require(c['format']=='moment-sliding-block-v1','wrong format')
    k=c['k'];s=c['start'];L=c['length'];a,A=setup(k,c['parameters'],s,L);d=2*k;m=len(a)
    require(len(c['vertices'])==L+1,'wrong path length')
    points=[];active=[];nrows=nidentity=ninterior=0
    for q,v in enumerate(c['vertices']):
        x=tuple(map(exact,v['point']));p=list(map(exact,v['coefficients']));h=exact(v['mean'])
        require(len(x)==d and len(p)==d+1 and p[-1]==1 and h>0,'bad witness dimensions/mean')
        T=set(range(s+q,s+q+d));pv=[eval_poly(p,t) for t in a]
        require(all(z>=0 and (z==0)==(i in T) for i,z in enumerate(pv)),'wrong root signs or zero set')
        require(h==sum(pv)/m,'not the ORIGINAL full-label mean')
        require(x==tuple(-z/h for z in p[1:]),'wrong explicit coefficient vector')
        vals=[sum(aa*xx for aa,xx in zip(row,x)) for row in A]
        require(all(vv==1-z/h for vv,z in zip(vals,pv)),'original row identity failed')
        require(all(vv<=1 and (vv==1)==(i in T) for i,vv in enumerate(vals)),'wrong original active set')
        points.append(x);active.append(T);nrows+=m;nidentity+=m
    require(len(set(points))==len(points),'stationary/repeated route vertex')
    for i in range(m):
        times=[t for t,T in enumerate(active) if i in T]
        require(not times or times==list(range(min(times),max(times)+1)),'original facet reentry')
    for q,(u,v) in enumerate(zip(points,points[1:])):
        common=active[q]&active[q+1]
        require(len(common)==d-1,'not one original-row exchange')
        for t in (F(1,4),F(1,2),F(3,4)):
            x=tuple((1-t)*a+t*b for a,b in zip(u,v))
            vals=[sum(aa*xx for aa,xx in zip(row,x)) for row in A]
            require(all(z<=1 and (z==1)==(i in common) for i,z in enumerate(vals)),'incorrect segment interior')
            ninterior+=1
    require(L<=m-d,'route count exceeds its proved class bound')
    return {'status':'PASS','dimension':d,'original_rows':m,'start':s,'original_edges':L,
       'vertices_checked':len(points),'row_identity_checks':nidentity,'original_inequalities':nrows,
       'strict_interior_points':ninterior,'original_reentries':0,'full_graph_enumerated':False}

def solve_square(M,b):
    """Independent exact Gaussian elimination: no root-polynomial producer."""
    n=len(M);T=[list(map(F,row))+[F(rhs)] for row,rhs in zip(M,b)]
    for j in range(n):
        r=next((r for r in range(j,n) if T[r][j]),None)
        if r is None:return None
        T[r],T[j]=T[j],T[r];t=T[j][j];T[j]=[x/t for x in T[j]]
        for i in range(n):
            if i!=j:
                t=T[i][j];T[i]=[x-t*y for x,y in zip(T[i],T[j])]
    return tuple(row[-1] for row in T)

def reference(A):
    m=len(A);d=len(A[0]);V={};systems=0;infeasible=0
    for I in combinations(range(m),d):
        systems+=1;x=solve_square([A[i] for i in I],[1]*d)
        if x is None:continue
        vals=[sum(a*b for a,b in zip(row,x)) for row in A]
        if not all(t<=1 for t in vals):infeasible+=1;continue
        J=frozenset(i for i,v in enumerate(vals) if v==1)
        require(len(J)==d,'small reference not simple');V[x]=J
    adj={x:[] for x in V}
    for u,v in combinations(V,2):
        if len(V[u]&V[v])==d-1:adj[u].append(v);adj[v].append(u)
    require(all(len(N)==d for N in adj.values()),'reference not d-regular')
    return V,adj,systems,infeasible

def distances(adj,u):
    out={u:0};q=deque([u])
    while q:
        v=q.popleft()
        for w in adj[v]:
            if w not in out:out[w]=out[v]+1;q.append(w)
    require(len(out)==len(adj),'reference disconnected')
    return out

def main():
    records=[];saved=[];graphs=0;totals={k:0 for k in ['reference_square_systems','reference_vertices','reference_edges',
      'infeasible_full_tight','corridor_edges','original_inequalities','row_identity_checks','interior_points',
      'objective_checks','corridor_endpoint_pairs','nonshortest_corridor_subpaths']}
    for k,m in [(1,3),(1,5),(1,8),(2,5),(2,7),(2,9),(3,7),(3,9),(3,13)]:
        # Each list is a prefix of an explicit strictly increasing sequence on N.
        a=[F(i**3+i-3,7) for i in range(m)]
        c=construct(k,a,0,m-2*k);r=verify(c);_,A=setup(k,a,0,m-2*k)
        V,adj,ns,bad=reference(A);pts=[tuple(map(F,v['point'])) for v in c['vertices']]
        require(all(x in V for x in pts),'constructed point absent from independent graph')
        require(all(v in adj[u] for u,v in zip(pts,pts[1:])),'constructed step not a reference edge')
        obj=0
        for u,v in zip(pts,pts[1:]):
            C=V[u]&V[v];maximizers=[]
            for x in V:
                val=sum(sum(A[i][j]*x[j] for j in range(2*k)) for i in C);obj+=1
                require(val<=len(C),'objective bound failed')
                if val==len(C):maximizers.append(x)
            require(set(maximizers)=={u,v},'common-row objective exposes a larger face')
        pairs=nonshort=0
        for i,u in enumerate(pts):
            D=distances(adj,u)
            for j in range(i+1,len(pts)):
                pairs+=1;nonshort+=j-i>D[pts[j]]
        row={**r,'reference_square_systems':ns,'reference_vertices':len(V),
          'reference_edges':sum(map(len,adj.values()))//2,'infeasible_full_tight':bad,
          'reference_all_pairs_diameter':max(max(distances(adj,u).values()) for u in V),
          'objective_checks':obj,'corridor_endpoint_pairs':pairs,'nonshortest_corridor_subpaths':nonshort,
          'whole_corridor_BFS_distance':distances(adj,pts[0])[pts[-1]],'full_graph_enumerated':True}
        records.append(row);saved.append(c);graphs+=1
        for key in ('reference_square_systems','reference_vertices','reference_edges','infeasible_full_tight',
                    'original_inequalities','row_identity_checks','objective_checks','corridor_endpoint_pairs',
                    'nonshortest_corridor_subpaths'):totals[key]+=row[key]
        totals['corridor_edges']+=r['original_edges'];totals['interior_points']+=r['strict_interior_points']
        print('small',k,m,'done',flush=True)
    assorted=[]
    for k in (1,2,3,4):
        m=4*k+3
        a=[F(5*i+2,3) for i in range(m)]
        for s,L in [(0,0),(m-2*k,0),(1,k),(2,2*k)]:
            c=construct(k,a,s,L);assorted.append(verify(c))
            if L==0:saved.append(c)
    large=[]
    for k in (4,8,16,32):
        m=4*k+1;c=construct(k,list(range(m)),1,2*k);r=verify(c)
        require(not set(range(1,2*k+1))&set(range(2*k+1,4*k+1)),'large endpoints not disjoint')
        large.append({**r,'disjoint_endpoint_active_sets':True});saved.append(c)
        print('large',k,'done',flush=True)
    failures=[]
    def reject(name,f):
        try:f()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):failures.append(name)
        else:raise AssertionError('accepted malformed certificate '+name)
    baseline=next(c for c in saved if c['k']==2 and len(c['parameters'])==9)
    for name,fn in [('wrong_point',lambda c:c['vertices'][0]['point'].__setitem__(0,'999')),
       ('wrong_mean',lambda c:c['vertices'][0].update(mean='1')),
       ('wrong_root_coefficients',lambda c:c['vertices'][0]['coefficients'].__setitem__(0,'999')),
       ('missing_vertex',lambda c:c['vertices'].pop()),
       ('nonconsecutive_jump',lambda c:c['vertices'].__setitem__(1,c['vertices'][-1])),
       ('duplicate_node',lambda c:c['parameters'].__setitem__(1,c['parameters'][0])),
       ('unordered_nodes',lambda c:c['parameters'].reverse()),
       ('outside_label_window',lambda c:c.update(start=100)),
       ('zero_half_dimension',lambda c:c.update(k=0)),
       ('boolean_length',lambda c:c.update(length=True)),
       ('float_node',lambda c:c['parameters'].__setitem__(0,0.0))]:
        bad=deepcopy(baseline);fn(bad);reject(name,lambda bad=bad:verify(bad))
    # Parity is essential: a three-root consecutive block crosses sign at nodes
    # on opposite sides. The theorem intentionally requires positive even dimension.
    oddp=coefficients([F(2),F(3),F(4)])
    require(eval_poly(oddp,F(0))<0<eval_poly(oddp,F(6)),'odd-degree countercontrol failed')
    old1,old2=globals()['construct'],globals()['coefficients']
    def disabled(*a,**kw):raise AssertionError('consumer invoked production')
    globals()['construct']=globals()['coefficients']=disabled
    try:
        for c in saved:verify(c)
    finally:globals()['construct'],globals()['coefficients']=old1,old2
    source=(PACKET/'solution.lean').read_text();meta=json.loads((PACKET/'problem.json').read_text())
    sig=source.split('\ntheorem solution ',1)[1].split(' := by\n',1)[0]
    target=meta['formal_statement'].split('\ntheorem moment_sliding_block_original_routes ',1)[1].split(' := by sorry',1)[0]
    require(sig==target,'exact target mismatch')
    require(all(x not in source for x in ('sorry','admit','native_decide','unsafe')),'forbidden proof token')
    report={'status':'PASS','scope':'Exact rational interpretation/source checks, not Lean or Prove2Me verification',
      'small_models':records,'small_totals':totals,'assorted_subcorridors':assorted,'large':large,
      'producer_disabled_audits':len(saved),'negative_controls':failures,'odd_degree_sign_counterexample':True,
      'exact_target_signature_match':True,'source_lines':len(source.splitlines()),
      'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [PACKET/'solution.lean',PACKET/'problem.json',Path(__file__)]}}
    (ROOT/'research/MOMENT_SLIDING_ROUTE_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'fixtures/moment_sliding_route_examples.json').write_text(json.dumps(saved,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'totals':totals,'large':large,'saved':len(saved),'negative':len(failures)},indent=2))
if __name__=='__main__':main()
