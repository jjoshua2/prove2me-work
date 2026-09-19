#!/usr/bin/env python3
"""Exact original-H composition tests. Not Lean extraction or formal Python.
Reuses the unchanged accepted label router and root-coefficient constructor.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import Counter, deque
from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json, random
import test_gale_even_gap_routes as labels
import test_moment_root_catalogue as roots


def inverse(A):
    d=len(A); cols=[]
    for j in range(d):
        x,r,inc=roots.square_solve(A,[Q(i==j) for i in range(d)])
        if x is None: raise ValueError('singular vertex basis')
        cols.append(x)
    return [list(row) for row in zip(*cols)]


def encode_record(a,d,S,T):
    walk=labels.build(len(a),S,T);A=roots.row_matrix(a,d);vertices=[]
    for I in walk:
        c=roots.candidate(a,d,I)
        if c['status']!='VERTEX': raise ValueError('label route is not geometrically feasible')
        x=list(map(Q,c['point']))
        vertices.append(dict(tight=list(I),point=list(map(str,x)),
                             inverse=[[str(z) for z in row] for row in inverse([A[i] for i in I])]))
    return dict(a=list(map(str,a)),dimension=d,start=list(S),target=list(T),vertices=vertices)


def audit(c):
    a=list(map(Q,c['a']));m=len(a);d=c['dimension']
    if not 0<=d<m or any(x>=y for x,y in zip(a,a[1:])):raise ValueError('ordered parameters/dimension')
    V=c['vertices'];walk=[v['tight'] for v in V]
    length=labels.audit(m,c['start'],c['target'],walk);A=roots.row_matrix(a,d)
    parsed=[]
    for v in V:
        I=v['tight'];x=list(map(Q,v['point']));R=[list(map(Q,row)) for row in v['inverse']]
        if len(x)!=d or len(R)!=d or any(len(r)!=d for r in R):raise ValueError('matrix size')
        z=[roots.dot(row,x) for row in A]
        if any(t>1 for t in z) or I!=[i for i,t in enumerate(z) if t==1]:raise ValueError('original feasibility/tight set')
        if any(sum(A[I[i]][k]*R[k][j] for k in range(d))!=int(i==j)
               for i in range(d) for j in range(d)):raise ValueError('original inverse')
        parsed.append((I,x,R))
    edgeids=0
    for (I,x,R),(J,y,_) in zip(parsed,parsed[1:]):
        common=sorted(set(I)&set(J));cols=[I.index(i) for i in common]
        if x==y or len(common)+1!=d:raise ValueError('degenerate/incorrect edge')
        if any(sum(A[common[i]][k]*R[k][cols[j]] for k in range(d))!=int(i==j)
               for i in range(d-1) for j in range(d-1)):raise ValueError('common rank')
        edgeids+=(d-1)**2
    return dict(length=length,vertex_count=len(V),original_row_checks=len(V)*m,
                source_inverse_identities=len(V)*d*d,common_rank_identities=edgeids)


def run():
    rng=random.Random(308);totals=Counter();models=[];saved=[];large=[]
    choices=[(d,m) for m in range(1,8) for d in range(m)]
    for model,(d,m) in enumerate(choices):
        a=[Q(x,7) for x in sorted(rng.sample(range(-50,80),m))]
        A=roots.row_matrix(a,d);V={};basis_count=0
        for S in combinations(range(m),d):
            basis_count+=1
            x,rank,inc=roots.square_solve([A[i] for i in S],[Q(1)]*d)
            if x is not None and all(roots.dot(row,x)<=1 for row in A):
                I=tuple(i for i,row in enumerate(A) if roots.dot(row,x)==1)
                assert len(I)==d;V[I]=x
        legal={S for S in combinations(range(m),d) if labels.gaps(m,S)}
        assert set(V)==legal
        G={S:{T for T in V if S!=T and len(set(S)&set(T))+1==d} for S in V}
        D={}
        for source in G:
            dist={source:0};q=deque([source])
            while q:
                z=q.popleft()
                for t in G[z]:
                    if t not in dist:dist[t]=dist[z]+1;q.append(t)
            assert len(dist)==len(G);D[source]=dist
        counts=Counter()
        for S in G:
            for T in G[S]:
                if S>=T:continue
                C=set(S)&set(T)
                maximizers={I for I,x in V.items() if sum(roots.dot(A[i],x) for i in C)==len(C)}
                assert maximizers=={S,T}
                counts['unique_edges']+=1;counts['supporting_vertex_checks']+=len(V)
        point_cache={S:roots.candidate(a,d,S) for S in V}
        for S,T in product(V,repeat=2):
            walk=labels.build(m,S,T);L=labels.audit(m,S,T,walk)
            assert all(Y in G[X] for X,Y in zip(walk,walk[1:]))
            for I in walk:
                c=point_cache[I];assert tuple(map(Q,c['point']))==V[I]
                counts['row_identities']+=roots.verify_record(a,d,c)
                counts['negative_mean_visits']+=Q(c['mean'])<0
            counts['routes']+=1;counts['edge_occurrences']+=L;counts['shortest_edge_occurrences']+=D[S][T]
            counts['nonshortest_routes']+=L>D[S][T]
            counts['repeated_vertex_routes']+=len(set(walk))<len(walk)
            counts['target_row_loss_routes']+=any(not(set(X)&set(T))<=set(Y) for X,Y in zip(walk,walk[1:]))
        if model in (0,2,5,9,14,20,27):
            ordered=sorted(V);rec=encode_record(a,d,ordered[-1],ordered[0]);audit(rec);saved.append(rec)
        totals.update(counts);totals['square_systems']+=basis_count;totals['models']+=1;totals['vertices']+=len(V)
        models.append(dict(dimension=d,rows=m,vertices=len(V),**counts))
    for d,m in [(8,17),(16,33)]:
        a=list(map(Q,range(m)));r=m-d
        for h,k in [(tuple(range(r)),tuple(range(1,r+1))),
                    (tuple(range(m-r,m)),tuple(range(r)))]:
            S=tuple(i for i in range(m) if i not in h);T=tuple(i for i in range(m) if i not in k)
            rec=encode_record(a,d,S,T);res=audit(rec);saved.append(rec)
            large.append(dict(dimension=d,rows=m,bound=2*r+1,**res,full_graph_enumerated=False))
    constructors={mod:{name:getattr(mod,name) for name in names} for mod,names in
                  [(labels,['build']),(roots,['candidate','polynomial','square_solve'])]}
    def fail(*a,**k):raise AssertionError('construction during saved audit')
    try:
        for mod,fs in constructors.items():
            for name in fs:setattr(mod,name,fail)
        replay=[audit(c) for c in saved]
    finally:
        for mod,fs in constructors.items():
            for name,f in fs.items():setattr(mod,name,f)
    b=next(c for c in saved if c['dimension']>=2 and len(c['vertices'])>1);bad=[]
    for name,mut in [('infeasible point',lambda c:c['vertices'][0]['point'].__setitem__(0,'999')),
                     ('bad inverse',lambda c:c['vertices'][0]['inverse'][0].__setitem__(0,'999')),
                     ('missing tight row',lambda c:c['vertices'][0]['tight'].pop()),
                     ('missing endpoint',lambda c:c['vertices'].pop()),
                     ('reversed nodes',lambda c:c['a'].reverse()),
                     ('repeated nodes',lambda c:c['a'].__setitem__(0,c['a'][1]))]:
        c=deepcopy(b);mut(c)
        try:audit(c)
        except (ValueError,AssertionError,IndexError,ZeroDivisionError):bad.append(name)
        else:raise AssertionError('accepted forgery '+name)
    report=dict(status='PASS',totals=dict(totals),models=models,large=large,
                saved_replay=dict(records=len(saved),edges=sum(x['length'] for x in replay),constructors_disabled=True),
                rejected=bad,scope='Supporting rational tests and rank certificates, not Lean extraction or a new optimal diameter claim.')
    return report,saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);args=p.parse_args()
    report,records=run();report['sources']={name:hashlib.sha256(Path(mod.__file__).read_bytes()).hexdigest()
      for name,mod in [('selected_router',labels),('root_constructor',roots),('packing_router',labels.accepted)]}
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',records)]:
        (args.out/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report['totals'],sort_keys=True),flush=True)
if __name__=='__main__':main()
