#!/usr/bin/env python3
"""Exact pivot, degeneracy and independently enumerated small-graph tests."""
from __future__ import annotations
from copy import deepcopy
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random,time
from network_potential_router import Network,UnionFind,construct,verify,recognize_rows,require,rat,serial
ROOT=Path(__file__).resolve().parents[1]


def solve(A,b):
    n=len(A);A=[list(r)+[v]for r,v in zip(A,b)]
    for j in range(n):
        k=next((i for i in range(j,n)if A[i][j]),None)
        if k is None:return None
        A[j],A[k]=A[k],A[j];t=A[j][j];A[j]=[v/t for v in A[j]]
        for i in range(n):
            if i!=j:
                t=A[i][j]
                if t:A[i]=[x-t*y for x,y in zip(A[i],A[j])]
    return tuple(r[-1]for r in A)


def vertices(nodes,arcs):
    d=nodes-1;points=set()
    A=[tuple(Q(int(j+1==b)-int(j+1==a))for j in range(d))for a,b,_ in arcs]
    for base in combinations(range(len(arcs)),d):
        x=solve([A[i]for i in base],[rat(arcs[i][2])for i in base])
        if x is None:continue
        x=(Q(0),)+x
        if all(x[b]-x[a]<=rat(c)for a,b,c in arcs):points.add(x)
    return sorted(points)


def graph(nodes,arcs,pts):
    acts=[{j for j,(a,b,c)in enumerate(arcs)if x[b]-x[a]==rat(c)}for x in pts];G=[set()for _ in pts]
    for a,b in combinations(range(len(pts)),2):
        uf=UnionFind(nodes)
        for j in acts[a]&acts[b]:u,v,_=arcs[j];uf.join(u,v)
        if len(set(uf.labels()))==2:G[a].add(b);G[b].add(a)
    return G,acts


def dist(G,source):
    D={source:0};q=deque([source])
    while q:
        a=q.popleft()
        for b in G[a]:
            if b not in D:D[b]=D[a]+1;q.append(b)
    return D


def spread(d,seed=None):
    rng=random.Random(seed);arcs=[]
    for i in range(1,d+1):arcs.extend([[i,0,Q(0)],[0,i,Q(1)]])
    for i in range(1,d+1):
        for j in range(1,d+1):
            if i!=j:
                c=Q(2,3)+(Q(rng.randrange(-1000,1001),1000000)if seed is not None else 0)
                arcs.append([i,j,c])
    return {'nodes':d+1,'arcs':arcs,'source':[0]*(d+1),'target':[0]+[1]*d}


def random_network(d,seed,integer=False):
    rng=random.Random(seed);potential=[Q(0)]+[Q(rng.randrange(-6,7),3)for _ in range(d)]
    arcs=[]
    for i in range(d+1):
        for j in range(d+1):
            if i!=j:
                c=Q(rng.randrange(1,8))if integer else Q(rng.randrange(1,1000),rng.randrange(2,17))
                arcs.append([i,j,c+potential[j]-potential[i]])
    def endpoint(r):
        D=[None]*(d+1);D[r]=Q(0)
        for _ in range(d):
            for a,b,c in arcs:
                if D[a]is not None and(D[b]is None or D[a]+c<D[b]):D[b]=D[a]+c
        require(all(t is not None for t in D),'random graph disconnected')
        return [t-D[0]for t in D]
    return {'nodes':d+1,'arcs':arcs,'source':endpoint(0),'target':endpoint(d)}


def main():
    start=time.monotonic();counts={'models':0,'small_pairs':0,'vertices':0,'edges':0,'distance_checks':0,
        'ordinary_edge_occurrences':0,'zero_pivots':0,'terminal_basis_exchanges':0,'nonsimple_endpoint_pairs':0}
    models=[];large=[]
    cases=[('spread'+str(d),spread(d))for d in (2,3,4)]
    cases += [('perturbed'+str(s),spread(3,s))for s in (1,7,19)]
    cases += [('random'+str(s),random_network(3,s,integer=(s%2==0)))for s in (3,4,6)]
    saved=None
    for name,data in cases:
        pts=vertices(data['nodes'],data['arcs']);G,acts=graph(data['nodes'],data['arcs'],pts)
        require(pts,'no independently enumerated vertices');d=data['nodes']-1
        counts['models']+=1;counts['vertices']+=len(pts);counts['edges']+=sum(map(len,G))//2
        pairs=0;maxlen=0;zero=0
        for i,x in enumerate(pts):
            D=dist(G,i);require(len(D)==len(pts),'enumerated graph disconnected');counts['distance_checks']+=len(D)
            for j,y in enumerate(pts[:i]):
                problem={**data,'source':x,'target':y};result=construct(problem);got=result['verified'];pairs+=1
                rr=[tuple(map(rat,z))for z in got['route']]
                ids=[pts.index(z)for z in rr]
                require(all(b in G[a]for a,b in zip(ids,ids[1:])),'not edge of independent full graph')
                require(got['ordinary_edges']>=D[j],'route shorter than exact graph distance')
                counts['ordinary_edge_occurrences']+=got['ordinary_edges'];counts['zero_pivots']+=got['zero_pivots']
                counts['terminal_basis_exchanges']+=got['terminal_basis_exchanges'];zero+=got['zero_pivots']
                counts['nonsimple_endpoint_pairs']+=int(len(acts[i])>d or len(acts[j])>d)
                maxlen=max(maxlen,got['ordinary_edges'])
                if saved is None and got['zero_pivots'] and got['carrier_dimension']>1:saved=(problem,result['certificate'])
        counts['small_pairs']+=pairs
        models.append({'name':name,'nodes':data['nodes'],'rows':len(data['arcs']),'vertices':len(pts),
                       'pairs':pairs,'max_route_length':maxlen,'zero_pivots':zero})
        print(models[-1],flush=True)
    # Sparse, redundant/parallel, and unbounded descriptions are accepted; not
    # silently simplified away in the pivot certificates.
    boundary=[]
    data={'nodes':3,'arcs':[[0,1,1],[1,2,1],[0,2,1],[1,0,0]],'source':[0,0,1],'target':[0,1,1]}
    for name,dd in [('unbounded',data),('same_point',spread(3)),('singleton',{'nodes':1,'arcs':[],'source':[0],'target':[0]})]:
        dd=deepcopy(dd)
        if name=='same_point':dd['target']=dd['source']
        res=construct(dd);boundary.append({'name':name,**{k:v for k,v in res['verified'].items()if k not in ('route','phases')}})
    data=spread(3);data['arcs']+=deepcopy(data['arcs'][:2])+[[0,1,Q(2)]]
    res=construct(data);boundary.append({'name':'duplicate_and_redundant',**{k:v for k,v in res['verified'].items()if k not in ('route','phases')}})
    # No all-vertex enumeration, no summand representation.
    for name,data in [('spread24',spread(24)),('perturbed24',spread(24,91)),('perturbed50',spread(50,92)),
                     ('dense16',random_network(16,27)),('dense32',random_network(32,29,True))]:
        result=construct(data);got=result['verified']
        large.append({'name':name,'nodes':data['nodes'],'rows':len(data['arcs']),
                      **{k:v for k,v in got.items()if k not in ('route','phases','scope','status')}})
        (ROOT/'fixtures'/f'{name}_input.json').write_text(json.dumps(serial(data),separators=(',',':'))+'\n')
        (ROOT/'fixtures'/f'{name}_certificate.json').write_text(json.dumps(result['certificate'],separators=(',',':'))+'\n')
        print(large[-1],flush=True)
    # All recognized rows are retained with their exact positive scaling.
    H=spread(4,12);A=[];rhs=[]
    for k,(a,b,c)in enumerate(H['arcs']):
        scale=Q(k%7+1,k%3+1)
        A.append([scale*(int(i+1==b)-int(i+1==a))for i in range(4)]);rhs.append(scale*c)
    hh={'A':A,'b':rhs,'source':H['source'][1:],'target':H['target'][1:]};nn,scales=recognize_rows(hh)
    require(nn['arcs']==H['arcs'],'scaled H recognition changed inequalities');construct(nn)
    # Finite invalid-certificate controls. Descriptive counters are recalculated,
    # so forged summaries have no bearing on proof acceptance.
    rejected=[]
    def reject(name,f):
        try:f()
        except(ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise AssertionError('accepted '+name)
    require(saved is not None,'tests did not exercise zero pivots')
    p,c=saved
    for key,value in [('source',[0]*p['nodes']),('target',[1]*p['nodes']),('nodes',True)]:
        bad=deepcopy(p);bad[key]=value;reject('changed_'+key,lambda bad=bad:verify(bad,c))
    bad=deepcopy(p);bad['arcs'][0][2]=0.1;reject('floating_input',lambda:Network(bad))
    for key,value in [('input_sha256','0'*64),('start_tree',[]),('target_tree',[]),('phases',[])]:
        bad=deepcopy(c);bad[key]=value;reject('forged_'+key,lambda bad=bad:verify(p,bad))
    phase=next(i for i,x in enumerate(c['phases'])if x['pivots'])
    for key,value in [('leave',999999),('enter',999999),('step','-1'),('moving_nodes',[])]:
        bad=deepcopy(c);bad['phases'][phase]['pivots'][0][key]=value
        reject('false_'+key,lambda bad=bad:verify(p,bad))
    bad=deepcopy(c);bad['phases'][phase]['pivots']*=2;reject('repeated_pivot',lambda:verify(p,bad))
    bad=deepcopy(c);bad['phases'][phase]['final_exchange']=999999;reject('invalid_terminal_exchange',lambda:verify(p,bad))
    bad=deepcopy(hh);bad['A'][0]=[1,1,0,0];reject('signed_nonnetwork_row',lambda:recognize_rows(bad))
    bad=deepcopy(hh);bad['A'][0]=[1,-2,0,0];reject('unbalanced_gain_row',lambda:recognize_rows(bad))
    # A circuit jump in a cube is not generally a polytope edge.
    cube={'nodes':4,'arcs':[[i,0,0]for i in range(1,4)]+[[0,i,1]for i in range(1,4)],'source':[0,0,0,0],'target':[0,1,1,1]}
    pp=Network(cube);both=pp.active(pp.start)&pp.active(pp.target)
    require(len(set(pp.labels(both)))==4,'cube diagonal false-edge test')
    summary={'status':'PASS','scope':'Exact rational H/network certificate tests, not Lean or Prove2Me acceptance.',
        **counts,'small_models':models,'large_models':large,'boundary_models':boundary,
        'scaled_H_recognition_rows':len(A),'negative_controls_rejected':len(rejected),'negative_controls':rejected,
        'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                         for folder,ext in [('scripts','*.py'),('Solutions','*.lean')]
                         for p in sorted((ROOT/folder).glob(ext))},'elapsed_seconds':round(time.monotonic()-start,3)}
    (ROOT/'research/NETWORK_PIVOT_CHECK_2026-09-12.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
