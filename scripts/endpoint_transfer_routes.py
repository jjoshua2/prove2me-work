#!/usr/bin/env python3
"""Direct original-edge routes for positive coordinate-simplex sums.

Descending-target insertion moves each summand only from its source winner to
its target winner. All summands with the same ordered endpoint transfer move
in ONE entire exposed edge. The length is exactly the number of distinct
nonzero endpoint-transfer pairs, at most n*(n-1)//2. This is a classical braid-
fan class, not arbitrary-polytope recognition or a new universal Hirsch bound.

The H wrapper takes a connected building set and its positive rational weights
as a PRESENTATION. It checks the complete canonical original H-description;
it does not infer a hidden presentation from arbitrary inequalities. The last
coordinate is eliminated bijectively, not projected from an extension.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json
import simple_tangent_policy_audit as original


def require(ok, message):
    if not ok: raise ValueError(message)


def rat(x):
    require(type(x) in (int, str) or isinstance(x, Q), 'exact rational required')
    return Q(x)


def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: serial(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)): return [serial(v) for v in x]
    return x


def presentation(n, subsets, weights=None):
    require(type(n) is int and n >= 2, 'ground size must be an integer >=2')
    require(isinstance(subsets, (list, tuple)) and subsets, 'nonempty summand list required')
    S=[]
    for part in subsets:
        require(isinstance(part, (list, tuple)) and part and
                all(type(i) is int and 0 <= i < n for i in part) and
                list(part) == sorted(set(part)), 'invalid coordinate simplex')
        S.append(tuple(part))
    require(len(set(S)) == len(S), 'duplicate summand supports')
    w=tuple(Q(1) for _ in S) if weights is None else tuple(map(rat, weights))
    require(len(w) == len(S) and all(t > 0 for t in w), 'strictly positive summand weights required')
    return tuple(S), w


def permutation(p, n):
    require(isinstance(p, (list, tuple)) and len(p) == n and
            all(type(i) is int for i in p) and sorted(p) == list(range(n)), 'invalid coordinate order')
    return list(p)


def point(n, S, w, order):
    order=permutation(order, n); rank={i: j for j, i in enumerate(order)}
    picks=[max(T, key=rank.__getitem__) for T in S]; x=[Q(0)]*n
    for i, t in zip(picks, w): x[i]+=t
    return tuple(x), picks


def swaps(source, target):
    """Fix target coordinates from greatest to least; each inversion swaps once."""
    p=list(source)
    for k in range(len(p)-1, -1, -1):
        j=p.index(target[k])
        while j < k:
            before=p[:]; a,b=p[j:j+2]; p[j],p[j+1]=b,a
            yield before, j, p[:]
            j+=1
    require(p == list(target), 'insertion failed')


def wall(n, S, w, before, j):
    """Independently check the WHOLE exposed slice: each factor is a point or
    the same coordinate segment. No adjacency is inferred from projection."""
    before=permutation(before,n)
    require(type(j) is int and 0 <= j < n-1, 'bad adjacent wall')
    a,b=before[j:j+2]; c=[Q(0)]*n
    for k,i in enumerate(before): c[i]=Q(k)
    c[a]=c[b]=Q(2*j+1, 2)
    base=[Q(0)]*n; mass=Q(0); changed=[]
    for z,(T,t) in enumerate(zip(S,w)):
        best=max(c[i] for i in T); I=[i for i in T if c[i] == best]
        if len(I) == 1: base[I[0]]+=t
        else:
            require(set(I) == {a,b}, 'independent tie would expose more than an edge')
            mass+=t; changed.append(z)
    x=base[:]; y=base[:]; x[b]+=mass; y[a]+=mass
    after=before[:]; after[j],after[j+1]=b,a
    require(tuple(x) == point(n,S,w,before)[0] and tuple(y) == point(n,S,w,after)[0],
            'wall endpoints disagree with original sum')
    return {'pair':[b,a], 'mass':mass, 'summands':changed,
            'normal':c, 'from':x, 'to':y}


def build(n, subsets, weights, source_order, target_order):
    S,w=presentation(n,subsets,weights)
    source=permutation(source_order,n); target=permutation(target_order,n)
    x,_=point(n,S,w,source); path=[x]; steps=[]; stationary=0
    for before,j,after in swaps(source,target):
        record=wall(n,S,w,before,j)
        if record['mass']:
            steps.append({'order':before, 'position':j, 'transfer':record})
            path.append(tuple(record['to']))
        else: stationary+=1
    c=serial({'source_order':source,'target_order':target,'steps':steps,
              'stationary_swaps':stationary,'path':path})
    return {'certificate':c,'verified':verify(n,S,w,c)}


def verify(n, subsets, weights, c):
    S,w=presentation(n,subsets,weights)
    source=permutation(c['source_order'],n); target=permutation(c['target_order'],n)
    start,first=point(n,S,w,source); end,last=point(n,S,w,target)
    groups={}
    for i,j,t in zip(first,last,w):
        if i != j: groups[i,j]=groups.get((i,j),Q(0))+t
    path=[start]; observed=[]; step=stationary=0; current=first[:]; switches=[0]*len(S)
    for before,j,after in swaps(source,target):
        r=wall(n,S,w,before,j)
        if not r['mass']:
            stationary+=1; continue
        require(step < len(c['steps']), 'omitted nonstationary original edge')
        got=c['steps'][step]
        permutation(got['order'],n)
        require(type(got['position']) is int, 'noninteger wall position')
        require(got == serial({'order':before,'position':j,'transfer':r}), 'changed whole-wall certificate')
        u,v=r['pair']; require(groups.get((u,v)) == r['mass'], 'not an exact endpoint transfer group')
        for k in r['summands']:
            require(current[k] == first[k] == u and last[k] == v and switches[k] == 0,
                    'a factor uses an intermediate/nonendpoint choice')
            current[k]=v; switches[k]+=1
        require(tuple(r['from']) == path[-1], 'disconnected route')
        path.append(tuple(r['to'])); observed.append((u,v)); step+=1
    require(step == len(c['steps']) and len(observed) == len(set(observed)) and set(observed) == set(groups),
            'unrelated, repeated, or missing transfer')
    require(current == last and switches == [int(a != b) for a,b in zip(first,last)], 'incomplete factor transport')
    require(path[-1] == end and c['path'] == serial(path), 'wrong endpoints or route coordinates')
    require(type(c['stationary_swaps']) is int and stationary == c['stationary_swaps'], 'false stationary count')
    require(step == len(groups) <= n*(n-1)//2, 'endpoint-transfer budget failed')
    rank={i:j for j,i in enumerate(target)}
    require(all(sum(Q(rank[i])*(y[i]-x[i]) for i in range(n)) > 0
                for x,y in zip(path,path[1:])), 'target-order objective did not strictly increase')
    return {'status':'PASS','ground_size':n,'positive_summands':len(S),'original_edges':step,
            'distinct_endpoint_transfer_pairs':len(groups),'stationary_swaps':stationary,
            'all_pairs_edge_bound':n*(n-1)//2,'each_summand_switches_at_most_once':True,'strict_target_order_progress':True,
            'every_common_exposed_face_preserved':True,
            'globally_shortest_claimed':False,
            'scope':'Exact whole-sum exposed edges for a supplied positive coordinate-simplex presentation; no Lean verdict.'}


def building_H(n, subsets, weights=None):
    S,w=presentation(n,subsets,weights); masks=[sum(1<<i for i in T) for T in S]
    B=set(masks); full=(1<<n)-1
    require(full in B and all(1<<i in B for i in range(n)), 'connected building set needs all singletons and ground set')
    require(all(not(a&b) or (a|b) in B for a,b in combinations(masks,2)), 'building-set union condition fails')
    total=sum(w,Q(0)); A=[]; rhs=[]; labels=[]
    for T,mask in zip(S,masks):
        if mask == full: continue
        z=sum((t for U,t in zip(masks,w) if U&mask == U),Q(0))
        if n-1 not in T:
            A.append(tuple(-Q(i in T) for i in range(n-1))); rhs.append(-z)
        else:
            A.append(tuple(Q(i not in T) for i in range(n-1))); rhs.append(total-z)
        labels.append(list(T))
    return tuple(A),tuple(rhs),total,labels


def endpoint_order(n,A,b,total,x,packet):
    y,J,D=original.audit_basis(A,b,packet)
    require(tuple(y) == tuple(x), 'incorrect endpoint basis')
    normal=[sum((A[j][i] for j in J),Q(0)) for i in range(n-1)]+[Q(0)]
    return sorted(range(n),key=lambda i:(normal[i],i))


def original_audit(A,b,path,packets):
    require(len(packets) == len(path), 'missing original vertex basis')
    states=[]
    for x,p in zip(path,packets):
        y,J,D=original.audit_basis(A,b,p)
        require(tuple(y) == tuple(x), 'basis does not describe path vertex'); states.append((y,J,D))
    for (x,J,D),(y,H,_) in zip(states,states[1:]):
        released=set(J)-set(H); require(len(released) == 1 and len(set(J)&set(H)) == len(x)-1, 'not an original edge')
        ray=D[J.index(next(iter(released)))]; alpha,_=original.maximal_step(A,b,x,ray)
        require(alpha > 0 and tuple(a+alpha*v for a,v in zip(x,ray)) == tuple(y), 'not the maximal original endpoint')
    common=set(states[0][1]) & set(states[-1][1])
    require(all(common <= set(J) for _,J,_ in states), 'common original facet lost')
    return len(common)


def build_H(data):
    n=data['n']; S=data['subsets']; w=data.get('weights')
    A,b,total,_=building_H(n,S,w)
    require(A == tuple(tuple(map(rat,a)) for a in data['A']) and
            b == tuple(map(rat,data['b'])), 'H-description not bound to supplied building set')
    u=tuple(map(rat,data['start'])); v=tuple(map(rat,data['target']))
    pu=original.basis_packet(A,b,u); pv=original.basis_packet(A,b,v)
    source=endpoint_order(n,A,b,total,u,pu); target=endpoint_order(n,A,b,total,v,pv)
    built=build(n,S,w,source,target); path=[tuple(map(rat,x[:-1])) for x in built['certificate']['path']]
    require(path[0] == u and path[-1] == v, 'endpoint orders do not recover requested vertices')
    c={'route':built['certificate'],'bases':[serial(original.basis_packet(A,b,x)) for x in path]}
    return {'certificate':c,'verified':verify_H(data,c)}


def verify_H(data,c):
    n=data['n']; S=data['subsets']; w=data.get('weights'); A,b,total,_=building_H(n,S,w)
    suppliedA=tuple(tuple(map(rat,a)) for a in data['A']); suppliedb=tuple(map(rat,data['b']))
    require(A == suppliedA and b == suppliedb, 'changed canonical original H-system')
    info=verify(n,S,w,c['route']); path=[tuple(map(rat,x[:-1])) for x in c['route']['path']]
    require(path[0] == tuple(map(rat,data['start'])) and path[-1] == tuple(map(rat,data['target'])), 'requested endpoints changed')
    packets=[{'point':list(map(rat,p['point'])),'active':p['active'],
              'directions':[list(map(rat,a)) for a in p['directions']]} for p in c['bases']]
    shared=original_audit(A,b,path,packets)
    for x,p,name in [(path[0],packets[0],'source_order'),(path[-1],packets[-1],'target_order')]:
        require(c['route'][name] == endpoint_order(n,A,b,total,x,p), 'not the fixed endpoint-order choice')
    return {**info,'dimension':n-1,'genuine_original_facets':len(A),'common_original_facets_retained':shared,
            'whole_H_equality':'building-set support/summation-by-parts identity in the accompanying proof',
            'hidden_presentation_discovered':False,'global_original_graph_enumerated':False}


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('input',type=Path); p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    try:
        out=build_H(json.loads(args.input.read_text()))
        args.output.write_text(json.dumps(serial(out),indent=2)+'\n')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No certified endpoint-transfer route: {exc}\n')
if __name__ == '__main__': main()
