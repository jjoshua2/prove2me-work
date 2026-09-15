#!/usr/bin/env python3
"""Realize arbitrary higher-defect kernels and certify unavoidable energy debt.

The classical nestohedron construction is used, not claimed invented here.
The input is a complete simplicial-complex minimal-nonface catalogue on n
labels; the realization enumerates 2**n subsets and is explicitly capped.
It is a simple bounded ORIGINAL H-polytope, not an extension whose edges are
silently projected. Its only higher minimal nonfaces are the input higher ones.

The first-original-pair counting certificate for a Steiner triple system proves
an unavoidable energy peak in ANY edge-stellar flagification, not just in a
bounded search or chosen rule. A separate exact Fano trace attains that peak.
Python and the classical imported face theorem are not Lean verification.
"""
from __future__ import annotations
from itertools import combinations, permutations
from math import comb, factorial
from fractions import Fraction as Q
from collections import deque
import argparse, json
from pathlib import Path
import stellar_defect_budget as S
import simple_tangent_policy_audit as H

require = S.require


def steiner_binary(r):
    require(type(r) is int and 3 <= r <= 5, 'binary design rank outside explicit cap')
    n = 2**r-1
    triples = {frozenset((a-1,b-1,(a^b)-1)) for a in range(1,n+1)
               for b in range(a+1,n+1)}
    return S.Complex.create(n,S.lists(triples))


def barrier_certificate(K):
    """A finite design certificate for the general first-original-pair proof.
    Completeness here is the exact original induced complex, not a sample.
    """
    n = K.n
    require(n >= 7 and all(len(N)==3 for N in K.missing), 'pure triple catalogue required')
    require(all(sum(set(E)<=N for N in K.missing)==1 for E in combinations(range(n),2)),
            'every original pair must belong to exactly one triple')
    q = len(K.missing)
    require(q*6==n*(n-1), 'design triple count')
    records = []
    for E in combinations(range(n),2):
        E=frozenset(E)
        common = [N for N in K.missing if E<=N]
        mixed = [N for N in K.missing if len(E&N)==1]
        residues = [N-E for N in mixed]
        require(len(mixed)==n-3 and len(set(residues))==n-3, 'distinct forced descendants')
        require(all(not(common[0]-E)<=R for R in residues), 'shared third label wrongly blocks a descendant')
        require(all(len(R)==2 and not any(M-E<R for M in K.missing if M&E)
                    for R in residues), 'forced descendant is not minimal')
        records.append({'edge':sorted(E),'consumed_original':sorted(common[0]),
                        'forced_residues':S.lists(residues)})
    return {'format':'steiner-first-original-edge-v1','input_sha256':S.fingerprint(K),
            'ground_labels':n,'initial_weight':q,'required_peak':q+n-4,
            'required_excess':n-4,'first_edge_cases':records,
            'scope':'Counting theorem applies after ANY preceding auxiliary subdivisions, not only direct first moves.'}


def verify_barrier(K,c):
    require(c==barrier_certificate(K),'incorrect complete first-original-edge certificate')
    return {'status':'PASS','initial_weight':c['initial_weight'],
            'unavoidable_peak':c['required_peak'],'unavoidable_excess':c['required_excess'],
            'all_original_pairs_checked':len(c['first_edge_cases'])}


def realize(K, subset_cap=100000, facet_pair_cap=250000):
    """B = all singletons and all nonfaces. No empty/full-simplex shortcuts."""
    require(K.missing and K.n>=3,'proper complex with all actual vertices required')
    require(type(subset_cap)is int and 2**K.n<=subset_cap,'building-set subset cap')
    n=K.n; ground=frozenset(range(n))
    B=[frozenset([i]) for i in range(n)]
    B += [frozenset(T) for size in range(2,n+1) for T in combinations(range(n),size)
          if not K.face(T)]
    require(B[-1]==ground,'connected building set requires the full ground set')
    labels=B[:-1]; total=len(B)
    require(type(facet_pair_cap)is int and comb(len(labels),2)<=facet_pair_cap,
            'facet-pair catalogue cap; no partial realization returned')
    # Each row is an ORIGINAL facet after eliminating x_(n-1)=total-sum(x_i).
    A=[]; b=[]
    for T in labels:
        h=sum(U<=T for U in B)
        if n-1 in T:
            A.append([int(i not in T) for i in range(n-1)]);b.append(total-h)
        else:
            A.append([-int(i in T) for i in range(n-1)]);b.append(-h)
    pairs=[]
    for i,j in combinations(range(len(labels)),2):
        U,V=labels[i],labels[j]
        compatible=U<=V or V<=U or (not(U&V) and K.face(U|V))
        if not compatible:pairs.append([i,j])
    dual=S.Complex.create(len(labels),pairs+S.lists(K.higher()))
    return {'ground_n':n,'A':A,'b':b,'building_set':[sorted(T) for T in B],
            'facet_labels':[sorted(T) for T in labels],'total_coordinate_sum':total,
            'dual':dual.payload(),'original_kernel':K.payload()}


def greedy(model, order):
    n=model['ground_n'];require(isinstance(order,(tuple,list)) and all(type(i)is int for i in order) and
                              sorted(order)==list(range(n)),'not an exact full coordinate order')
    rank={i:j for j,i in enumerate(order)};x=[0]*n
    for T in model['building_set']:x[max(T,key=rank.__getitem__)]+=1
    return tuple(x[:-1])


def ordered_vertices(model, permutation_cap=100000):
    """All generic objective orders, not alleged vertex completeness from samples."""
    n=model['ground_n'];require(factorial(n)<=permutation_cap,'full-order cap')
    vertices={}
    for order in permutations(range(n)):
        x=greedy(model,order)
        vertices.setdefault(x,order)
    return vertices


def expected_facet(model,order):
    """Independent prefix description of nested facets in this upward building set."""
    index={frozenset(T):i for i,T in enumerate(model['facet_labels'])}
    K=S.Complex.create(model['original_kernel']['vertices'],model['original_kernel']['minimal_nonfaces'])
    prefix=frozenset();face=set();started=False
    for i,v in enumerate(order):
        prefix=prefix|{v}
        if not started and K.face(prefix):face.add(v)
        else:
            started=True
            if i+1<len(order):face.add(index[prefix])
    require(len(face)==len(order)-1,'wrong nested-facet size')
    return frozenset(face)


def fano_refinement(dual):
    """Eleven explicit subdivisions; minimum possible peak, not minimum length."""
    require(dual.higher()==steiner_binary(3).higher(),'not the exact seven-label Fano kernel')
    word=[(0,1),(3,7),(6,7),(3,6),(0,10),(1,10),(0,3),(0,6),(1,3),(1,6),(2,4)]
    initial=dual;steps=[];weights=[dual.weight()];offset=dual.n-7
    for edge in word:
        E=[v if v<7 else v+offset for v in edge]
        dual,c=S.account(dual,E);steps.append(c);weights.append(dual.weight())
    require(weights==[7,10,8,6,9,7,5,4,3,2,1,0], 'Fano witness weight path changed')
    require(not dual.higher(),'Fano completion is not flag')
    packet={'format':'fano-minimax-refinement-v1','input_sha256':S.fingerprint(initial),
            'steps':steps,'terminal':dual.payload(),'peak':max(weights),'weights':weights}
    verify_refinement(initial,packet)
    return packet


def verify_refinement(K,c):
    require(c['format']=='fano-minimax-refinement-v1' and c['input_sha256']==S.fingerprint(K),
            'changed original complex')
    require(K.higher()==steiner_binary(3).higher(),'not the original Fano higher list')
    initial_n=K.n;weights=[K.weight()]
    for p in c['steps']:
        K,actual=S.account(K,p['edge'])
        require(actual==p,'forged stellar update')
        weights.append(K.weight())
    require(c['weights']==weights and c['peak']==max(weights),'false energy trajectory')
    require(K.payload()==c['terminal'] and not K.higher(),'incomplete flagification')
    require(c['peak']==10,'does not attain the first-original-pair lower bound')
    return {'status':'PASS','stellar_steps':len(c['steps']),'initial_vertices':initial_n,
            'refined_vertices':K.n,'minimum_possible_peak':10,'minimum_peak_attained':True,
            'not_claimed_minimum_number_of_steps':True}


def sorting_route(model,start_order,end_order):
    """Classical braid-chamber walk, no global graph supplied to the producer."""
    n=model['ground_n'];greedy(model,start_order);greedy(model,end_order)
    order=list(start_order);path=[greedy(model,order)];orders=[list(order)];stationary=0
    for target_pos,v in enumerate(end_order):
        position=order.index(v)
        while position>target_pos:
            order[position-1],order[position]=order[position],order[position-1]
            z=greedy(model,order);orders.append(list(order))
            if z!=path[-1]:path.append(z)
            else:stationary+=1
            position-=1
    require(path[-1]==greedy(model,end_order) and len(orders)-1<=comb(n,2),'sorting bound/endpoints')
    return {'orders':orders,'path':path,'swaps':len(orders)-1,'stationary_swaps':stationary,
            'all_pair_bound':comb(n,2),'scope':'Classical generalized-permutohedron route, not a new universal diameter theorem.'}


def audit_original_edge(A,b,from_packet,to_packet):
    x,J,D=H.audit_basis(A,b,from_packet);y,L,_=H.audit_basis(A,b,to_packet)
    require(len(set(J)-set(L))==len(set(L)-set(J))==1,'not a single original facet exchange')
    j=J.index(next(iter(set(J)-set(L))));length,blocker=H.maximal_step(A,b,x,D[j])
    require(length>0 and [a+length*v for a,v in zip(x,D[j])]==y,'not a maximal original edge')
    return {'length':length,'blocker':blocker}


def audit_sorting(model,c,packets):
    require(c['orders'],'empty order path')
    path=[greedy(model,c['orders'][0])];stationary=0
    for u,v in zip(c['orders'],c['orders'][1:]):
        change=[i for i,(a,b) in enumerate(zip(u,v)) if a!=b]
        require(len(change)==2 and change[1]==change[0]+1 and
                u[change[0]]==v[change[1]] and u[change[1]]==v[change[0]],'not adjacent order swap')
        x=greedy(model,v)
        if x==path[-1]:stationary+=1
        else:
            audit_original_edge(model['A'],model['b'],packets[path[-1]],packets[x]);path.append(x)
    require(path==list(map(tuple,c['path'])) and stationary==c['stationary_swaps'] and
            len(c['orders'])-1==c['swaps']<=comb(model['ground_n'],2),'false sorting route')
    return {'status':'PASS','edges':len(path)-1,'stationary_swaps':stationary}


def audit_saved(c):
    """Reconstruct the small model and audit saved certificates without LP,
    inverse computation, order enumeration, refined graph generation or BFS.
    The classical realization theorem remains a mathematical dependency.
    """
    model=c['model'];raw=model['original_kernel']
    K=S.Complex.create(raw['vertices'],raw['minimal_nonfaces'])
    require(model==realize(K),'saved original H-realization changed')
    verify_barrier(K,c['barrier'])
    dual=S.Complex.create(model['dual']['vertices'],model['dual']['minimal_nonfaces'])
    refined=verify_refinement(dual,c['refinement']);A,b=model['A'],model['b'];d=len(A[0])
    anchors=c['genuine_facet_points']
    require(len(anchors)==len(A),'incomplete facet witnesses')
    for i,raw in enumerate(anchors):
        x=list(map(H.rat,raw))
        require(len(x)==d and H.feasible(A,b,x) and H.active_rows(A,b,x)==[i],
                'false relative-interior facet witness')
    interior=list(map(H.rat,c['strict_interior_point']))
    require(len(interior)==d and all(H.dot(a,interior)<z for a,z in zip(A,b)),
            'no strict original interior')
    packets={};by_face={}
    for raw in c['route_vertex_bases']:
        p={'point':list(map(H.rat,raw['point'])),'active':raw['active'],
           'directions':[list(map(H.rat,r)) for r in raw['directions']]}
        x,F,_=H.audit_basis(A,b,p);key=tuple(x)
        require(key not in packets and frozenset(F) not in by_face,'duplicate basis')
        packets[key]=p;by_face[frozenset(F)]=p
    counts={'saved_pairs':0,'sorting_edges':0,'carrier_edges':0}
    for row in c['route_examples']:
        start=tuple(map(H.rat,row['start']));target=tuple(map(H.rat,row['target']))
        coarse=S.transport(dual,c['refinement']['steps'],row['ordered_refined_path'],d)
        require([sorted(F) for F in coarse]==row['original_path'],'wrong original carriers')
        require(tuple(by_face[coarse[0]]['point'])==start and
                tuple(by_face[coarse[-1]]['point'])==target,'carrier endpoints changed')
        common=coarse[0]&coarse[-1]
        require(all(common<=F for F in coarse),'common original facet lost')
        for F,T in zip(coarse,coarse[1:]):audit_original_edge(A,b,by_face[F],by_face[T])
        info=audit_sorting(model,row['sorting'],packets)
        require(tuple(row['sorting']['path'][0])==start and
                tuple(row['sorting']['path'][-1])==target,'sorting endpoints changed')
        counts['saved_pairs']+=1;counts['sorting_edges']+=info['edges'];counts['carrier_edges']+=len(coarse)-1
    return {'status':'PASS',**refined,**counts,'verified_original_facets':len(A),
            'graph_diameter_field_recomputed':False,
            'scope':'Set-identity and original-edge replay only; not a Lean or global graph-diameter audit.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--rank',type=int,default=3)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--realize',action='store_true')
    a=p.parse_args();K=steiner_binary(a.rank);out={'kernel':K.payload(),'barrier':barrier_certificate(K)}
    if a.realize:
        out['polytope']=realize(K)
        if a.rank==3:
            dual=out['polytope']['dual'];out['refinement']=fano_refinement(S.Complex.create(dual['vertices'],dual['minimal_nonfaces']))
    a.output.write_text(json.dumps(H.serial(out),indent=2)+'\n')
if __name__=='__main__':main()
