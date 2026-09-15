#!/usr/bin/env python3
"""Independent finite-complex identities and exact original-H route tests.

Small reference graphs are rebuilt independently. The main algorithm receives
only A,b,endpoints and optional blocks, not these graphs or face inventories.
Abstract exhaustive tests distinguish the exact TWO-block condition from the
stronger unnecessary condition that each defect lie inside one block.
"""
from __future__ import annotations
from itertools import combinations, permutations, product
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random, time
import defect_block_routes as new
import original_facet_segments as raw
import test_two_face_acquisition as ref
import two_face_acquisition as two

ROOT=Path(__file__).resolve().parents[1]
require=raw.require


def powers(S):
    return [frozenset(C) for r in range(len(S)+1) for C in combinations(sorted(S),r)]


def all_partitions(S):
    if not S:yield [];return
    a,*rest=sorted(S)
    for p in all_partitions(rest):
        yield [frozenset([a])]+p
        for j in range(len(p)):yield p[:j]+[p[j]|{a}]+p[j+1:]


def facets(K):
    return [F for F in K if not any(F<G for G in K)]


def maxcliques(G):
    out=[]
    def recurse(R,P,X):
        if not P and not X:out.append(frozenset(R));return
        v=max(P|X,key=lambda u:len(P&G[u])) if P|X else None
        for u in sorted(P-(G[v] if v is not None else set())):
            recurse(R|{u},P&G[u],X&G[u]);P.remove(u);X.add(u)
    recurse(set(),set(G),set());return out


def explicit_subdivision(K,blocks):
    """Independent construction by joined barycentric triangulations of each
    original maximal simplex, not the production oracle's pairwise test."""
    registry=[]
    for B in blocks:registry.extend(sorted([S for S in K if S and S<=B],key=lambda S:(len(S),tuple(sorted(S)))))
    index={S:i for i,S in enumerate(registry)};F=[]
    for U in facets(K):
        choices=[]
        for B in blocks:
            chains=[]
            for order in permutations(sorted(U&B)):
                chain=[];prefix=frozenset()
                for j in order:prefix=prefix|{j};chain.append(index[prefix])
                chains.append(frozenset(chain))
            choices.append(chains)
        for c in product(*choices):F.append(frozenset().union(*c))
    F=list(set(F));G={i:set() for i in range(len(registry))}
    for C in F:
        for i,j in combinations(C,2):G[i].add(j);G[j].add(i)
    return registry,F,G


def abstract_stage():
    # Every downward-closed complex on four fixed vertices, with all four present.
    U=set(range(4));other=[S for S in powers(U) if len(S)>=2];complexes=set()
    for mask in range(1<<len(other)):
        K={frozenset()};K.update(frozenset([v]) for v in U)
        for j,S in enumerate(other):
            if mask>>j&1:K.update(powers(S))
        complexes.add(frozenset(K))
    count=projection=passing=0
    for K in complexes:
        missing=[S for S in powers(U) if S not in K and all(S-{v} in K for v in S)]
        for blocks in all_partitions(U):
            blocks=sorted(blocks,key=lambda B:tuple(sorted(B)))
            reg,F,G=explicit_subdivision(K,blocks)
            flag=all(any(C<=D for D in F) for C in maxcliques(G))
            condition=all(sum(bool(W&B) for B in blocks)<=2 for W in missing)
            require(flag==condition,'two-block criterion fails on a complete abstract complex')
            count+=1;passing+=flag
            # Full-dimensional adjacency transport is checked without coordinates.
            sizes={len(C) for C in facets(K)}
            if len(sizes)==1:
                d=next(iter(sizes))
                for X,Y in combinations(F,2):
                    if len(X&Y)==d-1:
                        a=frozenset().union(*(reg[i] for i in X));b=frozenset().union(*(reg[i] for i in Y))
                        require(a==b or len(a&b)==d-1,'a refined ridge projected to a chord')
                        projection+=1
    # A single large minimal nonface forces <=2 blocks; the balanced minimum
    # is exponential even though the original simplex graph has diameter one.
    simplex=[]
    for m in range(3,17):
        lo=m//2;hi=m-lo;M=2**lo+2**hi-2
        simplex.append({'original_facets':m,'dimension':m-1,'best_partition_refined_vertices':M,
                        'resulting_bound':M-(m-1),'original_diameter':1})
    return {'complexes_on_four_vertices':len(complexes),'partition_checks':count,
        'flag_partitions':passing,'independent_adjacent_carrier_checks':projection,
        'simplex_partition_barrier':simplex}


def simplexd(d):
    return [[-int(i==j) for j in range(d)] for i in range(d)]+[[1]*d],[0]*d+[1]


def triangle_chain(r,cuts=True):
    d=2*r;A=[[-int(j==i) for j in range(d)] for i in range(d)];b=[Q(0)]*d
    for i in range(r):A.append([int(j//2==i) for j in range(d)]);b.append(Q(1))
    if cuts:
        for i in range(r-1):
            A.append([int(j//2 in (i,i+1)) for j in range(d)]);b.append(2-Q(1,10**(i+1)))
    return A,b


def models():
    D={name:ref.models()[name] for name in ['moment_3_6','moment_4_7','clipped_cube_3','holdout_moment_4_9']}
    D['tetrahedron']=simplexd(3);D['triangle_product']=triangle_chain(2,False)
    D['coupled_triangles']=triangle_chain(2,True)
    return D


def distances(G,s):
    D={s:0};queue=deque([s])
    while queue:
        x=queue.popleft()
        for y in G[x]:
            if y not in D:D[y]=D[x]+1;queue.append(y)
    return D


def graph_stage(name):
    begin=time.monotonic();A,b=models()[name];V,G,_=ref.reference(A,b);vs=list(V);d=len(A[0]);m=len(A)
    K={frozenset(S) for F in V.values() for S in powers(F)}
    true_missing=[S for S in powers(range(m)) if S not in K and all(S-{v} in K for v in S)]
    pairs=list(combinations(vs,2))
    if len(pairs)>90:random.Random(269+len(A)).shuffle(pairs);pairs=pairs[:90]
    totals={k:0 for k in ['routes','refined_edges','stationary','original_edges','raw_edges','two_face_edges','shortest',
        'new_nonshortest','raw_nonshortest','original_reentries','original_intersection_checks']}
    tables=[];prototype=None;refined_checks=0
    for u,v in pairs:
        data={'A':A,'b':b,'start':u,'target':v};out=new.run(data);c=out['certificate'];r=out['verified']
        require(set(map(frozenset,c['minimal_nonfaces']))==set(true_missing),'H classification not independently complete')
        if prototype is None:
            prototype=r
            # Independently enumerate the refined graph once per small model.
            reg,F,GG=explicit_subdivision(K,list(map(frozenset,c['blocks'])))
            require([sorted(S) for S in reg]==c['refined_vertices'],'different refinement registry')
            require(all(any(C<=B for B in F) for C in maxcliques(GG)),'refinement is not flag')
            require(len(reg)==r['refined_vertex_count'],'false vertex budget')
            refset=set(F)
        pp=list(map(frozenset,c['refined_path']));require(all(F in refset for F in pp),'not an independent refined facet')
        require(all(len(F&H)==d-1 for F,H in zip(pp,pp[1:])),'not an independent refined ridge path')
        refined_checks+=len(pp)-1
        path=[tuple(map(raw.rat,p['point'])) for p in c['vertices']]
        lookup={frozenset(V[x]):x for x in V};original=[lookup[frozenset(F)] for F in c['path']]
        require(original[0]==u and original[-1]==v and all(y in G[x] for x,y in zip(original,original[1:])),'not an independent ORIGINAL edge path')
        shortest=distances(G,u)[v];before=raw.construct(data,diagnose=0)['verified'];twoout=two.construct(A,b,u,v)['verified']
        for key,val in [('routes',1),('refined_edges',r['refined_edges']),('stationary',r['stationary_carrier_steps']),
                        ('original_edges',r['original_edges']),('raw_edges',before['original_edges']),
                        ('two_face_edges',twoout['committed_edges']),('shortest',shortest),
                        ('new_nonshortest',r['original_edges']>shortest),('raw_nonshortest',before['original_edges']>shortest),
                        ('original_reentries',r['original_reentry_debt']),('original_intersection_checks',len(c['intersections']))]:totals[key]+=val
        tables.append({'start':u,'target':v,'new':r['original_edges'],'refined':r['refined_edges'],'raw':before['original_edges'],
                       'two_face':twoout['committed_edges'],'shortest':shortest})
        if len(tables)==1:dump(ROOT/f'fixtures/defect_blocks_{name}.json',{'input':data,**out})
    dump(ROOT/f'research/DEFECT_PAIRS_{name}.json',tables)
    return {'name':name,'vertices':len(V),'edges':sum(map(len,G.values()))//2,
        'pair_sampling':'all unordered distinct pairs' if len(pairs)==len(vs)*(len(vs)-1)//2 else 'deterministic 90 pairs',
        'totals':totals,'structure':prototype,'independent_refined_edge_checks':refined_checks,
        'seconds':round(time.monotonic()-begin,3)}


def family_stage():
    records=[]
    for r in [2,3,4]:
        A,b=triangle_chain(r);d=2*r;target=[];u=Q(1)
        for i in range(r):
            if i:u=min(Q(1),2-Q(1,10**i)-u)
            target.extend([u,0])
        data={'A':A,'b':b,'start':[0]*d,'target':target};begin=time.monotonic();out=new.run(data);info=out['verified']
        require(info['refined_vertex_count']==5*r-1 and info['diameter_bound']==3*r-1,'coupled chain block budget changed')
        require(info['max_block_size']==2,'chain did not stay in matching blocks')
        # Independent complete original vertices via the known geometric
        # truncation history; NO such history is passed to the route producer.
        Fs=[frozenset().union(*(frozenset(C) for C in choice)) for choice in product(*[
            list(combinations([2*i,2*i+1,2*r+i],2)) for i in range(r)])]
        for i in range(r-1):
            a,c=2*r+i,2*r+i+1;newlabel=3*r+i;nextF=[]
            for F in Fs:
                if {a,c}<=F:nextF.extend([(F-{a})|{newlabel},(F-{c})|{newlabel}])
                else:nextF.append(F)
            Fs=nextF
        V={}
        for F in Fs:
            inv=raw.basis.invert([A[i] for i in sorted(F)])
            x=tuple(raw.dot(row,[b[i] for i in sorted(F)]) for row in inv)
            packet=raw.basis.basis_packet(A,b,x);require(frozenset(packet['active'])==F,'stellarly derived vertex not simple/feasible')
            V[x]=F
        G={x:set() for x in V}
        for x,F in V.items():
            p=raw.basis.basis_packet(A,b,x)
            for ray in p['directions']:
                t,_=raw.basis.maximal_step(A,b,x,ray);y=tuple(a+t*v for a,v in zip(x,ray))
                require(y in V,'independent truncation graph omitted original neighbor');G[x].add(y)
        require(len(distances(G,next(iter(V))))==len(V),'independent graph disconnected')
        # Closed neighbors + connected polytope graph establishes completeness.
        path={frozenset(F):x for x,F in V.items()};PP=[path[frozenset(F)] for F in out['certificate']['path']]
        require(all(y in G[x] for x,y in zip(PP,PP[1:])),'coupled family route not an original edge')
        rec={'triangle_factors_before_cuts':r,**info,'independent_vertices':len(V),'independent_edges':sum(map(len,G.values()))//2,
            'independent_distance':distances(G,tuple(data['start']))[tuple(target)],
            'history_passed_to_producer':False,'seconds':round(time.monotonic()-begin,3)}
        records.append(rec);dump(ROOT/f'fixtures/defect_coupled_{r}.json',{'input':data,**out,'independent':rec})
    return records


def negative_stage():
    A,b=triangle_chain(2);data={'A':A,'b':b,'start':[0]*4,'target':[1,0,Q(9,10),0]};out=new.run(data);good=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted invalid '+name)
    for field,value in [('problem_sha256','wrong'),('format','wrong'),('minimal_nonfaces',[]),('blocks',[[i] for i in range(len(A))])]:
        c=deepcopy(good);c[field]=value;reject(field,lambda c=c:new.verify(data,c))
    c=deepcopy(good);c['refined_vertices'].pop();reject('missing_refined_vertex',lambda:new.verify(data,c))
    c=deepcopy(good);c['refined_path']=c['refined_path'][1:];reject('wrong_refined_start',lambda:new.verify(data,c))
    c=deepcopy(good);c['path']=[c['path'][0],c['path'][-1]];reject('carrier_diagonal',lambda:new.verify(data,c))
    c=deepcopy(good);c['vertices'][0]['directions'][0][0]='99';reject('false_original_inverse',lambda:new.verify(data,c))
    c=deepcopy(good);c['boundedness'].pop();reject('missing_boundedness',lambda:new.verify(data,c))
    c=deepcopy(good);c['intersections'].pop(0);reject('omitted_classification_answer',lambda:new.verify(data,c))
    c=deepcopy(good);next(x for x in c['intersections'] if x['kind']=='absent')['bound']='999';reject('false_empty_face_bound',lambda:new.verify(data,c))
    c=deepcopy(good);next(x for x in c['intersections'] if x['kind']=='present')['point']=['99']*4;reject('false_present_face',lambda:new.verify(data,c))
    c=deepcopy(data);c['blocks']=[[0,1],[1,2]];reject('overlapping_partition',lambda:new.run(c))
    A0,b0=simplexd(3);c={'A':A0,'b':b0,'start':[0]*3,'target':[1,0,0],'blocks':[[0,1],[2],[3]]}
    reject('higher_missing_face_not_just_triangles',lambda:new.run(c))
    reject('classification_cap',lambda:new.run(data,classification_cap=5))
    # Replay uses no optimizer, inverse or original/refined producer. It DOES
    # replay finite combination classification and BFS on checked link graphs.
    saved=[]
    def forbidden(*a,**k):raise AssertionError('verification called discovery')
    for obj,name in [(raw.lp.ExactLP,'maximize'),(raw.basis,'invert'),(raw.basis,'basis_packet')]:
        saved.append((obj,name,getattr(obj,name)));setattr(obj,name,forbidden)
    try:require(new.verify(data,good)==out['verified'],'discovery-disabled replay disagrees')
    finally:
        for obj,name,fn in saved:setattr(obj,name,fn)
    return {'rejected':len(names),'names':names,'LP_inverse_basis_disabled_replay':True}


def hashes():
    names=['defect_block_routes.py','test_defect_block_routes.py','original_facet_segments.py','exact_farkas_lp.py',
           'simple_tangent_policy_audit.py','two_face_acquisition.py','test_two_face_acquisition.py','target_phase_pivot.py','target_roof_phase_barrier.py']
    return {f'scripts/{n}':hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in names}


def dump(path,data):path.write_text(json.dumps(raw.serial(data),sort_keys=True,indent=2)+'\n')


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--model');ap.add_argument('--aux',action='store_true');ap.add_argument('--assemble',action='store_true');args=ap.parse_args()
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    selected=[args.model] if args.model else list(models()) if not(args.aux or args.assemble) else []
    for name in selected:
        result=graph_stage(name);dump(ROOT/f'research/DEFECT_STAGE_{name}.json',{'source_sha256':hashes(),'result':result});print(name,result['totals'],flush=True)
    if args.aux or not(args.model or args.assemble):
        result={'abstract':abstract_stage(),'coupled_family':family_stage(),'negative':negative_stage()}
        dump(ROOT/'research/DEFECT_STAGE_aux.json',{'source_sha256':hashes(),'result':result});print('AUX PASS',flush=True)
    if args.assemble or not(args.model or args.aux):
        stages=[json.loads((ROOT/f'research/DEFECT_STAGE_{n}.json').read_text()) for n in models()]
        aux=json.loads((ROOT/'research/DEFECT_STAGE_aux.json').read_text());require(all(x['source_sha256']==hashes() for x in stages+[aux]),'stale source-bound stage')
        totals={k:sum(x['result']['totals'][k] for x in stages) for k in stages[0]['result']['totals']}
        result={'status':'PASS','source_sha256':hashes(),'graph_totals':totals,'graphs':[x['result'] for x in stages],**aux['result'],
            'scope':'Exact finite and rational research tests, not Lean or Prove2Me acceptance.'}
        dump(ROOT/'research/DEFECT_BLOCK_CHECK.json',result);print(totals,flush=True)
if __name__=='__main__':main()
