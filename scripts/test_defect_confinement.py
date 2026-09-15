#!/usr/bin/env python3
"""Independent tests for confined nonflag facets and the visited-state bound.

The family starts with a truncated three-cube times intervals and truncates
successive ridges between its cap and each additional coordinate's lower facet.
A direct shallow-cut proof and a minimal-nonface update certify the whole family.
Small exact vertex enumeration is a separate reference, not route input.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
from copy import deepcopy
from collections import deque
import argparse, hashlib, json, random, time
import sympy as sp
import original_facet_segments as seg
import defect_confinement as dc
import simple_tangent_policy_audit as base

ROOT=Path(__file__).resolve().parents[1]


def family(d):
    seg.require(type(d)is int and d>=3,'family dimension must be at least three')
    A=[];b=[]
    for i in range(d):
        A.extend([[-Q(i==j) for j in range(d)],[Q(i==j) for j in range(d)]])
        b.extend([Q(0),Q(1)])
    cap=[Q(j<3) for j in range(d)]
    A.append(cap);b.append(Q(5,2))
    core={1,3,5}
    pairs={frozenset((2*i,2*i+1)) for i in range(d)}
    pairs|={frozenset((2*d,2*i)) for i in range(3)}
    trace=[]
    for j in range(3,d):
        u,v=2*d,2*j;new=len(A)
        seg.require(u not in core and v not in core and frozenset((u,v)) not in pairs,
                    'stellar edge not between two good adjacent labels')
        newpairs={frozenset((new,w)) for w in range(new) if w not in (u,v)
                  and (frozenset((u,w)) in pairs or frozenset((v,w)) in pairs)}
        newpairs.add(frozenset((u,v)))
        pairs|=newpairs
        delta=Q(1,2**(j+1))
        row=cap[:];row[j]-=1
        A.append(row);b.append(Q(5,2)-delta)
        trace.append({'edge':[u,v],'new_facet':new,'delta':str(delta),
                      'new_missing_pairs':[sorted(x) for x in sorted(newpairs,key=lambda s:tuple(sorted(s)))]})
    u=[Q(0)]*d
    v=[Q(1),Q(1),Q(1,2)]+[Q(1,2**(j+1)) for j in range(3,d)]
    return {'A':A,'b':b,'start':u,'target':v},pairs,frozenset(core),trace


class FamilyOracle:
    """Family-specific exact witness producer. NEVER trusted by the consumer.
    Allowed intersections are constructed with one scalar sum interval; absent
    ones use the explicit minimal-nonface duals. No vertex graph or LP is used.
    """
    def __init__(self,d):
        self.data,self.pairs,self.core,self.trace=family(d)
        self.A,self.b,self.u,self.v=seg.parse(self.data)
        self.d=d;self.cache={};self.known=[];self.absent=[];self.lp_calls=0
        self.solver=type('NoSolver',(),{'pivots':0})()
        self.bounds=[{'coordinate':i,'sign':sgn,'dual':[[2*i+(sgn==1),'1']],
                      'bound':'1' if sgn==1 else '0'} for i in range(d) for sgn in (-1,1)]
    def negative(self,T):
        cap=2*self.d
        if len(T)==3: dual=[[cap,'1']]
        else:
            a,b=sorted(T)
            if a//2==b//2 and a%2==0 and b==a+1:dual=[]
            elif cap in T:
                low=next(x for x in T if x!=cap);i=low//2
                assert low%2==0
                dual=[[2*j+1,'1'] for j in range(3) if j!=i] if i<3 else [[cap+1+i-3,'1']]
            else:
                new=max(T);other=min(T);j=new-cap+2;i=other//2
                if i<3:
                    assert other%2==0
                    dual=[[2*l+1,'1'] for l in range(3) if l!=i]+[[2*j,'1']]
                elif other==2*j+1:dual=[[cap,'1']]
                else:
                    assert other%2==0 and i<j
                    dual=[[cap+1+i-3,'1'],[2*j,'1']]
        f=seg.objective(self.A,T)
        val=seg.lp.verify_dual(self.A,self.b,f,dual)
        seg.require(val<sum(self.b[i] for i in T),'family exclusion has no strict gap')
        return dual,str(val)
    def point_for(self,S):
        C=Q(5,2);lo=sum(2*i+1 in S for i in range(3));hi=sum(2*i not in S for i in range(3))
        if 2*self.d in S:lo=max(lo,C);hi=min(hi,C)
        hi=min(hi,C)
        for j in range(3,self.d):
            delta=Q(1,2**(j+1));new=2*self.d+1+j-3
            if 2*j in S:hi=min(hi,C-delta)
            if new in S:lo=max(lo,C-delta)
            if new in S and 2*j+1 in S:lo=max(lo,C-delta+1)
        seg.require(lo<=hi,'allowed family face has empty scalar interval')
        mass=Q(lo);x=[Q(2*i+1 in S) for i in range(3)]
        rest=mass-sum(x)
        for i in range(3):
            if 2*i not in S and 2*i+1 not in S:
                add=min(Q(1),rest);x[i]=add;rest-=add
        seg.require(rest==0,'family sum not allocated')
        for j in range(3,self.d):
            delta=Q(1,2**(j+1));new=2*self.d+1+j-3
            x.append(Q(1) if 2*j+1 in S else Q(0) if 2*j in S else max(Q(0),mass-C+delta))
        return tuple(x)
    def ask(self,S):
        S=frozenset(S);key=seg.key(S)
        if key in self.cache:return self.cache[key]['kind']=='present'
        T=next((T for T in sorted(self.pairs,key=lambda T:tuple(sorted(T))) if T<=S),None)
        if T is None and self.core<=S:T=self.core
        if T is None:
            x=self.point_for(S);record={'rows':sorted(S),'kind':'present','point':seg.serial(x)}
        else:
            dual,bound=self.negative(T);record={'rows':sorted(S),'kind':'absent','separated_rows':sorted(T),
                                               'dual':dual,'bound':bound}
        seg.intersection_audit(self.A,self.b,S,record);self.cache[key]=record
        return record['kind']=='present'
    def point(self,F):
        seg.require(self.ask(F),'family vertex not feasible')
        return tuple(map(seg.rat,self.cache[seg.key(F)]['point']))


def family_segment(d,u=None,v=None):
    O=FamilyOracle(d);A,b,x,y=seg.parse(O.data)
    if u is not None:x=tuple(u)
    if v is not None:y=tuple(v)
    data={'A':A,'b':b,'start':x,'target':y}
    pu=base.basis_packet(A,b,x);pv=base.basis_packet(A,b,y)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    alg=seg.Segment(len(A),d,O,10000,100000);path=alg.between(F&H,F,H)
    vertices={seg.key(F):pu,seg.key(H):pv}
    for T in path:
        if seg.key(T) not in vertices:vertices[seg.key(T)]=base.basis_packet(A,b,O.point(T))
    cert=seg.serial({'format':'original-facet-segment-v1','problem_sha256':seg.input_hash(A,b,x,y),
       'limits':{'edges':10000,'nodes':100000},'boundedness':O.bounds,'vertices':list(vertices.values()),
       'intersections':list(O.cache.values()),'events':alg.events,'path':[sorted(F) for F in path]})
    return data,{'certificate':cert,'verified':seg.verify(data,cert)},O


def minimal_nonfaces(facets,m,d):
    """Complete small independent combinatorial reference, exponential and capped by caller."""
    missing=[]
    for s in range(2,min(m,d+1)+1):
        for T in combinations(range(m),s):
            T=frozenset(T)
            if any(N<=T for N in missing):continue
            if not any(T<=F for F in facets):missing.append(T)
    return missing


def vertices(A,b):
    """ALL exact square systems; no floating filter, no construction formula."""
    d=len(A[0]);V={};tested=0
    for I in combinations(range(len(A)),d):
        tested+=1
        # SymPy for this independent reference, not the producer's inverse.
        M=sp.Matrix([A[i] for i in I])
        if M.det()==0:continue
        x=tuple(Q(str(z)) for z in M.inv()*sp.Matrix([b[i] for i in I]))
        if base.feasible(A,b,x):V[x]=frozenset(base.active_rows(A,b,x))
    seg.require(V and all(len(F)==d for F in V.values()),'reference not simple')
    return V,tested


def clipping_reference(d):
    """Independent complete vertex update by shallow cuts, used through dimension eight.
    Each step checks it cuts ONLY the intended original face vertices and uses
    every original edge crossing, with all resulting inequalities reevaluated.
    """
    data,_,_,_=family(d);A,b=data['A'],data['b']
    V={tuple(map(Q,x)):frozenset(2*i+x[i] for i in range(d)) for x in product((0,1),repeat=d)}
    currentA=A[:2*d];currentb=b[:2*d];counts=[]
    for row,rhs in zip(A[2*d:],b[2*d:]):
        idx=len(currentA);good={x:F for x,F in V.items() if seg.dot(row,x)<rhs}
        removed={x:F for x,F in V.items() if seg.dot(row,x)>rhs}
        seg.require(len(good)+len(removed)==len(V) and removed,'cut meets an old vertex or removes none')
        if idx==2*d:
            wanted={1,3,5}
        else:wanted={2*d,2*(idx-2*d+2)}
        seg.require(all((wanted<=F)==(x in removed) for x,F in V.items()),'cut removed a different face')
        new={};crossings=0
        for x,F in removed.items():
            for y,H in good.items():
                if len(F&H)==d-1:
                    alpha=(rhs-seg.dot(row,x))/(seg.dot(row,y)-seg.dot(row,x))
                    z=tuple(a+alpha*(bb-a) for a,bb in zip(x,y))
                    K=(F&H)|{idx};new[z]=frozenset(K);crossings+=1
        currentA=currentA+[row];currentb=currentb+[rhs]
        V={**good,**new}
        seg.require(all(base.feasible(currentA,currentb,x) and set(base.active_rows(currentA,currentb,x))==set(F)
                        for x,F in V.items()),'clipping vertex mismatch')
        counts.append({'rows':idx+1,'removed_vertices':len(removed),'new_vertices':len(new),'crossing_edges':crossings,'total_vertices':len(V)})
    seg.require(len(V)==(3*d+11)*2**d//16,'family vertex formula failed')
    return V,counts


def label_components(m,pairs,core):
    adj=[set() for _ in range(m)]
    for S in list(pairs)+[core]:
        for a in S:adj[a]|=S-{a}
    seen={0};q=[0]
    while q:
        x=q.pop()
        for y in adj[x]-seen:seen.add(y);q.append(y)
    return len(seen)


def distance(V,u,v):
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==len(x)-1:adj[x].append(y);adj[y].append(x)
    D={u:0};q=deque([u])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    return D[v],adj


def original_audit(data,out,V=None):
    a=dc.verify(data,out['certificate']);seg.require(a==out['verified'],'confinement report mismatch')
    if V is not None:
        points={tuple(sorted(F)):x for x,F in V.items()}
        path=[points[tuple(F)] for F in a['loop_erased_active_path']]
        seg.require(path[0]==tuple(data['start']) and path[-1]==tuple(data['target']),'reference endpoint mismatch')
        seg.require(all(len(V[x]&V[y])==len(x)-1 for x,y in zip(path,path[1:])), 'reference nonedge')
    return a


def reentry_models():
    # A known nonflag holdout, followed by products and a GOOD-edge truncation.
    # This tests genuine reentries in a bounded defect core, not just k=0 paths.
    vs=[[Q(i)**j for j in (1,2,3)] for i in range(8)]
    mean=[sum(v[j] for v in vs)/8 for j in range(3)]
    A=[[v[j]-mean[j] for j in range(3)] for v in vs];b=[Q(1)]*8
    V,_=vertices(A,b);N=minimal_nonfaces(list(V.values()),8,3)
    B=set().union(*(T for T in N if len(T)>=3));seg.require(B=={0,2,3,4,5,7},'holdout core changed')
    u=next(x for x,F in V.items() if F=={0,1,2});v=next(x for x,F in V.items() if F=={3,4,7})
    cases=[]
    for d in (4,6):
        AA=[list(a)+[Q(0)]*(d-3) for a in A];bb=list(b)
        for j in range(3,d):
            AA.extend([[-Q(j==i) for i in range(d)],[Q(j==i) for i in range(d)]]);bb.extend([Q(0),Q(1)])
        cases.append((f'nonflag_product_{d}',{'A':AA,'b':bb,'start':u+(Q(0),)*(d-3),'target':v+(Q(1),)*(d-3)},B,False))
    AA=[list(a)+[Q(0)] for a in A]+[[Q(0)]*3+[-Q(1)],[Q(0)]*3+[Q(1)]];bb=list(b)+[Q(0),Q(1)]
    productV={x+(Q(t),):F|{8+t} for x,F in V.items() for t in (0,1)}
    new=AA[1][:];new[-1]-=1;old=b[1]
    delta=min(old-seg.dot(new,x) for x in productV if old-seg.dot(new,x)>0)/3
    AA.append(new);bb.append(old-delta)
    VV,_=vertices(AA,bb);NN=minimal_nonfaces(list(VV.values()),11,4)
    BB=set().union(*(T for T in NN if len(T)>=3));seg.require(BB==B,'good-edge subdivision grew core')
    seg.require(label_components(11,[T for T in NN if len(T)==2],B)==11,'cross-cut did not remove product structure')
    cases.append(('nonflag_crosscut4',{'A':AA,'b':bb,'start':u+(delta,),'target':v+(Q(1),)},B,True))
    return cases


def test_combinatorial_count():
    # Random loop-free walks in Johnson graphs, accepting arbitrary revisits of
    # exceptional labels but only one interval for each protected label.
    rng=random.Random(903);tested=0;adverse=0
    for m in range(3,10):
        for d in range(1,m):
            for k in range(m+1):
                B=set(range(k))
                for _ in range(6):
                    F=frozenset(rng.sample(range(m),d));path=[F];seen={F};ended=set()
                    for step in range(40):
                        allowed=[]
                        for a in F:
                            for b in set(range(m))-F:
                                H=(F-{a})|{b}
                                if H not in seen and not ((H-B)&ended):allowed.append(H)
                        if not allowed:break
                        H=rng.choice(allowed);ended|=(F-B)-H;path.append(H);seen.add(H);F=H
                    dc.count_states(path,m,d,B);tested+=1
    # Exhaustive small walks guard counting and loop-erasure independently.
    m,d,k=5,2,3;B=set(range(k));count=0
    def rec(path,ended):
        nonlocal count
        dc.count_states(path,m,d,B);count+=1
        if len(path)>=6:return
        F=path[-1]
        for a in F:
            for b in set(range(m))-F:
                H=(F-{a})|{b}
                if H not in path and not ((H-B)&ended):rec(path+[H],ended|((F-B)-H))
    for F in map(frozenset,combinations(range(m),d)):rec([F],set())
    return {'random_interval_paths':tested,'exhaustive_small_paths':count}


def main():
    p=argparse.ArgumentParser();p.add_argument('--large',action='store_true');args=p.parse_args()
    start=time.monotonic();saved=[];models=[];summaries=[]
    for d in (3,4,5):
        data,pairs,core,trace=family(d);V,clipping=clipping_reference(d)
        independent,systems=vertices(data['A'],data['b'])
        seg.require(V==independent,'clipping and exact active subsets disagree')
        N=minimal_nonfaces(list(V.values()),len(data['A']),d)
        seg.require(set(N)==set(pairs)|{core},'minimal nonfaces differ from structural recurrence')
        # Confirm facet irredundancy using the entire independently known face.
        for i in range(len(data['A'])):
            X=[x for x,F in V.items() if i in F]
            x=tuple(sum(v[j] for v in X)/len(X) for j in range(d))
            seg.require(base.active_rows(data['A'],data['b'],x)==[i],'row is not an irredundant facet')
        connected=label_components(len(data['A']),pairs,core)
        seg.require(connected==len(data['A']),'minimal-nonface graph admits a product split')
        rng=random.Random(d*159)
        choices=[(tuple(data['start']),tuple(data['target']))]
        allpairs=[(u,v) for u in V for v in V if u!=v];rng.shuffle(allpairs)
        choices+=allpairs[:20]
        total={'dimension':d,'facets':len(data['A']),'vertices':len(V),'global_defect_core':sorted(core),
               'minimal_nonfaces':len(N),'independent_square_systems':systems,'pairs_tested':0,
               'raw_edges':0,'reentries_in_core':0,'local_k_max':0,'local_k_min':len(data['A']),
               'triangles_checked':0,'missing_triangles':0,'nonshortest':0,
               'uniform_core_bound':dc.bound(len(data['A']),d,3),'structural_signature_bound':14*d-20,'all_graph_vertices_supplied_to_producer':False,
               'nonface_hypergraph_connected':True}
        for i,(u,v) in enumerate(choices):
            di={**data,'start':u,'target':v};old=seg.construct(di)
            new=dc.construct(di,old,exceptional=core);r=original_audit(di,new,V)
            dist,_=distance(V,u,v)
            seg.require(r['loop_erased_edges']<=14*d-20,'family excluded-triple bound failed')
            total['pairs_tested']+=1;total['raw_edges']+=r['raw_edges'];total['nonshortest']+=r['loop_erased_edges']>dist
            total['reentries_in_core']+=old['verified']['reentry_debt']
            total['triangles_checked']+=r['triangles_checked'];total['missing_triangles']+=r['missing_link_triangles']
            local=set().union(*(set(q['triangle']) for q in r['missing_triangle_witnesses'])) if r['missing_triangle_witnesses'] else set()
            total['local_k_max']=max(total['local_k_max'],len(local));total['local_k_min']=min(total['local_k_min'],len(local))
            if i==0 or old['verified']['reentry_debt']:
                saved.append({'name':f'confined_{d}_{i}','input':seg.serial(di),'output':new,'reference_distance':dist})
        special_data,special_raw,_=family_segment(d)
        generic_raw=seg.construct(special_data)
        seg.require(special_raw['certificate']['path']==generic_raw['certificate']['path'],'special witness producer changed segment path')
        total['specialized_generic_full_path_match']=True
        total['clipping_transcript']=clipping;models.append(total);print('family',total,flush=True)
    # Only small historical INPUTS are reused. Construct every segment afresh;
    # no earlier report or route certificate is assumed verified here.
    for row in json.loads((ROOT/'fixtures/defect_reference_inputs.json').read_text()):
        raw=seg.construct(row['input'])
        out=dc.construct(row['input'],raw);r=original_audit(row['input'],out)
        summaries.append({'model':row['model'],'raw_edges':r['raw_edges'],'local_k':r['k'],
                          'triangles':r['triangles_checked'],'missing':r['missing_link_triangles'],
                          'bound':r['binomial_bound'],'certified_signature_bound':r['certified_signature_bound']})
        saved.append({'name':row['name'],'input':row['input'],'output':out})
    larger=[]
    if args.large:
        for d in (6,8,12):
            data,pairs,core,trace=family(d)
            t=time.monotonic()
            if d<=8:
                raw=seg.construct(data,query_cap=200000);oracle=None;kind='generic exact LP'
            else:
                data,raw,oracle=family_segment(d);kind='family scalar/dual witnesses; same segment recursion'
            out=dc.construct(data,raw,exceptional=core,triangle_cap=500000,query_cap=500000,oracle=oracle)
            r=original_audit(data,out)
            larger.append({'dimension':d,'facets':len(data['A']),'known_vertices':(3*d+11)*2**d//16,
                           'enumerated_vertex_graph':False,'edges':r['raw_edges'],'bound':r['binomial_bound'],
                           'structural_signature_bound':14*d-20,'certified_signature_bound':r['certified_signature_bound'],
                           'triangles':r['triangles_checked'],'missing_triangles':r['missing_link_triangles'],
                           'segment_lp_calls':raw.get('discovery_work',{}).get('lp_maximizations',0),'witness_producer':kind,
                           'extra_lp_calls':out['additional_discovery']['lp_maximizations_including_rechecked_bounds'],
                           'seconds':round(time.monotonic()-t,4)})
            saved.append({'name':f'large_{d}','input':seg.serial(data),'output':out});print('large',larger[-1],flush=True)
    print('starting reentry controls',flush=True)
    recurrent=[]
    for name,data,B,nonproduct in reentry_models():
        print('reentry model',name,flush=True)
        raw=seg.construct(data);out=dc.construct(data,raw,exceptional=B);rr=original_audit(data,out)
        seg.require(raw['verified']['reentry_debt']>0 and all(q['facet'] in B for q in raw['verified']['reentries']), 'holdout lost its real confined reentry')
        recurrent.append({'name':name,'dimension':rr['dimension'],'facets':rr['original_rows'],'core':sorted(B),
                          'edges':rr['raw_edges'],'reentry_debt':raw['verified']['reentry_debt'],'bound':rr['binomial_bound'],
                          'triangles':rr['triangles_checked'],'nonproduct_certified':nonproduct})
        saved.append({'name':name,'input':seg.serial(data),'output':out})
    print('starting negative controls',flush=True)
    # Attack the central distinction: a transversal is not whole confinement.
    negatives=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):negatives.append(name)
        else:raise AssertionError('forgery passed '+name)
    witness=next(x for x in saved if x['output']['verified']['missing_link_triangles'])
    wc=witness['output']['certificate'];bad=deepcopy(wc)
    T=witness['output']['verified']['missing_triangle_witnesses'][0]['triangle']
    seg.require(all(T[0] in q['triangle'] for q in witness['output']['verified']['missing_triangle_witnesses']), 'control not a hitting set')
    bad['exceptional_facets']=[T[0]]
    reject('triangle_hitting_set_not_confinement',lambda:dc.verify(witness['input'],bad))
    bad=deepcopy(wc);bad['exceptional_facets']=[]
    reject('declare_nonflag_execution_flag',lambda:dc.verify(witness['input'],bad))
    bad=deepcopy(wc);bad['intersections']=[]
    reject('missing_triangle_certificate_table',lambda:dc.verify(witness['input'],bad))
    bad=deepcopy(wc)
    missing=witness['output']['verified']['missing_triangle_witnesses'][0]
    key=set(missing['locked'])|set(missing['triangle'])
    j=next(i for i,c in enumerate(bad['intersections']) if set(c['rows'])==key)
    bad['intersections'][j]={'rows':sorted(key),'kind':'present','point':witness['input']['start']}
    reject('empty_triangle_declared_present',lambda:dc.verify(witness['input'],bad))
    bad=deepcopy(wc);bad['segment']['path'].pop()
    reject('wrong_segment_binding',lambda:dc.verify(witness['input'],bad))
    reject('zero_diagnostic_cap',lambda:dc.construct(witness['input'],wc['segment'],triangle_cap=0))
    # Protected-row revisiting invalidates the stand-alone combinatorial bound.
    reject('protected_reentry',lambda:dc.count_states([frozenset((0,1)),frozenset((1,2)),frozenset((0,2))],3,2,set()))
    # Every extra triangle witness and every original route can be checked with
    # all geometric producer/search entrypoints disabled. BFS is still replayed.
    old=(seg.lp.ExactLP,base.invert,base.basis_packet,seg.Discovery)
    def disabled(*a,**k):raise AssertionError('audit invoked geometric discovery')
    seg.lp.ExactLP=base.invert=base.basis_packet=seg.Discovery=disabled
    try:
        for row in saved:original_audit(row['input'],row['output'])
    finally:seg.lp.ExactLP,base.invert,base.basis_packet,seg.Discovery=old
    report={'status':'PASS','scope':'Written partial-flag route theorem and exact arithmetic certificates; no Lean/platform verdict',
            'models':models,'replayed_previous_inputs':summaries,'large_models':larger,'nonflag_reentry_controls':recurrent,
            'finite_count_tests':test_combinatorial_count(),'negative_controls':negatives,
            'search_disabled_audits':len(saved),'seconds':round(time.monotonic()-start,3),
            'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),ROOT/'scripts/defect_confinement.py',ROOT/'fixtures/defect_reference_inputs.json']}}
    (ROOT/'research/DEFECT_CONFINEMENT_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'fixtures/defect_confinement_examples.json').write_text(json.dumps(saved,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
