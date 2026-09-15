#!/usr/bin/env python3
"""Independent finite-simplicial and exact original-H tests of mixed absorption.
No Lean/platform claim. Random exploratory hulls are NOT used as proof data;
the saved rational plateau is reconstructed by all exact active-square systems.
"""
from __future__ import annotations
from itertools import combinations
from fractions import Fraction as Q
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random, time
import sympy as sp
import mixed_defect_absorption as M
D=M.prior;old=D.old
ROOT=Path(__file__).resolve().parents[1]


def allsets(n):return [frozenset(S) for k in range(n+1) for S in combinations(range(n),k)]


def fullfacets(K):
    faces=[S for S in allsets(K.n) if K.ask(S)]
    return [S for S in faces if not any(S<T for T in faces)]


def explicit_update(F,E,z):
    out=[]
    for S in F:
        if E<=S:
            out.extend((S-{i})|{z} for i in E)
        else:out.append(S)
    return D.ordered(out)


def missing(n,F):
    out=[]
    for S in allsets(n):
        if any(N<=S for N in out):continue
        if not any(S<=T for T in F):out.append(S)
    return D.ordered(out)


def abstract():
    start=time.monotonic();counts={'complexes':0,'face_edge_updates':0,'absorbed_updates':0,
       'non_twin_absorbed_updates':0,'mixed_blockers':0,'pure_carrier_adjacencies':0,
       'potential_increasing_edges':0,'same_weight_nonabsorbed_edges':0};examples=[]
    C=[S for S in allsets(4) if len(S)>=2]
    complexes=[]
    for mask in range(1<<len(C)):
        H=[S for j,S in enumerate(C) if mask>>j&1]
        if D.ordered(H)==D.minimal(H):complexes.append(D.Complex(4,H))
    rng=random.Random(260926)
    for n in(5,6,7):
        pool=[S for S in allsets(n) if 2<=len(S)<=5]
        for _ in range(70):
            complexes.append(D.Complex(n,D.minimal(rng.sample(pool,rng.randrange(1,min(len(pool),16))))))
    for K in complexes:
        counts['complexes']+=1;F=fullfacets(K);pure=len(set(map(len,F)))==1;d=len(F[0])
        for E in combinations(range(K.n),2):
            if not K.ask(E):continue
            J=D.stellar(K,E);G=explicit_update(F,frozenset(E),K.n)
            M.require(J.missing==missing(J.n,G),'stellar recurrence disagrees with explicit simplex update')
            counts['face_edge_updates']+=1
            if M.weight(J)>M.weight(K):counts['potential_increasing_edges']+=1
            p=M.absorption(K,E)
            if p:
                M.audit_absorption(K,p);counts['absorbed_updates']+=1;counts['mixed_blockers']+=len(p['mixed_blockers'])
                inc=K.incidence()
                if inc.get(E[0])!=inc.get(E[1]):counts['non_twin_absorbed_updates']+=1
            elif M.weight(J)==M.weight(K) and K.high():counts['same_weight_nonabsorbed_edges']+=1
            if pure:
                for X,Y in combinations(G,2):
                    if len(X&Y)!=d-1:continue
                    XX=(X-{K.n})|set(E) if K.n in X else X
                    YY=(Y-{K.n})|set(E) if K.n in Y else Y
                    M.require(XX in F and YY in F and (XX==YY or len(XX&YY)==d-1),'carrier not adjacency or stationarity')
                    counts['pure_carrier_adjacencies']+=1
    # Shared higher offspring can absorb a mixed child even when no pair is available.
    K=D.Complex(5,[{0,1,2,3},{0,2,3,4}]);p=M.absorption(K,(0,1))
    M.require(p and len(p['mixed_blockers'])==1 and len(p['mixed_blockers'][0]['blocker'])==4,'higher blocker absent')
    J=M.audit_absorption(K,p)
    examples.append({'input':[sorted(N) for N in K.missing],'certificate':p,
                     'output':[sorted(N) for N in J.missing],'weights':[M.weight(K),M.weight(J)]})
    return {'status':'PASS','stage':'abstract',**counts,'higher_blocker_example':examples[0],
            'seconds':round(time.monotonic()-start,3)},None,[]


def cyclic(n):
    X=[[Q(i)**j for j in range(1,5)]for i in range(n)]
    mean=[sum(x[j] for x in X)/n for j in range(4)]
    return [[x[j]-mean[j] for j in range(4)]for x in X],[Q(1)]*n


def simplex(d):return [[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(1)]*d],[Q(0)]*d+[Q(1)]


def exact_reference(A,b):
    d=len(A[0]);V={};attempts=0
    for I in combinations(range(len(A)),d):
        attempts+=1;S=sp.Matrix([A[i] for i in I])
        if S.det()==0:continue
        x=tuple(Q(str(z)) for z in S.inv()*sp.Matrix([b[i] for i in I]))
        if old.basis.feasible(A,b,x):V[x]=frozenset(old.basis.active_rows(A,b,x))
    M.require(V and all(len(T)==d for T in V.values()),'not a simple original reference')
    for i in range(len(A)):
        X=[x for x,T in V.items() if i in T];M.require(len(X)>=d,'empty or undersized facet')
        avg=tuple(sum(x[j] for x in X)/len(X) for j in range(d))
        M.require(old.basis.active_rows(A,b,avg)==[i],'not a genuine facet row')
        M.require(sp.Matrix([[x[j]-X[0][j] for j in range(d)]for x in X[1:]]).rank()==d-1,'facet dimension')
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    M.require(all(len(a)==d for a in adj.values()),'wrong reference degree')
    dist={}
    for x in V:
        dd={x:0};q=deque([x])
        while q:
            a=q.popleft()
            for b in adj[a]:
                if b not in dd:dd[b]=dd[a]+1;q.append(b)
        M.require(len(dd)==len(V),'reference disconnected');dist[x]=dd
    return V,adj,dist,attempts


def plateau():
    raw=json.loads((ROOT/'fixtures/mixed_absorption_plateau.json').read_text())
    X=raw['points'];n=len(X);d=len(X[0]);mean=[Q(sum(x[j] for x in X),n) for j in range(d)]
    return [[Q(x[j])-mean[j] for j in range(d)]for x in X],[Q(1)]*n


def graph_stage():
    start=time.monotonic();reports=[];fixtures=[];saved=[];negative=[]
    cases=[('simplex3',*simplex(3),6),('cyclic4_6',*cyclic(6),8),('cyclic4_7',*cyclic(7),12),
           ('cyclic4_8',*cyclic(8),12),('cyclic4_9',*cyclic(9),12),('plateau5_10',*plateau(),8)]
    for name,A,b,cap in cases:
        V,adj,dist,systems=exact_reference(A,b)
        K=D.Complex(len(A),missing(len(A),list(V.values())))
        base_stages,base_steps,_=D.compress(K);residual=base_stages[-1]
        old_ref=D.ResidualRefinement(residual,len(A[0]))
        once,once_report=M.plan(K,1);macro,macro_report=M.plan(K,3)
        budget_input=M.budget_view(K)
        budget_packet=M.budget.refine(budget_input,'budget')
        budget_report=M.budget.verify(budget_input,budget_packet)
        one_stages,_,_=M.audit_schedule(K,once,1)
        pairs=list(combinations(V,2));random.Random(260+len(A)).shuffle(pairs);pairs=pairs[:cap]
        row={'name':name,'dimension':len(A[0]),'original_facets':len(A),'original_vertices':len(V),
             'exact_square_systems':systems,'initial_weight':M.weight(K),'higher_defects':len(K.high()),
             'prior_refined_vertices':len(old_ref.vertices),'prior_bound':len(old_ref.vertices)-len(A[0]),
             'one_step_only':once_report,'macro_planner':macro_report,'unchanged_262_budget':budget_report,'pairs':0,'new_edges':0,'bfs_edges':0,
             'prior_edges':0,'nonshortest':0,'refined_edges':0,'stationary_steps':0,
             'LP_maximizations':0,'LP_pivots':0,'original_reentries':0}
        for j,(u,v) in enumerate(pairs):
            data={'A':A,'b':b,'start':u,'target':v};out=M.construct(data,3)
            rep=M.verify(data,out['certificate']);M.require(rep==out['verified'],'report mismatch')
            inv={T:x for x,T in V.items()};path=[inv[frozenset(T)]for T in out['certificate']['path']['original_path']]
            M.require(all(y in adj[x] for x,y in zip(path,path[1:])),'delivered original nonedge')
            _,oldrep,_=D.route(K,V[u],V[v],len(u))
            row['pairs']+=1;row['new_edges']+=rep['original_edges'];row['bfs_edges']+=dist[u][v]
            row['prior_edges']+=oldrep['original_edges'];row['nonshortest']+=rep['original_edges']>dist[u][v]
            row['refined_edges']+=rep['refined_edges'];row['stationary_steps']+=rep['stationary_steps']
            row['original_reentries']+=rep['original_facet_reentries']
            for k in('LP_maximizations','LP_pivots'):row[k]+=out['discovery'][k]
            row['new_refined_vertices']=rep['refined_vertices'];row['new_bound']=rep['all_pairs_bound']
            if j==0:
                fixtures.append({'model':name,'input':serial(data),'output':out,'shortest_distance':dist[u][v],
                                 'unchanged_262_budget_packet':budget_packet})
                saved.append((data,out))
        if name=='plateau5_10':
            M.require(one_stages[-1].high() and not macro_report['residual_higher_defects'],'plateau control disappeared')
            stage=one_stages[-1];failed=[]
            M.require(budget_report['completion']=='stalled' and budget_report['remaining_weight']==3, 'unchanged #262 budget no longer stalls')
            M.require(budget_packet['terminal']['minimal_nonfaces']==[sorted(N) for N in stage.missing], 'not the same #262 terminal plateau')
            blocked=M.budget.refine(M.budget_view(stage),'budget')
            M.require(blocked['status']=='stalled' and not blocked['steps'], 'unchanged #262 has a decreasing plateau move')
            for E in M.candidates(stage):
                if M.absorption(stage,E) is None:failed.append(list(E))
            neighbor_weights=[{'edge':list(E),'weight_after':M.weight(D.stellar(stage,E))} for E in M.candidates(stage)]
            M.require(all(q['weight_after']>=M.weight(stage) for q in neighbor_weights),'plateau has an immediate weight-decreasing move')
            row['plateau']={'neighbor_weights':neighbor_weights,'n':stage.n,'minimal_nonfaces':[sorted(N)for N in stage.missing],
                            'all_rejected_edges':failed,'weight':M.weight(stage),
                            'macro_weights':[rep['step_weights'] for _,out in saved[-1:] for rep in [out['verified']]][0]}
        reports.append(row);print(name,row['prior_refined_vertices'],row['new_refined_vertices'],row['pairs'],flush=True)
    # Real, audited certificate corruption; not merely checking expected scalar values.
    data,out=next((data,out)for data,out in saved if len(data['A'])==7)
    good=out['certificate']
    def reject(name,f):
        try:f()
        except(ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):negative.append(name)
        else:raise AssertionError('accepted forged certificate '+name)
    changes=[('omit_mixed_descendant',lambda c:c['macros'][0]['moves'][0]['mixed_blockers'].pop()),
       ('wrong_blocker',lambda c:c['macros'][0]['moves'][0]['mixed_blockers'][0].update(blocker=[0])),
       ('boolean_blocker',lambda c:c['macros'][0]['moves'][0]['mixed_blockers'][0].update(blocker=[False,1])),
       ('false_weight',lambda c:c['macros'][0].update(weight_after=999)),
       ('missing_original_nonface',lambda c:c['minimal_nonfaces'].pop()),
       ('missing_original_answers',lambda c:c.update(intersections=[])),
       ('wrong_original_inverse',lambda c:c['vertices'][0]['directions'][0].__setitem__(0,'999')),
       ('wrong_carrier_path',lambda c:c['path']['original_path'].pop()),
       ('wrong_input_hash',lambda c:c.update(problem_sha256='00')),
       ('missing_bound',lambda c:c['boundedness'].pop())]
    for name,change in changes:
        c=deepcopy(good);change(c);reject(name,lambda c=c:M.verify(data,c))
    p_data,p_out=saved[-1];c=deepcopy(p_out['certificate']);c['limits']['macro']=1
    reject('bridge_exceeds_declared_budget',lambda:M.verify(p_data,c))
    K=D.Complex(6,[{0,1,2},{3,4,5}]);c={'edge':[0,3],'shared':[],'mixed_blockers':[]}
    reject('unsafe_mixed_step_declared_absorbed',lambda:M.audit_absorption(K,c))
    p=deepcopy(good);p['macros'][0]['moves'][0]['edge'][0]=True
    reject('boolean_label',lambda:M.verify(data,p))
    original=(old.lp.ExactLP,old.basis.invert,old.basis.basis_packet,old.Discovery,M.best_absorption,M.plan)
    def forbidden(*a,**kw):raise AssertionError('consumer invoked a geometric/planner search')
    old.lp.ExactLP=old.basis.invert=old.basis.basis_packet=old.Discovery=M.best_absorption=M.plan=forbidden
    try:
        for inp,out in saved:M.require(M.verify(inp,json.loads(json.dumps(out['certificate'])))==out['verified'],'search-free replay')
    finally:old.lp.ExactLP,old.basis.invert,old.basis.basis_packet,old.Discovery,M.best_absorption,M.plan=original
    return {'status':'PASS','stage':'geometry','models':reports,'negative_controls':negative,
             'search_disabled_audits':len(saved),'seconds':round(time.monotonic()-start,3)},fixtures,saved


def wedge_data(n,multiplicity):
    A,b=cyclic(n);baseV,adj,dist,attempts=exact_reference(A,b)
    # Initial endpoint pair of maximum reference distance; no original graph
    # is passed to the final segment construction after these test endpoints.
    x,y=max(((x,y)for x in baseV for y in baseV if x!=y),key=lambda xy:dist[xy[0]][xy[1]])
    x=list(x);y=list(y);groups=[[i]for i in range(n)];history=[]
    counts=[multiplicity]*n if type(multiplicity)is int else multiplicity
    for i,k in enumerate(counts):
        for _ in range(k-1):
            idx=i;oldrow=A[idx][:];rhs=b[idx];new=len(A)
            sx=rhs-sum(a*z for a,z in zip(oldrow,x));sy=rhs-sum(a*z for a,z in zip(oldrow,y))
            A=[row+[Q(0)] for row in A];A[idx][-1]=Q(1);A.append(oldrow+[-Q(1)]);b.append(rhs)
            x.append(sx);y.append(-sy);groups[i].append(new)
            history.append({'split_original_row':idx,'new_row':new,'start_slack':str(sx),'target_slack':str(sy)})
    return {'A':A,'b':b,'start':x,'target':y},groups,history,baseV


def family_stage():
    start=time.monotonic();rows=[];fixtures=[];cycles=[]
    for n in range(6,17):
        K,mac,report=M.cyclic_multiwedge_schedule([[i]for i in range(n)])
        stages,steps,_=M.audit_schedule(K,mac,1)
        M.require(not stages[-1].high(),'cycle schedule not flag')
        cycles.append(report)
    for n,p in ((6,1),(7,1),(8,1),(6,2),(7,2),(8,2),(8,3),(10,2),(12,2)):
        data,groups,history,baseV=wedge_data(n,p)
        A,b,x,y=old.parse(data);K,mac,schedule=M.cyclic_multiwedge_schedule(groups)
        bx,by=old.basis.basis_packet(A,b,x),old.basis.basis_packet(A,b,y)
        packet,report,path=M.construct_refined_route(K,len(x),frozenset(bx['active']),frozenset(by['active']),mac,1)
        original={}
        for F in path:
            I=sorted(F);inv=old.basis.invert([A[i]for i in I]);point=[sum(inv[j][k]*b[I[k]]for k in range(len(I)))for j in range(len(I))]
            original[F]=old.basis.basis_packet(A,b,point)
        D.audit_original(A,b,serial(list(original.values())),path)
        previous_stages,_,_=D.compress(K)
        previous_refined=D.ResidualRefinement(previous_stages[-1],len(x))
        extra=None
        if n==6 and p==2:
            V,adj,ds,tests=exact_reference(A,b)
            M.require(D.ordered(missing(len(A),list(V.values())))==K.missing,'wedge nonface recurrence')
            extra={'all_exact_square_systems':tests,'all_original_vertices':len(V),'reference_distance':ds[tuple(x)][tuple(y)]}
        r={'prior_twin_refined_vertices':len(previous_refined.vertices),'base_n':n,'multiplicity':p,'dimension':len(x),'original_facets':len(A),
           'exact_base_vertices':len(baseV),'base_graph_only':extra is None,
           'structural_complete_nonfaces':True,'generic_LP_classification_performed':False,
           'wedge_operations':len(history),**schedule,**report,'additional_full_reference':extra}
        rows.append(r);fixtures.append({'input':serial(data),'groups':groups,'wedge_history':history,
           'macros':mac,'refinement':packet,'original_vertices':serial(list(original.values())),'report':r})
        print('wedge',n,p,r['dimension'],r['refined_vertices'],r['all_pairs_bound'],r['original_edges'],flush=True)
    return {'status':'PASS','stage':'family','cycle_schedules':cycles,'multiwedges':rows,
            'seconds':round(time.monotonic()-start,3)},fixtures,[]


def serial(obj):return D.serial(obj)


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=('abstract','geometry','family'),required=True);arg=p.parse_args()
    r,fixture,_={'abstract':abstract,'geometry':graph_stage,'family':family_stage}[arg.stage]()
    r['scope']='Written absorption/potential/carrier argument and exact rational tests, not Lean/platform verification'
    files=['mixed_defect_absorption.py','test_mixed_defect_absorption.py','defect_incidence_compression.py',
           'original_facet_segments.py','simple_tangent_policy_audit.py','exact_farkas_lp.py','stellar_defect_budget.py']
    r['source_sha256']={name:hashlib.sha256((ROOT/'scripts'/name).read_bytes()).hexdigest()for name in files}
    (ROOT/f'research/MIXED_ABSORPTION_{arg.stage.upper()}_TESTS.json').write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    if fixture is not None:(ROOT/f'fixtures/mixed_absorption_{arg.stage}.json').write_text(json.dumps(serial(fixture),sort_keys=True,indent=2)+'\n')
    print(json.dumps(r,sort_keys=True,indent=2))
if __name__=='__main__':main()
