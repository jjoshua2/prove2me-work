#!/usr/bin/env python3
"""Audited mixed-incidence stellar moves and bounded, net-decreasing macros.

Research implementation: finite original-H classification can be exponential.
A completed flag refinement gives a classical flag-normal route bound; neither
universal cheap refinement nor Lean verification is asserted. Existing #261
stellar updates/carriers and #258 original edge checks are reused unchanged.
"""
from __future__ import annotations
from itertools import combinations
from pathlib import Path
import argparse, json
import defect_incidence_compression as prior

require, serial = prior.require, prior.serial


def weight(K):
    return sum(len(N)-2 for N in K.high())


def label_pair(E,n):
    require(type(E) in (list,tuple) and len(E)==2 and
            all(type(i)is int and 0<=i<n for i in E) and E[0]<E[1], 'invalid edge labels')
    return frozenset(E)


def candidates(K):
    return sorted({E for N in K.high() for E in combinations(sorted(N),2)})


def absorption(K, edge):
    """Return explicit blockers for ALL mixed descendants, or None.
    No supposition that unequal incidences are inherently unsafe is made.
    """
    E=label_pair(edge,K.n)
    shared=[N for N in K.high() if E<=N]
    if not shared:return None
    atoms=[N for N in K.missing if E<=N or (len(N)==2 and N&E)]
    records=[]
    for N in K.high():
        if len(N&E)!=1:continue
        blockers=[B for B in atoms if B-E <= N-E]
        if not blockers:return None
        records.append({'mixed':sorted(N),'blocker':sorted(min(blockers,key=lambda S:(len(S),tuple(sorted(S)))))})
    return {'edge':list(edge),'shared':[sorted(N) for N in shared],'mixed_blockers':records}


def audit_absorption(K,packet):
    E=label_pair(packet['edge'],K.n)
    require(K.ask(E),'not a face edge')
    shared=[N for N in K.high() if E<=N]
    require(type(packet['shared']) is list and all(type(row) is list and all(type(i) is int for i in row) for row in packet['shared']), 'invalid shared labels')
    require(shared and packet['shared']==[sorted(N) for N in shared],'incorrect shared defects')
    mixed=[N for N in K.high() if len(N&E)==1]
    rows=packet['mixed_blockers']
    require(len(rows)==len(mixed),'missing or duplicate mixed audit')
    for N,r in zip(mixed,rows):
        require(type(r['mixed']) is list and all(type(i) is int for i in r['mixed']) and r['mixed']==sorted(N),'wrong mixed-descendant identity')
        require(type(r['blocker']) is list and all(type(i) is int and 0<=i<K.n for i in r['blocker']), 'invalid blocker labels')
        B=frozenset(r['blocker'])
        require(sorted(B)==r['blocker'] and B in K.missing,'blocker not an original minimal nonface')
        require(E<=B or (len(B)==2 and B&E),'blocker is neither shared nor a pair')
        require(B-E <= N-E,'blocker does not absorb this descendant')
    J=prior.stellar(K,E)
    expected=prior.ordered([N for N in K.high() if not E<=N]+
                          [(N-E)|{K.n} for N in shared if len(N)>=4])
    require(J.high()==expected,'exact absorbed update failed')
    require(weight(J)==weight(K)-len(shared),'exact defect-size decrease failed')
    return J


def best_absorption(K):
    out=[]
    for E in candidates(K):
        p=absorption(K,E)
        if p is not None:
            out.append((-len(p['shared']),-sum(len(N)==3 for N in p['shared']),E,p))
    return min(out,key=lambda x:x[:3])[-1] if out else None


def plan(K, macro_cap=3, total_cap=2000, trial_cap=2000):
    """Prefer one absorbed move. At a stall try ONE arbitrary move followed by
    absorbed moves; accept only a macro of <= macro_cap moves with net W decrease.
    Trial exploration and residual completion are NOT assumed polynomial.
    """
    require(all(type(i)is int and i>0 for i in (macro_cap,total_cap,trial_cap)), 'invalid planner caps')
    start_weight=weight(K); macros=[]; trials=0; work_steps=0
    while K.high():
        p=best_absorption(K)
        if p:
            macro={'kind':'absorbed','moves':[p],'weight_before':weight(K)}
            J=audit_absorption(K,p)
        else:
            options=[]
            if macro_cap>1:
                for E in candidates(K):
                    if trials>=trial_cap:break
                    trials+=1;J=prior.stellar(K,E)
                    moves=[{'edge':list(E)}]
                    while len(moves)<macro_cap and J.high():
                        p=best_absorption(J)
                        if p is None:break
                        J=audit_absorption(J,p);moves.append(p)
                    if weight(J)<weight(K):
                        options.append((weight(J),len(moves),E,J,moves))
            if not options:break
            _,_,_,J,moves=min(options,key=lambda x:x[:3])
            macro={'kind':'bridge','moves':moves,'weight_before':weight(K)}
        if work_steps+len(macro['moves'])>total_cap:break
        macro['weight_after']=weight(J);macros.append(macro)
        work_steps+=len(macro['moves']);K=J
    summary={'initial_weight':start_weight,'residual_weight':weight(K),'macro_count':len(macros),
             'stellar_steps':work_steps,'macro_cap':macro_cap,'bridge_trials':trials,
             'flag_reached':not K.high(),'residual_higher_defects':len(K.high()),
             'certified_step_budget':macro_cap*(start_weight-weight(K))}
    require(work_steps<=summary['certified_step_budget'],'macro budget')
    return macros,summary


def audit_schedule(K,macros,macro_cap):
    require(type(macro_cap)is int and macro_cap>=1,'bad macro cap')
    stages=[K];steps=[];weights=[];w0=weight(K)
    for macro in macros:
        require(macro['kind'] in ('absorbed','bridge'),'unknown macro kind')
        moves=macro['moves'];require(1<=len(moves)<=macro_cap,'macro length outside budget')
        require(type(macro['weight_before']) is int and type(macro['weight_after']) is int and macro['weight_before']==weight(K),'wrong checkpoint weight')
        before=weight(K)
        if macro['kind']=='absorbed':require(len(moves)==1,'absorbed macro must have one move')
        for i,p in enumerate(moves):
            E=label_pair(p['edge'],K.n)
            if i==0 and macro['kind']=='bridge':
                require(any(E<=N for N in K.high()),'bridge does not address a higher defect')
                J=prior.stellar(K,E)
            else:J=audit_absorption(K,p)
            steps.append({'edge':sorted(E),'new_label':K.n})
            weights.append([weight(K),weight(J)]);K=J;stages.append(K)
        require(weight(K)<before and macro['weight_after']==weight(K),'macro has no strict net progress')
    require(len(steps)<=macro_cap*(w0-weight(K)),'global macro accounting failed')
    return stages,steps,weights


def construct_refined_route(K,d,F,H,macros,macro_cap,residual_cap=100000,vertex_cap=2000):
    stages,steps,weights=audit_schedule(K,macros,macro_cap)
    R=prior.ResidualRefinement(stages[-1],d,residual_cap,vertex_cap)
    U,V=prior.lift_pair(F,H,steps);X,Y=R.lift(U,U&V),R.lift(V,U&V)
    M=len(R.vertices);require(M>=d,'refined dimension impossible')
    alg=prior.old.Segment(M,d,R,max(1,M-d),(4*d+4)*(max(1,M-d)+1))
    fine=alg.between(X&Y,X,Y)
    require(prior.old.ledger(fine,M,d)['nonrevisiting'],'refined flag segment reentered')
    current=[R.carrier(T) for T in fine]
    for j in reversed(range(len(steps))):
        E=frozenset(steps[j]['edge']);z=steps[j]['new_label']
        current=[(T-{z})|E if z in T else T for T in current]
        require(all(len(T)==d and stages[j].ask(T) for T in current),'invalid intermediate carrier')
        require(all(A==B or len(A&B)==d-1 for A,B in zip(current,current[1:])), 'carrier made a chord')
    path=[]
    for T in current:
        if not path or T!=path[-1]:path.append(T)
    require(path[0]==F and path[-1]==H and all(F&H<=T for T in path),'endpoint/common-face transport')
    require(len(path)-1<=len(fine)-1<=M-d,'original route exceeds refined bound')
    packet={'residual_vertices':[sorted(T) for T in R.vertices],
            'refined_path':[sorted(T) for T in fine],'original_path':[sorted(T) for T in path]}
    report={'refined_vertices':M,'refined_edges':len(fine)-1,'original_edges':len(path)-1,
            'all_pairs_bound':M-d,'stationary_steps':len(fine)-len(path),
            'stellar_steps':len(steps),'macro_count':len(macros),'macro_cap':macro_cap,
            'initial_weight':weight(K),'residual_weight':weight(stages[-1]),
            'residual_higher_labels':len(R.core),'residual_nonempty_faces':M-R.core_start,
            'step_weights':weights,'growing_individual_steps':sum(b>a for a,b in weights),
            'neutral_individual_steps':sum(b==a for a,b in weights),
            'original_facet_reentries':prior.old.ledger(path,K.n,d)['reentry_debt']}
    return packet,report,path


def construct(data,macro_cap=3,classification_cap=500000,trial_cap=2000):
    A,b,u,v=prior.old.parse(data);d=len(u);m=len(A)
    pu,pv=prior.old.basis.basis_packet(A,b,u),prior.old.basis.basis_packet(A,b,v)
    O=prior.old.Discovery(A,b,u,v,20000,1000000)
    K,work=prior.classify(m,d,O,classification_cap)
    macros,planning=plan(K,macro_cap,trial_cap=trial_cap)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    pathpacket,report,path=construct_refined_route(K,d,F,H,macros,macro_cap)
    packets={T:prior.old.basis.basis_packet(A,b,O.point(T)) for T in path}
    cert={'format':'mixed-defect-absorption-v1','problem_sha256':prior.old.input_hash(A,b,u,v),
          'limits':{'classification':classification_cap,'macro':macro_cap,'residual':100000,'vertices':2000},
          'minimal_nonfaces':[sorted(T) for T in K.missing],'macros':macros,'path':pathpacket,
          'boundedness':O.bounds,'vertices':list(packets.values()),'intersections':list(O.cache.values())}
    cert=serial(cert);verified=verify(data,cert)
    return {'certificate':cert,'verified':verified,'planner':planning,
            'discovery':{**work,'LP_maximizations':O.lp_calls,'LP_pivots':O.solver.pivots}}


def verify(data,c):
    A,b,u,v=prior.old.parse(data)
    require(c['format']=='mixed-defect-absorption-v1' and
            c['problem_sha256']==prior.old.input_hash(A,b,u,v),'wrong original input')
    prior.old.audit_bounds(A,b,c['boundedness']);O=prior.old.Certified(A,b,c['intersections'])
    K,_=prior.classify(len(A),len(u),O,c['limits']['classification'])
    require(c['minimal_nonfaces']==[sorted(T) for T in K.missing],'incomplete defect list')
    F=frozenset(prior.old.basis.active_rows(A,b,u));H=frozenset(prior.old.basis.active_rows(A,b,v))
    p,r,path=construct_refined_route(K,len(u),F,H,c['macros'],c['limits']['macro'],
                                   c['limits']['residual'],c['limits']['vertices'])
    require(c['path']==p,'incorrect refined/original path')
    V=prior.audit_original(A,b,c['vertices'],path)
    require(V[F][0]==u and V[H][0]==v,'wrong geometric endpoints')
    return {'status':'PASS','dimension':len(u),'original_facets':len(A),**r,
            'scope':'Exact original-row/carrier and potential-checkpoint audits; research, not Lean/Prove2Me.'}


def cyclic_multiwedge_schedule(groups):
    """Explicit ALL-SIZE schedule for multiwedges of the polar cyclic 4-polytope.
    Geometry is established separately; this is not a supplied arbitrary graph.
    """
    n=len(groups);require(n>=6 and all(groups),'need at least six nonempty groups')
    flat=[i for G in groups for i in G];require(all(type(i) is int for i in flat) and sorted(flat)==list(range(len(flat))),'group labels not a partition')
    triples=[T for T in combinations(range(n),3) if all((i-j)%n not in (1,n-1) for i,j in combinations(T,2))]
    K=prior.Complex(len(flat),[set().union(*(set(groups[i]) for i in T)) for T in triples])
    original=K;macros=[];representatives=[]
    def perform(E):
        nonlocal K
        E=tuple(sorted(E));p=absorption(K,E);require(p is not None,'cyclic schedule lacks absorption certificate')
        J=audit_absorption(K,p);macros.append({'kind':'absorbed','moves':[p],
                   'weight_before':weight(K),'weight_after':weight(J)});K=J
    for G in groups:
        work=list(G)
        while len(work)>1:
            u,v=work[:2];new=K.n;perform((u,v));work=[new]+work[2:]
        representatives.append(work[0])
    clone_steps=len(macros)
    for i in range(n):
        E={representatives[(i-1)%n],representatives[(i+1)%n]}
        if any(E<=N for N in K.high()):perform(E)
    first_steps=len(macros)-clone_steps
    a=n//2
    for block in (representatives[:a],representatives[a:]):
        for E in combinations(block,2):
            if any(set(E)<=N for N in K.high()):perform(E)
    require(not K.high(),'cyclic schedule did not finish')
    cap=a*(a-1)//2+(n-a)*(n-a-1)//2-n+6
    require(clone_steps==len(flat)-n and len(macros)-clone_steps<=cap,'cyclic all-size step count')
    return original,macros,{'base_labels':n,'original_labels':len(flat),'clone_compressions':clone_steps,
             'distance_two_steps':first_steps,'base_cleanup_steps':len(macros)-clone_steps,
             'base_step_cap':cap,'final_refined_labels':K.n,
             'all_pairs_bound':K.n-(4+len(flat)-n),
             'structural_all_pairs_bound':len(flat)-4+cap}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',type=Path)
    p.add_argument('--macro-cap',type=int,default=3);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data,a.macro_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as e:
        p.exit(2,f'No completed mixed-defect certificate: {e}\n')
if __name__=='__main__':main()
