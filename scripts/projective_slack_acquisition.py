#!/usr/bin/env python3
"""Projectively invariant target-face acquisition on simple original H-polytopes.

Reuse #253's complete original two-face certificates, but compare the MINIMUM
SHARE of target slack, not its radial sum. At phase anchor p put
z_j(x)=slack_j(x)/slack_j(p) for missing target rows and
rho(x)=min(z_j(x))/sum(z_j(x)). Positive projective transformations multiply
all z_j(x) by the same factor, so this score and all tie signatures survive.

If there is no acquisition, move to a minimum-rho inspected corner by a
SHORTEST polygon arc. Only decision anchors must strictly decrease rho; an
intermediate vertex may raise it. Every improving inspected face retires.
The resulting original-facet subset bound is still exponential in general.
This is exact research software, not a Lean-extracted or nonsimple solver.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import argparse, json
import two_face_acquisition as old

base=old.base
require,rat,serial,dot=old.require,old.rat,old.serial,old.dot


def phase_rows(A,b,anchor,target):
    _,T,_=base.audit_basis(A,b,target)
    locked=sorted(set(base.active_rows(A,b,anchor))&set(T))
    missing=[j for j in T if j not in locked]
    require(missing,'nonterminal phase must have a missing target facet')
    return locked,missing


def shares(A,b,anchor,x,T):
    rows=[j for j in T if b[j]-dot(A[j],anchor)>0]
    require(rows,'empty target slack coordinate system')
    z=[(b[j]-dot(A[j],x))/(b[j]-dot(A[j],anchor)) for j in rows]
    require(all(s>=0 for s in z),'negative target slack')
    total=sum(z,Q(0))
    # The unique target has zero denominator and is handled as acquisition,
    # never as a nonterminal fallback state.
    return tuple(s/total for s in z) if total else tuple(Q(0) for _ in z)


def score(A,b,anchor,x,T):
    return min(shares(A,b,anchor,x,T))


def options(A,b,anchor,target,root,neighbors,faces):
    T=target['active'];locked=set(base.active_rows(A,b,root))&set(T)
    def hit(z):return bool((set(base.active_rows(A,b,z))&set(T))-locked)
    def signature(z):return tuple(-s for s in shares(A,b,anchor,z,T))
    def tie(path):return signature(path[-1]),tuple(signature(z) for z in path)
    immediate=[n for n in neighbors if hit(n['to'])]
    if immediate:
        n=max(immediate,key=lambda n:tie([n['to']]))
        return {'kind':'edge_acquisition','selected':n['selected'],'path':[n['to']]}
    acquisition=[];descent=[];rho=score(A,b,anchor,root,T)
    for face in faces:
        C=face['corners'];q=len(C)
        for sign in (1,-1):
            path=[]
            for count in range(1,q):
                z=C[(sign*count)%q]['point'];path.append(z)
                record={'fixed_rows':face['fixed_rows'],'sign':sign,'count':count,'path':list(path)}
                if hit(z):
                    acquisition.append({'kind':'face_acquisition',**record});break
                if score(A,b,anchor,z,T)<rho:
                    descent.append({'kind':'face_descent',**record})
    if acquisition:return max(acquisition,key=lambda o:(-len(o['path']),)+tie(o['path']))
    require(descent,'no eligible slack-share descent: simple bounded input premise failed')
    return max(descent,key=lambda o:(-score(A,b,anchor,o['path'][-1],T),-len(o['path']))+tie(o['path']))


def produce(A,b,anchor,target,root,cache):
    if tuple(root) not in cache:cache[tuple(root)]=base.basis_packet(A,b,root)
    bs=cache[tuple(root)];locked,_=phase_rows(A,b,root,target)
    ns=old.neighbors(A,b,bs,locked);T=set(target['active'])
    direct=any((set(base.active_rows(A,b,n['to']))&T)-set(locked) for n in ns)
    free=[j for j in bs['active'] if j not in locked];faces=[]
    if not direct:
        require(len(free)>=2,'a retained segment must directly reach its target')
        for i,j in combinations(free,2):
            fixed=[r for r in bs['active'] if r not in (i,j)]
            faces.append(old.trace_face(A,b,root,fixed,cache))
    selected=options(A,b,anchor,target,root,ns,faces)
    return {'basis':bs,'faces':faces,'selection':old.selection_only(selected)}


def audit_decision(A,b,anchor,target,c):
    root,J,D=base.audit_basis(A,b,c['basis']);y,T,_=base.audit_basis(A,b,target)
    locked=sorted(set(J)&set(T));ns=old.neighbors(A,b,c['basis'],locked)
    require(ns,'nonterminal state has no eligible edge')
    rho=score(A,b,anchor,root,T);require(rho>0,'a phase already acquired a target row')
    immediate=any((set(base.active_rows(A,b,n['to']))&set(T))-set(locked) for n in ns)
    free=[j for j in J if j not in locked]
    expected=[] if immediate else [[r for r in J if r not in (i,j)] for i,j in combinations(free,2)]
    require(len(c['faces'])==len(expected),'incomplete incident two-face cover')
    for fixed,face in zip(expected,c['faces']):old.audit_face(A,b,root,fixed,face)
    if not immediate:
        # A local executable certificate of the decreasing-edge claim. The
        # written proof derives its existence from a minimum-share coordinate.
        require(any(score(A,b,anchor,n['to'],T)<rho for n in ns),'no strict share-decreasing original edge')
    chosen=options(A,b,anchor,target,root,ns,c['faces'])
    require(type(c['selection'])is dict and all(type(v)is int for k,v in c['selection'].items()
        if k in ('selected','sign','count')) and c['selection']==old.selection_only(chosen),'wrong macro selection')
    arc=chosen['path'];end=arc[-1];acquired=sorted((set(base.active_rows(A,b,end))&set(T))-set(locked))
    require(bool(acquired)==(chosen['kind']!='face_descent'),'wrong phase end')
    require(all(set(locked)<=set(base.active_rows(A,b,z)) for z in arc),'released a locked target facet')
    require(not any((set(base.active_rows(A,b,z))&set(T))-set(locked) for z in arc[:-1]),'not a first-acquisition prefix')
    cap=(len(A)-len(root)+2)//2
    require(len(arc)<=cap,'macro is not a shortest arc within the facet bound')
    labels=[]
    if not acquired:
        endrho=score(A,b,anchor,end,T);require(endrho<rho,'fallback does not decrease anchor potential')
        for face in c['faces']:
            vals=[score(A,b,anchor,bs['point'],T) for bs in face['corners']]
            require(endrho<=min(vals),'fallback does not minimize every inspected face')
            require(all(v>0 for v in vals),'fallback inspected a target acquisition')
            if min(vals)<rho:labels.append(tuple(face['fixed_rows']))
        require(len(labels)>=len(free)-1,'missing h-1 improving-face charges')
    oldf,unused=old.phase_objective(A,b,anchor,target)
    return arc,{'kind':chosen['kind'],'acquired':acquired,'retired_labels':labels,
        'faces':len(c['faces']),'traced_face_edges':sum(len(f['corners']) for f in c['faces']),
        'rho_before':rho,'rho_after':score(A,b,anchor,end,T),
        'intermediate_rho_increases':sum(score(A,b,anchor,z,T)>score(A,b,anchor,x,T)
            for x,z in zip([root]+arc[:-1],arc)),
        'old_phase_objective_decreases':sum(dot(oldf,[v-u for u,v in zip(x,z)])<0
            for x,z in zip([root]+arc[:-1],arc))}


def construct(A,b,start,target,edge_cap=10000):
    A,b,start,target=old.parse(A,b,start,target)
    require(type(edge_cap)is int and edge_cap>=0,'invalid edge cap')
    tbs=base.basis_packet(A,b,target);x=start;cache={};phases=[];count=0
    while x!=target:
        locked,missing=phase_rows(A,b,x,tbs);phase={'anchor':x,'locked':locked,'decisions':[]}
        while x!=target:
            require(count<edge_cap,'route cap; no complete route claimed')
            dc=produce(A,b,phase['anchor'],tbs,x,cache)
            arc,info=audit_decision(A,b,phase['anchor'],tbs,dc)
            require(count+len(arc)<=edge_cap,'macro exceeds route cap')
            phase['decisions'].append(dc);count+=len(arc);x=arc[-1]
            if info['acquired']:break
        phases.append(phase)
    c={'format':'projective-slack-two-face-v1','problem_sha256':old.digest(A,b,start,target),
       'target_basis':tbs,'phases':phases}
    return {'certificate':c,'verified':verify(A,b,start,target,c)}


def verify(A,b,start,target,c):
    A,b,start,target=old.parse(A,b,start,target)
    require(c['format']=='projective-slack-two-face-v1' and c['problem_sha256']==old.digest(A,b,start,target),'changed original problem')
    bs=c['target_basis'];y,T,_=base.audit_basis(A,b,bs);require(y==target,'wrong target basis')
    x=start;path=[start];anchors=set();retired=set();phase_reports=[]
    r=len(start)-len(set(base.active_rows(A,b,start))&set(T));e=len(A)-len(start);a=(e+2)//2
    totals={'decisions':0,'fallbacks':0,'acquisitions':0,'faces':0,'traced_face_edges':0,
        'intermediate_rho_increases':0,'old_phase_objective_decreases':0,'retired_faces':0}
    for p in c['phases']:
        require(p['anchor']==x and p['decisions'],'empty or misanchored phase')
        locked,missing=phase_rows(A,b,x,bs);require(p['locked']==locked,'locked row mismatch')
        h=len(missing);fallbacks=0;phase_length=0
        for index,dc in enumerate(p['decisions']):
            require(tuple(x)not in anchors and dc['basis']['point']==x,'repeated or disconnected anchor')
            anchors.add(tuple(x));arc,info=audit_decision(A,b,p['anchor'],bs,dc)
            require(bool(info['acquired'])==(index==len(p['decisions'])-1),'phase not stopped at first acquisition')
            if not info['acquired']:
                require(h>=3,'a complete retained 2-face contains a target acquisition')
                labels=set(info['retired_labels'])
                require(not labels&retired,'reused improving-face charge')
                require(len(labels)>=h-1,'insufficient new face labels');retired|=labels
                fallbacks+=1;totals['retired_faces']+=len(labels)
            totals['decisions']+=1;totals['fallbacks']+=not bool(info['acquired']);totals['acquisitions']+=bool(info['acquired'])
            for key in ('faces','traced_face_edges','intermediate_rho_increases','old_phase_objective_decreases'):totals[key]+=info[key]
            path+=arc;phase_length+=len(arc);x=arc[-1]
        upper=comb(e,h-2)//(h-1) if h>=3 else 0
        require(fallbacks<=upper,'non-target facet-subset count exceeded')
        phase_reports.append({'dimension':h,'fallbacks':fallbacks,'subset_bound':upper,'edges':phase_length})
    require(x==target and len(c['phases'])<=r,'incomplete target route or too many phases')
    bound=a*(r+sum(comb(e,h-2)//(h-1) for h in range(3,r+1)))
    oldbound=a*r+(e+1)*sum(comb(e,h-2)//(h-1) for h in range(3,r+1))
    require(len(path)-1<=a*(r+totals['fallbacks'])<=bound,'quantitative macro bound failed')
    short=old.loop_erase(path)
    return {'status':'PASS','dimension':len(start),'original_rows':len(A),'committed_edges':len(path)-1,
        'loop_erased_edges':len(short)-1,'path':path,'loop_erased_path':short,'macro_edge_bound':a,
        'facet_subset_route_bound':bound,'previous_monotone_macro_bound':oldbound,'phases':phase_reports,**totals,
        'uniform_polynomial_bound_claimed':False,'global_graph_supplied':False,
        'scope':'Exact simple ORIGINAL-H routes and face budgets. Positive projective covariance is proved in the note; no Lean/platform verdict.'}


def decode(raw):
    c=raw.get('certificate',raw)
    def bs(z):return {'point':list(map(rat,z['point'])),'active':z['active'],
        'directions':[list(map(rat,v)) for v in z['directions']]}
    return {'format':c['format'],'problem_sha256':c['problem_sha256'],'target_basis':bs(c['target_basis']),
        'phases':[{'anchor':list(map(rat,p['anchor'])),'locked':p['locked'],
            'decisions':[{'basis':bs(dc['basis']),'selection':dc['selection'],
                'faces':[{'fixed_rows':f['fixed_rows'],'corners':[bs(z) for z in f['corners']]} for f in dc['faces']]} for dc in p['decisions']]} for p in c['phases']]}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--certificate',type=Path);p.add_argument('--edge-cap',type=int,default=10000);args=p.parse_args()
    try:
        d=json.loads(args.input.read_text());A,b,x,y=old.parse(d['A'],d['b'],d['start'],d['target'])
        out={'certificate':decode(json.loads(args.certificate.read_text()))} if args.certificate else construct(A,b,x,y,args.edge_cap)
        out['verified']=verify(A,b,x,y,out['certificate']);args.output.write_text(json.dumps(serial(out),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No complete projective-slack route: {exc}\n')
if __name__=='__main__':main()
