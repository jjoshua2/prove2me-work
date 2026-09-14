#!/usr/bin/env python3
"""Facet-acquisition-first simple ORIGINAL-H routing with phase objective resets.

An acquisition step may decrease the previous objective. It strictly shrinks
an invariant target face instead. A fixed target-normal objective improves on
all other steps in a phase. No polynomial count, LP extraction or projection
edge transport is asserted. Only simple bounded original-H instances supported.
"""
from __future__ import annotations
from fractions import Fraction as Q
import argparse, hashlib, json
from pathlib import Path
import simple_tangent_policy_audit as base
from simple_tangent_policy_audit import (require, rat, serial, dot, basis_packet,
    audit_basis, active_rows, feasible, maximal_step)


def problem_hash(A,b,start,target,policy):
    return hashlib.sha256(json.dumps(serial([A,b,start,target,policy]),sort_keys=True,
                                     separators=(',',':')).encode()).hexdigest()


def phase_objective(A,b,x,target):
    """Reciprocal target slacks at a PHASE anchor; hold fixed until acquisition.
    Coefficients of locked rows are omitted: they are constant on this face.
    Row-rescaling invariant. Normalize the initial objective gap to the number
    of remaining target facets; no external objective or optimized weights.
    """
    v,T,_=audit_basis(A,b,target)
    locked=[j for j in T if dot(A[j],x)==b[j]]
    missing=[j for j in T if j not in locked]
    require(missing,'nonstationary phase has no missing target facet')
    slacks={j:b[j]-dot(A[j],x) for j in missing}
    require(all(s>0 for s in slacks.values()),'negative target facet slack')
    f=[sum(Q(A[j][i])/slacks[j] for j in missing) for i in range(len(x))]
    require(dot(f,[v[i]-x[i] for i in range(len(x))])==len(missing),'incorrect phase normalization')
    return f,locked


def endpoint_signature(A,b,anchor,end,target):
    """Target-slack ratios remove coordinate-chart dependence in tie breaking.
    Original row labels fix only their order. Under positive row rescaling or
    any invertible affine coordinate change the entire tuple is unchanged.
    """
    return tuple(-Q(b[j]-dot(A[j],end))/(b[j]-dot(A[j],anchor))
        for j in target['active'] if b[j]-dot(A[j],anchor)>0)

def candidates(A,b,f,basis,target):
    x,J,D=audit_basis(A,b,basis);v,T,_=audit_basis(A,b,target)
    shared=set(J)&set(T)
    options=[]
    for i,j in enumerate(J):
        if j in shared:continue
        length,blocker=maximal_step(A,b,x,D[i])
        require(length>0,'zero step at a purported simple vertex')
        end=[a+length*r for a,r in zip(x,D[i])]
        # Feasibility + exact simple active set; producer checks no unseen graph.
        K=active_rows(A,b,end)
        require(feasible(A,b,end) and len(K)==len(x),'nonsimple endpoint is out of scope')
        require(set(J)-{j}<=set(K),'lost a second original active facet')
        gained=sorted((set(K)&set(T))-shared)
        gain=dot(f,[y-a for y,a in zip(end,x)])
        s=b[j]-dot(A[j],v)
        require(s>0,'released locked facet')
        options.append({'selected':i,'length':length,'blocker':blocker,'to':end,
          'gained':gained,'gain':gain,'normalized_gain':s*dot(f,D[i]),'released':j,'signature':endpoint_signature(A,b,x,end,target)})
    require(options,'nonterminal vertex has no free edge')
    # Exact full tangent identity proves at least one positive phase gain.
    disp=[a-c for a,c in zip(v,x)]
    require(all(disp[k]==sum((b[J[i]]-dot(A[J[i]],v))*D[i][k]
               for i in range(len(J)) if J[i] not in shared) for k in range(len(x))),
            'false target direction decomposition')
    require(sum(o['normalized_gain'] for o in options)==dot(f,disp)>0,
            'phase objective not strict on the current target face')
    return options,sorted(shared)


def choose(options,policy):
    require(policy in ('facet_first','reset_gain','reset_slack'),'unknown phase policy')
    # Acquisition deliberately need not improve the OLD phase objective.
    gains=[o for o in options if o['gained']]
    if policy=='facet_first' and gains:
        return max(gains,key=lambda o:(len(o['gained']),o['gain'],o['signature']))
    good=[o for o in options if o['gain']>0]
    require(good,'positive target-normal phase direction was lost')
    if policy=='reset_slack':
        return max(good,key=lambda o:(o['normalized_gain'],o['gain'],o['signature']))
    return max(good,key=lambda o:(o['gain'],o['signature']))


def block_choice(A,b,f,basis,target,policy,lookahead):
    """Producer for a shortest acquisition block inside a radius TWO neighborhood.
    Inverse computations generate witnesses only. Every possible first neighbor
    is independently certified before ruling out length-two acquisition.
    """
    require(type(lookahead)is int and lookahead in (1,2),'lookahead must be 1 or 2')
    opts,_=candidates(A,b,f,basis,target)
    packet={'basis':basis,'lookahead_bases':[]}
    if policy!='facet_first' or lookahead==1 or any(o['gained'] for o in opts):
        packet['selected_block']=[choose(opts,policy)['selected']]
        return packet
    exits=[]
    for a in opts:
        bs=basis_packet(A,b,a['to']);packet['lookahead_bases'].append({'first':a['selected'],'basis':bs})
        nxt,_=candidates(A,b,f,bs,target)
        for b2 in nxt:
            if b2['gained']:exits.append((a,b2))
    if exits:
        a,b2=max(exits,key=lambda pair:(len(pair[1]['gained']),pair[0]['gain']+pair[1]['gain'],
                                      endpoint_signature(A,b,basis['point'],pair[1]['to'],target),
                                      endpoint_signature(A,b,basis['point'],pair[0]['to'],target)))
        packet['selected_block']=[a['selected'],b2['selected']]
    else:packet['selected_block']=[choose(opts,policy)['selected']]
    return packet


def audit_block(A,b,f,target,packet,policy,lookahead):
    """Finite arithmetic certificate audit; never call a basis/neighbor solver."""
    opts,_=candidates(A,b,f,packet['basis'],target)
    root={o['selected']:o for o in opts};bymiddle={};exits=[];neighbor_count=0
    inspect=(policy=='facet_first' and lookahead==2 and not any(o['gained'] for o in opts))
    require(type(packet['lookahead_bases'])is list,'malformed lookahead witnesses')
    if inspect:
        require(len(packet['lookahead_bases'])==len(opts),'missing or extra first-neighbor certificate')
        for a,item in zip(opts,packet['lookahead_bases']):
            require(type(item['first'])is int and item['first']==a['selected'],'wrong lookahead order')
            bs=item['basis'];require(bs['point']==a['to'],'lookahead point not bound to full original edge')
            nxt,_=candidates(A,b,f,bs,target);neighbor_count+=len(nxt)
            bymiddle[a['selected']]=(bs,{b2['selected']:b2 for b2 in nxt})
            for b2 in nxt:
                if b2['gained']:exits.append((a,b2))
    else:require(not packet['lookahead_bases'],'unexpected lookahead witnesses')
    if exits:
        a,b2=max(exits,key=lambda pair:(len(pair[1]['gained']),pair[0]['gain']+pair[1]['gain'],
                                      endpoint_signature(A,b,packet['basis']['point'],pair[1]['to'],target),
                                      endpoint_signature(A,b,packet['basis']['point'],pair[0]['to'],target)))
        chosen=[a,b2];bs=[packet['basis'],bymiddle[a['selected']][0]]
    else:chosen=[choose(opts,policy)];bs=[packet['basis']]
    want=[a['selected'] for a in chosen]
    require(type(packet['selected_block'])is list and all(type(i)is int for i in packet['selected_block'])
            and packet['selected_block']==want,'incorrect complete acquisition block')
    if len(chosen)==2:
        require(not chosen[0]['gained'] and chosen[1]['gained'],'not a first-hit block')
    steps=[]
    for a,basis in zip(chosen,bs):
        steps.append({'basis':basis,**{k:a[k] for k in ('selected','length','blocker','to')},
                      'gain':a['gain'],'new_target_facets':a['gained']})
    return steps,{'incident_candidates':len(opts),'lookahead_candidates':neighbor_count,
                  'new_target_facets':chosen[-1]['gained'],'ends_phase':bool(chosen[-1]['gained'])}

def construct(A,b,start,v,policy='facet_first',edge_cap=10000,lookahead=2):
    require(type(edge_cap)is int and edge_cap>=0,'invalid edge cap')
    require(type(lookahead)is int and lookahead in (1,2),'lookahead must be 1 or 2')
    target=basis_packet(A,b,v);x=list(start);audit_basis(A,b,basis_packet(A,b,x))
    phases=[];count=0
    while x!=list(v):
        f,locked=phase_objective(A,b,x,target)
        phase={'anchor':list(x),'objective':f,'locked':locked,'blocks':[]}
        while x!=list(v):
            require(count<edge_cap,'route cap: no completion or negative verdict')
            p=block_choice(A,b,f,basis_packet(A,b,x),target,policy,lookahead)
            steps,r=audit_block(A,b,f,target,p,policy,lookahead)
            require(count+len(steps)<=edge_cap,'route cap before committing a complete acquisition block')
            phase['blocks'].append(p);count+=len(steps);x=steps[-1]['to']
            if r['ends_phase']:break
        phases.append(phase)
    cert={'format':'target-phase-v2','policy':policy,'lookahead':lookahead,'target_basis':target,'phases':phases,
      'problem_sha256':problem_hash(A,b,start,v,[policy,lookahead])}
    verify(A,b,start,v,cert)
    return cert


def verify(A,b,start,v,cert):
    require(cert['format']=='target-phase-v2','unknown format')
    policy=cert['policy'];require(policy in ('facet_first','reset_gain','reset_slack'),'unknown policy')
    lookahead=cert['lookahead'];require(type(lookahead)is int and lookahead in (1,2),'invalid lookahead')
    require(cert['problem_sha256']==problem_hash(A,b,start,v,[policy,lookahead]),'changed input')
    target=cert['target_basis'];tv,T,_=audit_basis(A,b,target);require(tv==list(v),'wrong target')
    x=list(start);seen={tuple(x)};reports=[];initial=len(set(active_rows(A,b,x))&set(T));edges=0
    candidate_count=neighbor_count=0;path=[x]
    for phase in cert['phases']:
        require(phase['anchor']==x and phase['blocks'],'invalid or empty phase')
        f,locked=phase_objective(A,b,x,target)
        require(phase['objective']==f and all(type(z)in (int,Q) for z in phase['objective']),'changed phase objective')
        require(phase['locked']==locked,'false locked-face record')
        negative=zero=phase_edges=lookahead_blocks=0
        for i,p in enumerate(phase['blocks']):
            require(p['basis']['point']==x,'discontinuous phase route')
            steps,r=audit_block(A,b,f,target,p,policy,lookahead)
            candidate_count+=r['incident_candidates'];neighbor_count+=r['lookahead_candidates']
            require(r['ends_phase']==(i==len(phase['blocks'])-1),'phase did not end at its first acquisition')
            lookahead_blocks+=len(steps)==2
            for step in steps:
                x=step['to'];edges+=1;phase_edges+=1
                require(tuple(x)not in seen,'repeated original vertex');seen.add(tuple(x));path.append(x)
                negative+=step['gain']<0;zero+=step['gain']==0
        reports.append({'edges':phase_edges,'constant_face_edges':phase_edges-1,
          'target_facets_before':locked,'target_facets_after':sorted(set(active_rows(A,b,x))&set(T)),
          'old_phase_decreasing_edges':negative,'old_phase_zero_edges':zero,
          'two_edge_acquisition_blocks':lookahead_blocks})
    require(x==list(v),'target not reached')
    require(len(reports)<=len(v)-initial,'too many strict face acquisitions')
    return {'status':'PASS','policy':policy,'lookahead':lookahead,'edges':edges,'phases':reports,
       'max_constant_face_edges':max((r['constant_face_edges'] for r in reports),default=0),
       'incident_candidates_audited':candidate_count,'lookahead_candidates_audited':neighbor_count,
       'path':path,'source_or_image_graph_supplied':False,
       'scope':'Exact finite simple original-H route; no polynomial phase/route bound or Lean-extracted parser.'}


def decode_certificate(c):
    if 'certificate'in c:c=c['certificate']
    def basis(bs):return {'point':list(map(rat,bs['point'])),'active':bs['active'],
             'directions':[list(map(rat,r)) for r in bs['directions']]}
    out={k:c[k] for k in ('format','policy','problem_sha256','lookahead')};out['target_basis']=basis(c['target_basis']);out['phases']=[]
    for p in c['phases']:
        q={'anchor':list(map(rat,p['anchor'])),'objective':list(map(rat,p['objective'])),'locked':p['locked'],'blocks':[]}
        for a in p['blocks']:
            q['blocks'].append({'basis':basis(a['basis']),'selected_block':a['selected_block'],
                'lookahead_bases':[{'first':w['first'],'basis':basis(w['basis'])} for w in a['lookahead_bases']]})
        out['phases'].append(q)
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--certificate',type=Path);p.add_argument('--policy',choices=['facet_first','reset_gain','reset_slack'],default='facet_first')
    p.add_argument('--edge-cap',type=int,default=10000);p.add_argument('--lookahead',type=int,choices=[1,2],default=2);a=p.parse_args()
    try:
        d=json.loads(a.input.read_text());A=[list(map(rat,r)) for r in d['A']];b=list(map(rat,d['b']))
        u=list(map(rat,d['start']));v=list(map(rat,d['target']))
        require(A and A[0] and len(A)==len(b) and all(len(r)==len(u)==len(v) for r in A),'bad input shape')
        c=decode_certificate(json.loads(a.certificate.read_text())) if a.certificate else construct(A,b,u,v,a.policy,a.edge_cap,a.lookahead)
        a.output.write_text(json.dumps(serial({'certificate':c,'verified':verify(A,b,u,v,c)}),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No certified route: {exc}\n')
if __name__=='__main__':main()
