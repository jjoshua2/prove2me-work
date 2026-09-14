#!/usr/bin/env python3
"""Target-aware simple ORIGINAL-H pivots with a search-free arithmetic auditor.

Only simple bounded H-polytopes are supported. This is not a replacement for
#248's general projected-image algorithm. Shared target facets remain fixed.
The target-slack rule normalizes each allowed incident direction by its target
slack; the alternative compares the COMPLETED edge gains on that same face.
No uniform polynomial bound or Lean extraction is claimed.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
import simple_tangent_policy_audit as base
from simple_tangent_policy_audit import (require, rat, serial, dot, audit_basis,
    basis_packet, active_rows, feasible, maximal_step, audit_target, decode_input)


def problem_hash(A, b, f, start, target):
    raw=serial([A,b,f,start,target])
    return hashlib.sha256(json.dumps(raw,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def choices(A,b,f,basis,target):
    """No inverse, rank, optimizer, or graph search. Check all incident columns."""
    x,J,D=audit_basis(A,b,basis)
    v=audit_target(A,b,f,target)
    shared=set(J)&set(target['active'])
    slack=[b[j]-dot(A[j],v) for j in J]
    require(all(s>=0 for s in slack),'target not feasible in active inequalities')
    eligible=[i for i,j in enumerate(J) if j not in shared]
    require(all(slack[i]>0 for i in eligible),'nonshared row has zero target slack')
    require(all(slack[i]==0 for i,j in enumerate(J) if j in shared),'shared row not tight at target')
    displacement=[vv-xx for xx,vv in zip(x,v)]
    require(all(displacement[k]==sum(slack[i]*D[i][k] for i in eligible)
                for k in range(len(x))),'false target displacement decomposition')
    gap=dot(f,displacement)
    require(gap>0,'already at target or target is not strict')
    candidates=[]
    for i in eligible:
        derivative=dot(f,D[i])
        if derivative<=0:continue
        length,blocker=maximal_step(A,b,x,D[i])
        require(length>0,'degenerate or unsupported zero step')
        y=[xx+length*rr for xx,rr in zip(x,D[i])]
        candidates.append({'index':i,'normalized_gain':slack[i]*derivative,
            'gain':length*derivative,'end':y,'length':length,'blocker':blocker,
            'blocking_fraction':length/slack[i]})
    require(candidates,'target displacement requires an improving allowed ray')
    normalized=[slack[i]*dot(f,D[i]) for i in eligible]
    require(sum(normalized)==gap,'target gap does not equal the sum of ray scores')
    return {'x':x,'J':J,'D':D,'shared':shared,'slack':slack,'eligible':eligible,
            'gap':gap,'candidates':candidates}


def key(c,policy):
    if policy=='target_slack':return c['normalized_gain'],c['gain'],tuple(c['end'])
    if policy=='full_gain_locked':return c['gain'],tuple(c['end'])
    raise ValueError('unknown target-aware policy')


def make_step(A,b,f,basis,target,policy):
    info=choices(A,b,f,basis,target)
    c=max(info['candidates'],key=lambda c:key(c,policy))
    return {'basis':basis,'selected':c['index'],'length':c['length'],
            'blocker':c['blocker'],'to':c['end']}


def audit_step(A,b,f,target,step,policy):
    info=choices(A,b,f,step['basis'],target)
    best=max(info['candidates'],key=lambda c:key(c,policy))
    require(type(step['selected'])is int and step['selected']==best['index'],'wrong selected direction')
    require(type(step['blocker'])is int and step['blocker']==best['blocker'],'wrong blocker')
    require(type(step['length'])in (int,Q) and step['length']==best['length'],'not a maximal original step')
    y=step['to'];require(len(y)==len(info['x']) and all(type(z)in (int,Q) for z in y),'inexact endpoint')
    require(y==best['end'] and feasible(A,b,y),'incorrect feasible endpoint')
    require(all(dot(A[j],y)==b[j] for j in info['shared']),'lost a previously acquired target facet')
    released=info['J'][best['index']]
    require(all(dot(A[j],y)==b[j] for j in info['J'] if j!=released),'not an original edge')
    if policy=='target_slack':
        # A positive height on the CURRENT COMMON FACE, not the ambient cone.
        s=info['slack'];h=[-sum(A[info['J'][i]][k]/s[i] for i in info['eligible']) for k in range(len(y))]
        for i in info['eligible']:
            require(dot(h,[s[i]*z for z in info['D'][i]])==1,'wrong face-tangent normalization')
        require(dot(h,[v-x for v,x in zip(target['point'],info['x'])])==len(info['eligible']),
                'target height must equal the number of remaining active directions')
        require(best['normalized_gain']*len(info['eligible'])>=info['gap'],
                'normalized progress below target-gap average')
    gain=dot(f,y)-dot(f,info['x'])
    require(gain==best['gain'] and gain>0,'not a strict improvement')
    return {'to':y,'gain':gain,'gap_before':info['gap'],
            'gap_fraction':gain/info['gap'],'blocking_fraction':best['blocking_fraction'],
            'remaining_face_directions':len(info['eligible']),
            'target_facets_before':sorted(info['shared']),
            'target_facets_after':sorted(set(active_rows(A,b,y))&set(target['active']))}


def construct(A,b,f,start,target,policy='target_slack',edge_cap=10000):
    require(type(edge_cap)is int and edge_cap>=0,'invalid edge cap')
    audit_target(A,b,f,target);x=list(start);steps=[]
    while x!=target['point']:
        require(len(steps)<edge_cap,'route cap: no completed path')
        s=make_step(A,b,f,basis_packet(A,b,x),target,policy)
        audit_step(A,b,f,target,s,policy);steps.append(s);x=s['to']
    out={'format':'target-aware-simple-v1','policy':policy,
         'problem_sha256':problem_hash(A,b,f,start,target),'steps':steps}
    verify(A,b,f,start,target,out)
    return out


def verify(A,b,f,start,target,cert):
    require(cert.get('format')=='target-aware-simple-v1','unknown certificate format')
    require(cert.get('problem_sha256')==problem_hash(A,b,f,start,target),'changed input or target')
    policy=cert['policy'];require(policy in ('target_slack','full_gain_locked'),'unknown policy')
    end=audit_target(A,b,f,target);x=list(start);seen={tuple(x)};reports=[]
    # Validate a stationary route rather than silently accepting arbitrary start.
    if x==end:audit_basis(A,b,target)
    for step in cert['steps']:
        require(step['basis']['point']==x,'discontinuous route')
        r=audit_step(A,b,f,target,step,policy);x=r['to']
        require(tuple(x)not in seen,'repeated vertex');seen.add(tuple(x));reports.append(r)
    require(x==end,'wrong or missing final endpoint')
    return serial({'status':'PASS','policy':policy,'original_edges':len(reports),
        'target_facets_never_lost':True,'steps':reports,
        'scope':'Finite simple original-H route; no general polynomial bound, projected-edge transport, or Lean verification.'})


def decode_certificate(c):
    if isinstance(c,dict) and 'certificate' in c and 'steps' not in c:c=c['certificate']
    require(type(c)is dict and type(c.get('steps'))is list,'malformed route')
    out={k:c[k] for k in ('format','policy','problem_sha256')};out['steps']=[]
    for s in c['steps']:
        bs=s['basis']
        basis={'point':[rat(x) for x in bs['point']],'active':bs['active'],
               'directions':[[rat(x) for x in r] for r in bs['directions']]}
        out['steps'].append({'basis':basis,'selected':s['selected'],'length':rat(s['length']),
                            'blocker':s['blocker'],'to':[rat(x) for x in s['to']]})
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--policy',choices=['target_slack','full_gain_locked'],default='target_slack')
    p.add_argument('--certificate',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--edge-cap',type=int,default=10000);args=p.parse_args()
    try:
        A,b,f,u,t=decode_input(json.loads(args.input.read_text()))
        c=decode_certificate(json.loads(args.certificate.read_text())) if args.certificate else construct(A,b,f,u,t,args.policy,args.edge_cap)
        args.output.write_text(json.dumps(serial({'certificate':c,'verified':verify(A,b,f,u,t,c)}),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:p.exit(2,f'No certified target-aware route: {exc}\n')
if __name__=='__main__':main()
