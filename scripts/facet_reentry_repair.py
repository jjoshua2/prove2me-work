#!/usr/bin/env python3
"""Replace a facet-reentry excursion by a shorter certified path in that facet.

The raw path is a checked original-facet combinatorial segment. Each trial uses
UNCHANGED #253 on the two already supplied excursion endpoints, whose common
facet is automatically locked. A replacement is committed ONLY if strictly
shorter. This is not a polynomial bound on the number of original segment
edges or the work of failed repair trials. Non-shortening attempts are retained.
"""
from __future__ import annotations
from fractions import Fraction as Q
import argparse,json
from pathlib import Path
import original_facet_segments as seg
import two_face_acquisition as face
import simple_tangent_policy_audit as base


def original_path(data,c):
    seg.verify(data,c)
    points={tuple(p['active']):tuple(map(seg.rat,p['point']))for p in c['vertices']}
    return [points[tuple(F)]for F in c['path']]


def excursions(A,b,path):
    """Disjoint absence intervals for each original facet; no optimization."""
    last={};found=[]
    for j,x in enumerate(path):
        for i in base.active_rows(A,b,x):
            if i in last and last[i]<j-1:found.append((last[i],j,i))
            last[i]=j
    return sorted(found,key=lambda t:(-(t[1]-t[0]),t[0],t[2]))


def verify(data,c):
    A,b,u,v=seg.parse(data);path=original_path(data,c['segment']);initial=len(path)-1
    for record in c['repairs']:
        a,z,i=record['start_index'],record['end_index'],record['facet']
        seg.require(all(type(t)is int for t in(a,z,i)) and (a,z,i)in excursions(A,b,path),
                    'not an actual current original-facet excursion')
        out=face.verify(A,b,list(path[a]),list(path[z]),face.decode(record['route']))
        piece=[tuple(x)for x in out['loop_erased_path']]
        seg.require(len(piece)-1<z-a,'repair is not strictly shorter')
        seg.require(all(seg.dot(A[i],x)==b[i]for x in piece),'repair leaves the chosen original facet')
        path=path[:a]+piece+path[z+1:]
    seg.require(path[0]==u and path[-1]==v,'repaired path endpoints changed')
    labels=[frozenset(base.active_rows(A,b,x))for x in path];r=seg.ledger(labels,len(A),len(u))
    seg.require(len(c['repairs'])<=initial-r['original_edges'],'length descent failed')
    return {**r,'status':'PASS','input_segment_edges':initial,'accepted_repairs':len(c['repairs']),
            'saved_edges':initial-r['original_edges'],'path':seg.serial(path),
            'scope':'Strictly shorter original-facet splice; no universal bound or optimality guarantee.'}


def construct(data,segment_output,trial_cap=200,repair_edge_cap=10000):
    seg.require(type(trial_cap)is int and trial_cap>0,'invalid trial cap')
    A,b,u,v=seg.parse(data);sc=segment_output['certificate'];path=original_path(data,sc)
    trials=[];repairs=[];finished=True
    while True:
        moved=False
        for a,z,i in excursions(A,b,path):
            if len(trials)>=trial_cap:finished=False;break
            try:
                out=face.construct(A,b,list(path[a]),list(path[z]),edge_cap=repair_edge_cap)
            except ValueError as exc:
                # Explicitly incomplete trial, never a proof of absence/optimality.
                trials.append({'facet':i,'excursion_edges':z-a,'status':'incomplete','reason':str(exc)})
                continue
            piece=[tuple(x)for x in out['verified']['loop_erased_path']]
            trials.append({'facet':i,'excursion_edges':z-a,'replacement_edges':len(piece)-1,
                           'status':'accepted'if len(piece)-1<z-a else 'not_shorter'})
            if len(piece)-1<z-a:
                repairs.append({'start_index':a,'end_index':z,'facet':i,'route':seg.serial(out['certificate'])})
                path=path[:a]+piece+path[z+1:];moved=True;break
        if not moved:break
    cert={'segment':sc,'repairs':repairs};report=verify(data,cert)
    seg.require([list(map(seg.rat,x))for x in report['path']]==[list(x)for x in path],'repair replay mismatch')
    return {'certificate':cert,'verified':report,'trials':trials,
            'scan_completed':finished,'proof_boundary':'The repair need not be a combinatorial segment. Length decreases, not necessarily reentry count; failed trials have no polynomial bound.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('segment',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--trial-cap',type=int,default=200);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());s=json.loads(a.segment.read_text())
        a.output.write_text(json.dumps(seg.serial(construct(data,s,a.trial_cap)),sort_keys=True,indent=2)+'\n')
    except(ValueError,TypeError,KeyError,IndexError,OSError)as e:p.exit(2,f'No repaired-route certificate: {e}\n')
if __name__=='__main__':main()
