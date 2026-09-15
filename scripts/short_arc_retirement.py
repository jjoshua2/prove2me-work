#!/usr/bin/env python3
"""Shorten #253 fallback arcs without changing ANY decision endpoint.

The reference complete-two-face certificate is checked unchanged. Its globally
maximal fallback endpoint is then reached by the shortest boundary arc among
already audited incident polygons. Intermediate objective decrease is allowed;
anchor improvement, permanent target locks and retired-face labels are retained.
No new faces, neighbors, LP solutions or universal polynomial bound are assumed.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse, json
import two_face_acquisition as old

require, serial, dot = old.require, old.serial, old.dot


def route_choice(A,b,f,target,decision):
    root=decision['basis']['point']
    locked=sorted(set(decision['basis']['active']) & set(target['active']))
    options=old.neighbors(A,b,decision['basis'],locked)
    original=old.choose(A,b,f,target,root,options,decision['faces'])
    if original['kind']!='face_gain':
        return old.selection_only(original),original['path'],original['path']
    # Keep the original endpoint even when another maximum ties: this makes
    # the ENTIRE sequence of decision anchors identical to the reference.
    endpoint=original['path'][-1];routes=[]
    for face in decision['faces']:
        vertices=[bs['point'] for bs in face['corners']]
        if endpoint not in vertices:continue
        index=vertices.index(endpoint);q=len(vertices)
        require(index>0,'fallback maximum equals its anchor')
        for sign,count in ((1,index),(-1,q-index)):
            path=[vertices[(sign*k)%q] for k in range(1,count+1)]
            routes.append({'kind':'short_face_gain','fixed_rows':face['fixed_rows'],
                           'sign':sign,'count':count,'path':path})
    require(routes,'original maximizing endpoint absent from inspected faces')
    def quality(route):
        return (-len(route['path']),tuple(old.signature(A,b,root,x,target['active'])
                                         for x in route['path']))
    choice=max(routes,key=quality)
    require(choice['path'][-1]==endpoint,'changed certified maximum')
    return old.selection_only(choice),choice['path'],original['path']


def shorten(A,b,start,target,reference):
    """Transform a complete original certificate; validation is not optional."""
    old.verify(A,b,start,target,reference)
    choices=[]
    for phase in reference['phases']:
        choices.append([route_choice(A,b,phase['objective'],reference['target_basis'],dc)[0]
                        for dc in phase['decisions']])
    cert={'format':'short-arc-retirement-v1','reference':reference,'choices':choices}
    return {'certificate':cert,'verified':verify(A,b,start,target,cert)}


def construct(A,b,start,target,edge_cap=10000):
    reference=old.construct(A,b,start,target,edge_cap)['certificate']
    return shorten(A,b,start,target,reference)


def verify(A,b,start,target,certificate):
    """Finite audit, with original inverses and every polygon checked by #253.
    No discovery, elimination, LP, graph search, or inverse routine is called.
    """
    A,b,start,target=old.parse(A,b,start,target)
    require(certificate['format']=='short-arc-retirement-v1','unknown shortcut format')
    ref=certificate['reference'];baseline=old.verify(A,b,start,target,ref)
    choices=certificate['choices']
    require(type(choices)is list and len(choices)==len(ref['phases']),'missing or extra phase choices')
    T=ref['target_basis']['active'];path=[start];current=start;phase_edges=[];saved=0;backward=0;shortened=0
    old_anchors=[];new_anchors=[];fallback_edges=0
    for phase,chosen in zip(ref['phases'],choices):
        require(type(chosen)is list and len(chosen)==len(phase['decisions']),'incomplete decision choices')
        count=0
        for dc,given in zip(phase['decisions'],chosen):
            require(dc['basis']['point']==current,'changed reference decision anchor')
            expected,arc,original=route_choice(A,b,phase['objective'],ref['target_basis'],dc)
            require(type(given)is dict and all(type(v)is int for k,v in given.items()
                if k in ('selected','sign','count')) and given==expected,'incorrect shortest same-endpoint arc')
            require(arc and arc[-1]==original[-1] and len(arc)<=len(original),'lost endpoint or failed shortening')
            locked=set(dc['basis']['active'])&set(T)
            acquired=bool((set(old.base.active_rows(A,b,arc[-1]))&set(T))-locked)
            require(all(locked<=set(old.base.active_rows(A,b,z)) for z in arc),'lost a permanent target facet')
            require(not any((set(old.base.active_rows(A,b,z))&set(T))-locked for z in arc[:-1]),
                    'shortcut crosses a phase boundary early')
            if not acquired:
                require(expected['kind']=='short_face_gain','false fallback classification')
                require(dot(phase['objective'],arc[-1])>dot(phase['objective'],current),
                        'decision maximum did not improve')
                require(all(dot(phase['objective'],bs['point'])<=dot(phase['objective'],arc[-1])
                    for face in dc['faces'] for bs in face['corners']), 'lost global inspected-face dominance')
                fallback_edges+=len(arc)
                backward+=sum(dot(phase['objective'],v)<dot(phase['objective'],u)
                              for u,v in zip([current]+arc[:-1],arc))
            require(len(arc)<=(len(A)-len(start)+2)//2,'short arc exceeded the ORIGINAL-row half-perimeter bound')
            old_anchors.append(tuple(original[-1]));new_anchors.append(tuple(arc[-1]))
            saved+=len(original)-len(arc);shortened+=len(arc)<len(original)
            count+=len(arc);path+=arc;current=arc[-1]
        phase_edges.append(count)
    require(current==target and old_anchors==new_anchors,'decision trajectory changed')
    e=len(A)-len(start);r=len(start)-len(set(old.base.active_rows(A,b,start))&set(T));a=(e+2)//2
    slots=sum(comb(e,h-2)//(h-1) for h in range(3,r+1))
    cap=a*(r+slots);observed=a*(baseline['acquisition_decisions']+baseline['fallback_decisions'])
    require(len(path)-1<=cap and len(path)-1<=observed,'retirement-based short-arc bound failed')
    require(baseline['committed_edges']-(len(path)-1)==saved,'false saved-edge count')
    erased=old.loop_erase(path)
    return {'status':'PASS','committed_edges':len(path)-1,'loop_erased_edges':len(erased)-1,
        'reference_committed_edges':baseline['committed_edges'],
        'reference_loop_erased_edges':baseline['loop_erased_edges'],
        'saved_raw_edges':saved,'shortened_fallback_macros':shortened,'backward_fallback_edges':backward,
        'fallback_edges':fallback_edges,'fallback_decisions':baseline['fallback_decisions'],
        'retired_improving_faces':baseline['retired_improving_faces'],
        'same_decision_endpoints':old_anchors==new_anchors,'short_arc_per_macro_bound':a,
        'bound_using_observed_macros':observed,'improved_facet_subset_bound':cap,
        'reference_facet_subset_bound':baseline['original_facet_binomial_route_bound'],
        'phase_fallback_bounds':baseline['phase_fallback_bounds'],'phase_edges':phase_edges,
        'path':path,'loop_erased_path':erased,
        'audited_face_edge_occurrences':baseline['traced_face_edges'],
        'additional_faces_or_neighbors_searched':0,
        'scope':'Same-anchor shortening of complete original-face routes. Bound remains binomial/exponential; not Lean verification.'}


def decode(c):
    if 'certificate'in c:c=c['certificate']
    return {'format':c['format'],'reference':old.decode(c['reference']),'choices':c['choices']}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',type=Path)
    p.add_argument('--edge-cap',type=int,default=10000);args=p.parse_args()
    try:
        d=json.loads(args.input.read_text());A,b,x,y=old.parse(d['A'],d['b'],d['start'],d['target'])
        result={'certificate':decode(json.loads(args.certificate.read_text()))} if args.certificate else construct(A,b,x,y,args.edge_cap)
        result['verified']=verify(A,b,x,y,result['certificate'])
        args.output.write_text(json.dumps(serial(result),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No certified shortened route: {exc}\n')
if __name__=='__main__':main()
