#!/usr/bin/env python3
"""Weighted accounting for the UNCHANGED #253 original two-face route.

This checks an existing route certificate, never changes or selects its path.
With at most three missing target facets, a planar incidence argument in the
written proof gives a LINEAR original-facet edge bound. Geometric simplicity
and boundedness remain the original algorithm's input class. No Lean claim.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
import two_face_acquisition as route
from simple_tangent_policy_audit import require,serial,active_rows,dot


def account(A,b,start,target,certificate):
    """No inverse, linear program, graph enumeration, or additional search.

    Complete original polygon cycles and the route policy are checked first by
    #253's unchanged auditor. The extra arithmetic checks bind selected facet
    charges, their distinctness, and actual macro lengths. The planar incidence
    upper bound is justified in the accompanying mathematical argument, not by
    trusting a graph supplied by a producer.
    """
    report=route.verify(A,b,start,target,certificate)
    d=len(start);m=len(A);T=set(certificate['target_basis']['active'])
    J=set(active_rows(A,b,start))&T;r=d-len(J);e=m-d
    require(r<=3,'linear tail accounting requires at most three missing target facets')
    require(e>=r,'not enough original non-target rows for the initial vertex')
    selected=set();cells=[];fallback_edges=0;acquisition_edges=0
    for phase in certificate['phases']:
        h=d-len(phase['locked']);f=phase['objective']
        for dc in phase['decisions']:
            arc,info=route.audit_decision(A,b,f,certificate['target_basis'],dc)
            if info['kind']!='face_gain':
                acquisition_edges+=len(arc)
                continue
            require(h==3 and set(phase['locked'])==J,'fallback outside the initial three-face')
            fixed=dc['selection']['fixed_rows'];free=set(fixed)-J
            require(J<=set(fixed) and len(free)==1,'selected polygon is not an intrinsic facet')
            label=next(iter(free))
            require(label not in T and label not in selected,'reused or target fallback facet')
            selected.add(label)
            face=next(q for q in dc['faces']if q['fixed_rows']==fixed)
            corners=[q['point']for q in face['corners']];size=len(corners)
            require(all((set(active_rows(A,b,z))&T)==J for z in corners),
                    'fallback polygon intersects a missing target facet')
            require(len(arc)<=size-1,'fallback arc exceeds its OWN polygon size')
            require(dot(f,arc[-1])==max(dot(f,z)for z in corners),'selected facet not fully retired')
            fallback_edges+=len(arc)
            cells.append({'original_row':label,'polygon_sides':size,'macro_edges':len(arc),
                          'max_label_at_anchor':max(dc['basis']['active']),
                          'max_label_at_endpoint':max(active_rows(A,b,arc[-1]))})
    # In the three-dimensional retained face, selected facets have no neighbor
    # among its three target facets. The induced dual graph on at most e other
    # facets is simple planar: total available degree <= 6e-12 for e>=3.
    if r==3:
        incidence_bound=6*e-12
        acquisition_bound=2*((e+2)//2)
    elif r==2:
        incidence_bound=0;acquisition_bound=(e+2)//2
    else:
        incidence_bound=0;acquisition_bound=r
    charge=sum(c['polygon_sides']-1 for c in cells)
    require(fallback_edges<=charge<=incidence_bound-len(cells),
            'weighted selected-facet incidence bound failed')
    require(acquisition_edges<=acquisition_bound,'final polygon tail not shortest')
    total_bound=incidence_bound+acquisition_bound
    require(report['committed_edges']==fallback_edges+acquisition_edges<=total_bound,
            'linear tail route accounting failed')
    return {'status':'PASS','dimension':d,'original_input_rows':m,'missing_target_facets':r,
       'facet_excess':e,'committed_edges':report['committed_edges'],'loop_erased_edges':report['loop_erased_edges'],
       'fallback_macros':len(cells),'fallback_edges':fallback_edges,'selected_facets':cells,
       'weighted_fallback_charge':charge,'available_planar_incidence':incidence_bound,
       'acquisition_edges':acquisition_edges,'acquisition_tail_bound':acquisition_bound,
       'linear_tail_bound':total_bound,'previous_binomial_route_bound':report['original_facet_binomial_route_bound'],
       'scope':'Exact accounting for unchanged #253 in a retained face of dimension <=3. Written planar proof, not Lean or a bound for arbitrary dimension.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('certificate',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());A,b,u,v=route.parse(data['A'],data['b'],data['start'],data['target'])
        c=route.decode(json.loads(a.certificate.read_text()))
        a.output.write_text(json.dumps(account(A,b,u,v,c),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No checked linear tail account: {exc}\n')
if __name__=='__main__':main()
