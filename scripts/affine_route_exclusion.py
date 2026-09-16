#!/usr/bin/env python3
"""Uniform certificates for Ax <= b0+t*b1, for EVERY real t>0.

The finite star/closure template is checked at t=1; CONSTANT normal/rank and
exact affine identity/sign checks then transport all its geometry over the
entire parameter ray. This is not interpolation-based proof by two samples.
"""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import argparse,hashlib,json
import original_route_exclusion as R


def aff(x):
    R.require(isinstance(x,(list,tuple)) and len(x)==2,'affine coefficient pair required')
    return tuple(map(R.rat,x))


def plus(x,y):return x[0]+y[0],x[1]+y[1]
def minus(x,y):return x[0]-y[0],x[1]-y[1]
def times(c,x):return c*x[0],c*x[1]
def val(x,t):return x[0]+t*x[1]
def zero(x):return x==(0,0)
def positive(x):return x[0]>=0 and x[1]>=0 and not zero(x)
def nonnegative(x):return x[0]>=0 and x[1]>=0

def pairing(row,x):
    return sum((a*z[0] for a,z in zip(row,x)),Q(0)),sum((a*z[1] for a,z in zip(row,x)),Q(0))


def interpolate(one,two):
    a,b=R.rat(one),R.rat(two)
    return 2*a-b,b-a


def family_data(data,t):
    return {'A':data['A'],'b':[val(aff(z),t) for z in data['b']],
            'start':[val(aff(z),t) for z in data['start']],
            'target':[val(aff(z),t) for z in data['target']]}


def bind(data):return hashlib.sha256(json.dumps(R.serial(data),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def prepare(data,one,two):
    """Producer convenience only. verify() checks the coefficients, not samples."""
    R.require(one['format']==two['format'],'different certificate formats')
    a,b=deepcopy(one),deepcopy(two)
    points=[]
    for u,v in zip(a['vertices'],b['vertices']):
        points.append([interpolate(x,y) for x,y in zip(u.pop('point'),v.pop('point'))])
    a.pop('input_sha256');b.pop('input_sha256');steps={};target=None
    if a['format']=='original-route-exclusion-v1':
        target=[interpolate(x,y) for x,y in zip(a['target'].pop('point'),b['target'].pop('point'))]
        for s,t in zip(a['stars'],b['stars']):
            for j,(r,z) in enumerate(zip(s['rays'],t['rays'])):
                if r['kind']=='edge':steps[str(s['vertex'])+':'+str(j)]=interpolate(r.pop('step'),z.pop('step'))
    R.require(a==b,'sample templates differ: cannot propose affine transport')
    c={'format':'uniform-affine-route-v1','parameter':'t>0','family_sha256':bind(data),
       'template':one,'vertex_coefficients':points,'step_coefficients':steps,'target_coefficients':target}
    c=R.serial(c);verify(data,c);return c


def verify(data,c):
    R.require(c['format']=='uniform-affine-route-v1' and c['parameter']=='t>0' and c['family_sha256']==bind(data),'changed affine family')
    A=tuple(tuple(map(R.rat,r)) for r in data['A']);rhs=list(map(aff,data['b']));u=list(map(aff,data['start']));v=list(map(aff,data['target']))
    R.require(A and A[0] and len(A)==len(rhs) and all(len(r)==len(u)==len(v)==len(A[0]) for r in A),'family dimensions')
    temp=c['template'];at_one=family_data(data,1)
    f=R.verify_exclusion if temp['format']=='original-route-exclusion-v1' else R.verify_path
    result=f(at_one,temp)
    points=[[aff(z) for z in x] for x in c['vertex_coefficients']]
    R.require(len(points)==len(temp['vertices']),'missing affine vertices')
    def check_point(p,x):
        R.require(len(x)==len(A[0]) and [val(z,1) for z in x]==list(map(R.rat,p['point'])),'wrong affine vertex at template')
        slacks=[minus(b,pairing(a,x)) for a,b in zip(A,rhs)]
        I=set(p['active'])
        R.require(all(zero(z) if i in I else positive(z) for i,z in enumerate(slacks)),'active set is not constant over t>0')
        return slacks
    checks=0
    for p,x in zip(temp['vertices'],points):check_point(p,x);checks+=len(A)
    R.require(points[0]==u,'wrong affine source')
    if temp['format']=='original-route-witness-v1':
        R.require(points[-1]==v and c['step_coefficients']=={} and c['target_coefficients'] is None,'wrong affine path endpoints/format')
        # Positive vertex and shared-row rank certificates are constant in t;
        # exact distinct active sets imply nonstationary endpoints for all t.
        R.require(all(p['active']!=q['active'] for p,q in zip(temp['vertices'],temp['vertices'][1:])),'potentially coincident path vertices')
    else:
        target=list(map(aff,c['target_coefficients']));check_point(temp['target'],target);checks+=len(A)
        R.require(target==v,'wrong affine target');expected=set()
        for s in temp['stars']:
            x=points[s['vertex']]
            for j,r in enumerate(s['rays']):
                if r['kind']=='unbounded_ray':continue
                key=str(s['vertex'])+':'+str(j);expected.add(key);alpha=aff(c['step_coefficients'][key]);direction=tuple(map(R.rat,r['direction']))
                R.require(positive(alpha) and val(alpha,1)==R.rat(r['step']),'finite step not positive on entire ray')
                R.require(points[r['target']]==[plus(z,times(t,alpha)) for z,t in zip(x,direction)],'affine neighbor identity failed')
                slack=[minus(b,pairing(a,x)) for a,b in zip(A,rhs)]
                remain=[minus(z,times(R.dot(a,direction),alpha)) for a,z in zip(A,slack)]
                R.require(all(nonnegative(z) for z in remain) and zero(remain[r['blocker']]),'universal maximal step failed')
                checks+=len(A)
        R.require(set(c['step_coefficients'])==expected,'extra/missing affine step')
    return {'status':'PASS','parameter_domain':'EVERY real t>0','template_verdict':result,
            'affine_sign_identity_checks':checks,'scope':'Universal affine identities/signs plus constant rank and coverage, not sampled extrapolation or Lean.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('family',type=Path);p.add_argument('certificate',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    a.output.write_text(json.dumps(verify(json.loads(a.family.read_text()),json.loads(a.certificate.read_text())),sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
