#!/usr/bin/env python3
"""Symbolic identities supporting the separate written five-row mass example.

This does not run Lean and does not use symbolic signs as a geometric oracle.
The uniform sign argument is written in NEIGHBOR_TRANSPORT.md.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sympy as s


def run():
    e=s.Symbol('e',positive=True)
    nodes=[s.Integer(0),e,s.Integer(1),s.Integer(2),s.Integer(3)]
    D=e**2-5*e+14
    A=s.Matrix([[x-sum(nodes)/5,x*x-sum(y*y for y in nodes)/5] for x in nodes])
    u=s.Matrix([5*e/(2*(7-3*e)),-5/(2*(7-3*e))])
    v=s.Matrix([25/D,-5/D])
    z0=s.Matrix([5*(e+1)/(2*(4-e)),-5/(2*(4-e))])
    z1=s.Matrix([-15/((4-e)*(e+1)),5/((4-e)*(e+1))])
    t=[5*e/(2*(4-e)),5*e*(3-e)/((4-e)*(e+1))]
    b=[12*(4-e)/(e*D),(4-e)*(2-e)*(e+1)/(e*D)]
    L=(4-e)*(14+e-e**2)/(e*D)
    assert s.factor(sum(b)-L)==0
    assert s.factor(L-1/e-(3-e)*(14+3*e-e**2)/(e*D))==0
    assert all(s.factor(x)==0 for x in v-u-b[0]*(z0-u)-b[1]*(z1-u))
    slacks={name:[s.factor(x) for x in s.ones(5,1)-A*z]
            for name,z in [('u',u),('v',v),('z0',z0),('z1',z1)]}
    expected={
        'u':[0,0,5*(1-e)/(2*(7-3*e)),5*(2-e)/(7-3*e),15*(3-e)/(2*(7-3*e))],
        'v':[30/D,5*(3-e)*(2-e)/D,10/D,0,0],
        'z0':[t[0],0,0,5*(2-e)/(2*(4-e)),5*(3-e)/(4-e)],
        'z1':[0,t[1],10/((4-e)*(e+1)),10/((4-e)*(e+1)),0]}
    for name in slacks:
        assert all(s.factor(x-y)==0 for x,y in zip(slacks[name],expected[name]))
    for p,z in enumerate([z0,z1]):
        w=(z-u)/t[p]
        for i in [0,1]:assert s.factor((A*w)[i]+int(i==p))==0
        assert s.factor((1-(A*v)[p])/t[p]-b[p])==0
    f=lambda z:(A*z)[3]+(A*z)[4]
    gap=s.factor(f(v)-f(u))
    fractions=[s.factor((f(z)-f(u))/gap) for z in [z0,z1]]
    limits=[s.limit(x,e,0) for x in fractions]
    assert s.limit(e*L,e,0)==4 and limits==[-s.Rational(1,13),s.Rational(6,13)]
    controls=[]
    for q in [s.Rational(1,16),s.Rational(1,256),s.Rational(1,65536)]:
        for values in expected.values():assert all(s.sympify(x).subs(e,q)>=0 for x in values)
        controls.append({'epsilon':str(q),'mass':str(s.factor(L.subs(e,q)))})
    return {'status':'PASS','mass':str(s.factor(L)),
        'mass_minus_inverse_e':str((3-e)*(14+3*e-e**2)/(e*D)),
        'e_times_mass_limit':'4','neighbor_gain_fraction_limits':list(map(str,limits)),
        'slacks':{name:list(map(str,values)) for name,values in expected.items()},
        'controls':controls,
        'scope':'Symbolic identities plus written sign/extreme-point argument; NOT Lean or a new Prove2Me verdict.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    result=run();result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(result['mass'])
if __name__=='__main__':main()
