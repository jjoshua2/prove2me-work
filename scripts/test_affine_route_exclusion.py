#!/usr/bin/env python3
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from itertools import combinations
import argparse,json,hashlib
import original_route_exclusion as R
import affine_route_exclusion as U
from test_original_route_exclusion import kw


def run(folder):
    base=kw(18);data={'A':base['A'],'b':[[b,int(i==8)] for i,b in enumerate(base['b'])],
      'start':[[x,0] for x in base['start']],'target':[[x,0] for x in base['target']]}
    out={'status':'PASS','family':'Klee-Walkup capped at sum(x)<=18+t','domain':'all real t>0','certificates':{}}
    certificates={}
    for name,L,B in [('exclude_four',4,None),('nonrevisiting_five',None,0)]:
        c1=R.solve(U.family_data(data,1),L,B)['certificate'];c2=R.solve(U.family_data(data,2),L,B)['certificate']
        cert=U.prepare(data,c1,c2);certificates[name]=cert;out['certificates'][name]=U.verify(data,cert)
        (folder/(name+'.json')).write_text(json.dumps(cert,sort_keys=True,indent=2)+'\n')
    (folder/'family.json').write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
    # Exact strict witnesses for all nine original facets, valid for every t>0.
    c=certificates['exclude_four'];vertices=c['vertex_coefficients'];tpl=c['template']['vertices'];anchors=[]
    for i in range(9):
        selected=[x for x,p in zip(vertices,tpl) if i in p['active']];assert selected
        point=[U.times(Q(1,len(selected)),(sum(Q(x[j][0]) for x in selected),sum(Q(x[j][1]) for x in selected))) for j in range(4)]
        sl=[U.minus(U.aff(b),U.pairing(list(map(Q,a)),point)) for a,b in zip(data['A'],data['b'])]
        assert all(U.zero(z) if j==i else U.positive(z) for j,z in enumerate(sl));anchors.append(R.serial(point))
    strict=[(Q(1,100),Q(0))]*4
    assert all(U.positive(U.minus(U.aff(b),U.pairing(list(map(Q,a)),strict))) for a,b in zip(data['A'],data['b']))
    out['genuine_facets']=9;out['facet_anchor_affine_coefficients']=anchors
    out['strict_point']=['1/100']*4;out['boundedness']='x_i>=0 and sum(x)<=18+t imply 0<=x_i<=18+t'
    out['path_affine_coefficients']=certificates['nonrevisiting_five']['vertex_coefficients']
    # EVERY basis of the original UNBOUNDED input is either singular,
    # infeasible, or one of 15 finite vertices with sum<=18. No old finite vertex
    # is cut at C>18. The path result nevertheless changes.
    raw=kw();A=tuple(tuple(map(Q,r)) for r in raw['A']);b=tuple(map(Q,raw['b']));verts=set();sing=blocked=0
    for J in combinations(range(8),4):
        p=R.inverse_or_kernel([A[i] for i in J])
        if 'kernel' in p:sing+=1;continue
        x=tuple(sum(p['inverse'][j][k]*b[J[k]] for k in range(4)) for j in range(4))
        if any(R.dot(a,x)>t for a,t in zip(A,b)):blocked+=1;continue
        verts.add(x)
    assert len(verts)==15 and max(map(sum,verts))==18
    out['original_finite_vertex_check']={'complete_bases':70,'singular':sing,'infeasible':blocked,'vertices':15,'maximum_sum':18}
    controls=[]
    def bad(name,cert,edit):
        c=deepcopy(cert);edit(c)
        try:U.verify(data,c)
        except (ValueError,TypeError,KeyError,IndexError):controls.append(name);return
        raise AssertionError(name)
    neg=certificates['exclude_four'];pos=certificates['nonrevisiting_five']
    bad('changed domain',neg,lambda c:c.update(parameter='t>=0'))
    bad('missing affine vertex',neg,lambda c:c['vertex_coefficients'].pop())
    bad('changed family binding',neg,lambda c:c.update(family_sha256='bad'))
    # Perturb an affine coordinate by K*(t-1): invisible at the checked template,
    # so only the universal checks (not a pointwise recheck) detect it.
    bad('same template wrong vertex slope',neg,lambda c:c['vertex_coefficients'][1][0].__setitem__(slice(None),['-1000','1000']))
    def step(c):
        key=next(iter(c['step_coefficients']));z=list(map(Q,c['step_coefficients'][key]));c['step_coefficients'][key]=[str(z[0]+1000),str(z[1]-1000)]
    bad('same template wrong step slope',neg,step)
    bad('wrong affine endpoint',pos,lambda c:c['vertex_coefficients'][-1][0].__setitem__(slice(None),['0','1']))
    # Disable production for saved uniform certificate readback.
    old={n:getattr(R,n) for n in ('solve','inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses')};prep=U.prepare
    def kill(*a,**k):raise AssertionError('producer called')
    try:
        for n in old:setattr(R,n,kill)
        U.prepare=kill
        for name in certificates:
            saved=json.loads((folder/(name+'.json')).read_text());assert U.verify(data,saved)==out['certificates'][name]
    finally:
        for n,z in old.items():setattr(R,n,z)
        U.prepare=prep
    out['negative_controls']=controls;out['producer_disabled_saved_readback']=True
    return out


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args();a.fixtures.mkdir(parents=True,exist_ok=True)
    r=run(a.fixtures);r['source_sha256']={s:hashlib.sha256((Path(__file__).parent/s).read_bytes()).hexdigest() for s in ['affine_route_exclusion.py','test_affine_route_exclusion.py']}
    a.out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['path_affine_coefficients','facet_anchor_affine_coefficients']},indent=2))
if __name__=='__main__':main()
