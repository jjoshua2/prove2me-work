#!/usr/bin/env python3
"""Exact checks and written-formula certificates for an irredundant projective cube.

No large vertex graph is enumerated. Original support equations, line endpoints,
denominator positivity, facet witnesses, and projective inverse identities are
checked independently of the route producer. All-dimensional interpretation is
written mathematics, not an additional Lean instance theorem.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, permutations, product
import json
from pathlib import Path
import test_geometric_coordinate_routes as g
from test_normalized_slack_routes import exact_rank


def need(ok, message):
    if not ok: raise ValueError(message)


def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))


def point(bits):
    den=1+sum((2**j)*int(b) for j,b in enumerate(bits))
    return tuple(Q(int(b),den) for b in bits)


def rows_for(d):
    return [tuple([-Q(i==j) for j in range(d)]+[Q(0)]) for i in range(d)]+[
        tuple([Q(2**j+int(i==j)) for j in range(d)]+[Q(1)]) for i in range(d)]


def produce(d):
    rows=rows_for(d);order=list(range(d));bits=[True]*d;p=[point(bits)];edges=[]
    for j in order:
        before={i for i,b in enumerate(bits) if b};bits[j]=False;p.append(point(bits))
        common=[i if i not in before else d+i for i in range(d) if i!=j]
        H=set(range(j));remaining=set(range(d))-H
        edges.append(dict(acquired=j,released=d+j,common=common,
                          prefix=sorted(H),raw_charge=2**(len(remaining)-1),normalized_charge=1))
    facets=[]
    for side in (0,1):
        for i in range(d):
            y=[Q(1,2)]*d;y[i]=Q(side);den=1+sum(Q(2**j)*z for j,z in enumerate(y))
            facets.append(dict(row=side*d+i,point=[z/den for z in y]))
    return dict(d=d,rows=rows,path=p,edges=edges,order=order,facets=facets,
                raw_minimum=2**d-1,normalized_budget=d,
                all_order_charge_multiset=[2**k for k in range(d)],
                denominator=dict(a=1,D=[-2**j for j in range(d)]))


def consume(c, enumerate_small=True):
    d=c['d'];need(isinstance(d,int) and d>=1,'invalid dimension')
    rows=[tuple(map(Q,r)) for r in c['rows']];p=[tuple(map(Q,x)) for x in c['path']]
    need(rows==rows_for(d),'changed/incomplete original H rows')
    w=[Q(2**j) for j in range(d)];a=Q(c['denominator']['a']);D=list(map(Q,c['denominator']['D']))
    need(a==1 and D==[-z for z in w],'not the claimed positive normalization')
    need(c['order']==list(range(d)) and len(p)==d+1 and len(c['edges'])==d,'invalid order or size')
    need(p[0]==point([True]*d) and p[-1]==(Q(0),)*d,'wrong endpoints')
    need(c['raw_minimum']==2**d-1 and c['normalized_budget']==d,'incorrect route budgets')
    need(c['all_order_charge_multiset']==[2**k for k in range(d)],'wrong all-order formula')
    def active(x): return {i for i,r in enumerate(rows) if dot(r[:-1],x)==r[-1]}
    for x in p:
        need(len(x)==d and all(dot(r[:-1],x)<=r[-1] for r in rows),'infeasible vertex')
        den=a+dot(D,x);need(den>0,'nonpositive denominator')
        y=tuple(z/den for z in x)
        need(all(z in (0,1) for z in y),'not a projective cube vertex')
        need(tuple(z/(1+dot(w,y)) for z in y)==x,'projective inverse identity')
        S={i for i,z in enumerate(y) if z}
        need(active(x)==(set(range(d))-S)|{d+i for i in S},'incorrect tight rows')
        # The tight homogeneous rows force z_i=0 off S and z_i=-w.z on S.
        # Then (1+sum_{i in S} w_i)*(w.z)=0; the coefficient is positive.
        need(1+sum(w[i] for i in S)>0,'vertex uniqueness coefficient')
        need(all((r[-1]-dot(r[:-1],x))/den in (0,1) for r in rows),'nonbinary normalized spectrum')
    need(len(c['facets'])==2*d,'missing original-facet witness')
    for i,rec in enumerate(c['facets']):
        x=tuple(map(Q,rec['point']));need(rec['row']==i and active(x)=={i},'not exact singleton support')
        need(all(dot(r[:-1],x)<=r[-1] for r in rows),'infeasible facet witness')
        den=1-dot(w,x);need(den>0,'facet denominator')
        y=tuple(z/den for z in x)
        need(y[i%d]==int(i>=d) and all(y[j]==Q(1,2) for j in range(d) if j!=i%d),'wrong relative interior witness')
    raw=0
    for k,(x,y,e) in enumerate(zip(p,p[1:],c['edges'])):
        j=e['acquired'];need(j==k and e['released']==d+j,'wrong boundary transition')
        common=e['common'];need(set(common)==active(x)&active(y) and len(common)==d-1,'wrong support rows')
        F=set(range(k+1,d));B=set(range(k))
        need(set(common)==B|{d+i for i in F},'missing or nonindependent row certificate')
        # Free-coordinate formula for nullspace of the common rows.
        # z_i=0 on B, z_i=-w_j*z_j/(1+w_F) on F. This gives exactly one free parameter.
        den=1+sum(w[i] for i in F);need(den>0,'common-row kernel formula')
        z=tuple(0 if i in B else (1 if i==j else -w[j]/den) for i in range(d))
        need(all(dot(rows[i][:-1],z)==0 for i in common),'false line direction')
        delta=tuple(b-a for a,b in zip(x,y));need(delta[j]<0,'stationary or reversed phase')
        need(all(delta[i]==delta[j]*z[i] for i in range(d)),'segment not on entire support line')
        need(dot(rows[d+j][:-1],delta)<0 and dot(rows[j][:-1],delta)>0,'line not bounded at the two endpoints')
        support=tuple(sum((rows[i][l] for i in common),Q(0)) for l in range(d))
        maximum=sum((rows[i][-1] for i in common),Q(0))
        need(dot(support,x)==maximum==dot(support,y),'whole supporting face mismatch')
        need((active(x)&set(range(d)))<=(active(y)&set(range(d))),'target lock lost')
        need(e['prefix']==list(range(k)) and e['raw_charge']==2**(d-k-1) and e['normalized_charge']==1,'false prefix charge')
        raw+=e['raw_charge']
    need(raw==c['raw_minimum'],'incorrect all-order total')
    enumerated=orders=basis_candidates=0
    if enumerate_small and d<=4:
        V=[point(bits) for bits in product((False,True),repeat=d)];enumerated=len(V)
        need(len(set(V))==2**d,'corner collision')
        # Independently solve every d-subset of the original 2d equations.
        import sympy as sp
        found=set()
        for I in combinations(range(2*d),d):
            M=sp.Matrix([rows[i][:-1] for i in I]);rhs=sp.Matrix([rows[i][-1] for i in I]);basis_candidates+=1
            if M.det()==0:continue
            x=tuple(Q(t) for t in M.inv()*rhs)
            if all(dot(r[:-1],x)<=r[-1] for r in rows):found.add(x)
        need(found==set(V),'incomplete actual vertex classification')
        for J in permutations(range(d)):
            H=set();total=0
            for j in J:
                face=[x for x in V if all(x[i]==0 for i in H)]
                vals={-x[j] for x in face};normalized={x[j]/(1-dot(w,x)) for x in face}
                need(len(vals)-1==2**(d-len(H)-1) and normalized=={0,1},'conditional spectra disagree')
                total+=len(vals)-1;H.add(j)
            need(total==2**d-1,'order evades raw exponential charge');orders+=1
        for x in V:
            need(exact_rank([rows[i][:-1] for i in active(x)],d)==d,'independent rank check')
    return dict(dimension=d,original_rows=2*d,original_edges=d,raw_optimal_local_charge=c['raw_minimum'],
                normalized_charge=d,enumerated_vertices=enumerated,enumerated_orders=orders,
                original_bases_checked=basis_candidates,facet_witnesses=2*d,
                large_count_basis='written binary-subset formula',full_large_graph_enumerated=False)


def encoded(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encoded(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encoded(v) for v in x]
    return x


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True);certs=[];reports=[]
    for d in (1,2,3,4,8,16,32,64):
        c=produce(d);r=consume(c);certs.append(encoded(c));reports.append(r);print(json.dumps(r),flush=True)
    frozen=json.loads(json.dumps(certs));original=globals()['produce']
    def disabled(*args,**kwargs):raise RuntimeError('producer disabled')
    globals()['produce']=disabled
    try:
        for c in frozen:consume(c,enumerate_small=False)
    finally:globals()['produce']=original
    controls=[]
    for name,edit in [
        ('changed original row',lambda c:c['rows'][0].__setitem__(0,'-2')),
        ('wrong normalizer',lambda c:c['denominator'].update(a=0)),
        ('missing common row',lambda c:c['edges'][0]['common'].pop()),
        ('false raw optimum',lambda c:c.update(raw_minimum=4)),
        ('false local spectrum',lambda c:c['edges'][0].update(raw_charge=1)),
        ('missing facet witness',lambda c:c['facets'].pop()),
    ]:
        c=deepcopy(frozen[3]);edit(c)
        try:consume(c,enumerate_small=False)
        except (ValueError,AssertionError):controls.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    (args.out/'report.json').write_text(json.dumps(dict(kind='written_family_exact_tests_not_Lean_instances',cases=reports,controls=controls),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(certs,indent=2)+'\n')

if __name__=='__main__':main()
