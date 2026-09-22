#!/usr/bin/env python3
"""Stress tests of the generic face-local charge on the known triangular family.

This is not a new Lean classification or route theorem for that family (#282's
separate work). Global counts and large-face classification use the written
recurrence argument, not enumeration of the 2**d vertices. Every delivered edge
has original supporting rows, exact rank and line-endpoint certificates.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
from test_face_local_flags import exact_rank, need


def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))


def point(bits,e):
    x=[Q(0)]*len(bits);tail=Q(0)
    for j in reversed(range(len(bits))):
        x[j]=1-e*tail if bits[j] else e*tail;tail=x[j]
    return tuple(x)


def original_rows(d,e):
    rows=[]
    for side in (0,1):
        for j in range(d):
            a=[Q(0)]*d;a[j]=Q(-1 if side==0 else 1)
            if j+1<d:a[j+1]=e
            rows.append(tuple(a+[Q(side)]))
    return rows


def produce(d,e=Q(1,4)):
    rows=original_rows(d,e);bits=[True]*d;p=[point(bits,e)];edges=[];phases=[]
    for j in reversed(range(d)):
        H=list(range(j+1,d));bits[j]=False;y=point(bits,e);x=p[-1];D=tuple(b-a for a,b in zip(x,y))
        common=list(range(j+1,d))+[d+i for i in range(j)]
        edges.append(dict(common=common,direction=D,released=d+j,acquired=j,
            support=[sum((rows[i][k] for i in common),Q(0)) for k in range(d)],
            maximum=sum((rows[i][-1] for i in common),Q(0))))
        phases.append(dict(row=j,entry_rows=H,local_values=[Q(-1),Q(0)],charge=1))
        p.append(y)
    return dict(d=d,e=e,rows=rows,order=list(reversed(range(d))),path=p,edges=edges,phases=phases,
                static_row_weights=[2**(d-j-1) for j in range(d)],static_minimum=2**d-1,
                local_minimum=d)


def decode(c):
    c=deepcopy(c);c['e']=Q(c['e']);c['rows']=[tuple(map(Q,r)) for r in c['rows']]
    c['path']=[tuple(map(Q,x)) for x in c['path']]
    for p in c['phases']:p['local_values']=list(map(Q,p['local_values']))
    for e in c['edges']:
        e['direction']=tuple(map(Q,e['direction']));e['support']=list(map(Q,e['support']));e['maximum']=Q(e['maximum'])
    return c


def consume(c):
    c=decode(c);d=c['d'];e=c['e'];rows=c['rows'];p=c['path']
    need(d>=1 and 0<e<Q(1,2),'outside original family')
    need(rows==original_rows(d,e),'not the original 2d rows')
    need(c['order']==list(reversed(range(d))) and len(p)==d+1 and len(c['edges'])==d,'order or path size')
    need(p[0]==point([True]*d,e) and p[-1]==(Q(0),)*d,'wrong endpoints')
    need(c['static_row_weights']==[2**(d-j-1) for j in range(d)],'false global count formula')
    need(c['static_minimum']==2**d-1 and c['local_minimum']==d,'wrong budget')
    # At the zero target the exactly d lower rows form an invertible triangular
    # matrix. All are missing at the upper source; every determining flag uses all.
    need(exact_rank([rows[j][:-1] for j in range(d)],d)==d,'target kernel')
    def active(x):return {i for i,r in enumerate(rows) if dot(r[:-1],x)==r[-1]}
    need(active(p[0])==set(range(d,2*d)) and active(p[-1])==set(range(d)),'wrong target labels')
    for x in p:
        need(all(dot(r[:-1],x)<=r[-1] for r in rows),'infeasible route vertex')
        need(exact_rank([rows[i][:-1] for i in active(x)],d)==d,'nonvertex endpoint')
    for k,(x,y,edge,phase) in enumerate(zip(p,p[1:],c['edges'],c['phases'])):
        j=d-1-k;H=set(range(j+1,d));D=tuple(b-a for a,b in zip(x,y));common=edge['common']
        need(phase==dict(row=j,entry_rows=sorted(H),local_values=[Q(-1),Q(0)],charge=1),'false conditional charge')
        need(H<=active(x) and H<=active(y) and all(x[i]==y[i]==0 for i in H),'suffix not fixed')
        need(edge['direction']==D and any(D),'wrong or stationary edge')
        need(set(common)==active(x)&active(y) and len(common)==d-1,'wrong original common rows')
        need(exact_rank([rows[i][:-1] for i in common],d)==d-1,'support slice not a line')
        need(all(dot(rows[i][:-1],D)==0 for i in common),'direction leaves support line')
        need(edge['released']==d+j and edge['acquired']==j,'wrong endpoint rows')
        need(dot(rows[d+j][:-1],D)<0 and dot(rows[j][:-1],D)>0,'line does not stop at endpoints')
        need(edge['support']==[sum((rows[i][l] for i in common),Q(0)) for l in range(d)]
             and edge['maximum']==sum((rows[i][-1] for i in common),Q(0)),'wrong whole support objective')
        need((active(x)&set(range(d)))<=(active(y)&set(range(d))),'target row lost')
    # Small all-vertex checks validate the formulas independently of the route.
    enumerated=0
    if d<=8:
        V=[point(bits,e) for bits in product((False,True),repeat=d)];enumerated=len(V)
        need(len(set(V))==2**d,'corner collision')
        for j in range(d):
            need(len({dot(rows[j][:-1],x) for x in V})-1==c['static_row_weights'][j],'global inventory mismatch')
            F=[x for x in V if all(x[i]==0 for i in range(j+1,d))]
            need(sorted({dot(rows[j][:-1],x) for x in F})==[Q(-1),Q(0)],'local inventory mismatch')
    return dict(dimension=d,original_rows=2*d,original_edges=d,global_minimum=c['static_minimum'],
                local_minimum=d,local_K=1,enumerated_vertices=enumerated,full_graph_enumerated=False,
                large_level_count='written triangular recurrence, not enumeration')


def encoded(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encoded(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encoded(v) for v in x]
    return x


def main():
    a=argparse.ArgumentParser();a.add_argument('--out',type=Path,required=True);args=a.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    certs=[];results=[]
    for d in (4,8,16,32,64):
        c=produce(d);r=consume(c);certs.append(c);results.append(r);print(json.dumps(r),flush=True)
    frozen=json.loads(json.dumps(encoded(certs)))
    original=globals()['produce']
    def disabled(*a,**kw):raise RuntimeError('producer disabled')
    globals()['produce']=disabled
    try:
        for c in frozen:consume(c)
    finally:globals()['produce']=original
    controls=[]
    for name,edit in [
        ('wrong conditional count',lambda c:c['phases'][0].update(charge=0)),
        ('missing common row',lambda c:c['edges'][0]['common'].pop()),
        ('changed H row',lambda c:c['rows'][0].__setitem__(0,'-2')),
        ('wrong global formula',lambda c:c.update(static_minimum=1)),
    ]:
        c=deepcopy(frozen[0]);edit(c)
        try:consume(c)
        except (ValueError,AssertionError):controls.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    (args.out/'report.json').write_text(json.dumps(dict(kind='known_family_exact_checks_not_Lean_instance',cases=results,controls=controls),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(frozen,indent=2)+'\n')

if __name__=='__main__':main()
