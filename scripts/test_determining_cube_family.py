#!/usr/bin/env python3
"""Sparse exact checks for cubes with an expensive redundant target row.

The all-dimensional H/hull, binary-level and minimal-completion arguments are
written applications, not separate Lean instance theorems. No 2**d vertex set
or full graph is enumerated. All displayed original rows and delivered edges
are checked exactly; singleton/free-coordinate support certificates are explicit.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
import json
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def rows_for(d):
    rows=[]
    for sign in (-1,1):
        for i in range(d):rows.append([sign*int(i==j) for j in range(d)]+[int(sign==1)])
    rows.append([2**j for j in range(d)]+[2**d-1])
    return rows


def produce(d):
    rows=rows_for(d);p=[[int(j<k) for j in range(d)] for k in range(d+1)]
    edge_cert=[]
    for k in range(d):
        fixed=[d+j if j<k else j for j in range(d) if j!=k]
        normal=[sum(rows[i][j] for i in fixed) for j in range(d)]
        edge_cert.append(dict(free_coordinate=k,fixed_rows=fixed,support=normal,
                              maximum=sum(rows[i][-1] for i in fixed)))
    return dict(d=d,m=2*d+1,rows=rows,path=p,edges=edge_cert,
                missing=list(range(d,2*d+1)),shared=[],selected=list(range(d,2*d)),
                selected_weight=d,selected_K=1,all_missing_weight=d+(2**d-1),
                redundant_row_levels=2**d,
                # Exactly d independent rows are necessary; there are d+1 possible d-row subsets.
                candidate_costs=[dict(omit=i,weight=(d if i==2*d else d-1+(2**d-1)))
                                 for i in range(d,2*d+1)])


def consume(c):
    d=c['d'];rows=c['rows'];p=c['path'];edges=c['edges']
    need(isinstance(d,int) and d>=1,'invalid dimension')
    need(rows==rows_for(d) and c['m']==len(rows),'incomplete original H system')
    need(c['shared']==[] and c['missing']==list(range(d,2*d+1)),'false missing/shared set')
    need(c['selected']==list(range(d,2*d)),'not the coordinate determining set')
    # Those selected rows form the identity matrix exactly.
    need(all(rows[d+i][j]==int(i==j) for i in range(d) for j in range(d)),'selected kernel not trivial')
    need(all(a>0 for a in rows[-1][:-1]) and sum(rows[-1][:-1])==rows[-1][-1], 'extra row not redundant on cube')
    need(c['redundant_row_levels']==2**d,'binary value-count formula')
    need(c['selected_weight']==d and c['selected_K']==1 and c['all_missing_weight']==d+2**d-1,'wrong weights')
    expected=[dict(omit=i,weight=(d if i==2*d else d-1+2**d-1)) for i in range(d,2*d+1)]
    need(c['candidate_costs']==expected and min(x['weight'] for x in expected)==d,'wrong minimum candidate weight')
    # In a competitor retaining the binary row, the single omitted coordinate
    # is determined by its nonzero coefficient after all other coordinates.
    for omitted in range(d):
        need(rows[-1][omitted]==2**omitted and rows[-1][omitted]!=0,'competitor rank certificate')
    need(len(p)==d+1 and len(edges)==d and p[0]==[0]*d and p[-1]==[1]*d,'route endpoints/length')
    for x in p:
        need(len(x)==d and all(v in (0,1) for v in x),'nonvertex coordinate')
        need(all(sum(a*z for a,z in zip(row[:-1],x))<=row[-1] for row in rows),'original infeasibility')
    target_rows=set(range(d,2*d+1))
    def active(x):return {i for i,row in enumerate(rows) if sum(a*z for a,z in zip(row[:-1],x))==row[-1]}
    for k,(x,y,e) in enumerate(zip(p,p[1:],edges)):
        free=e['free_coordinate'];fixed=e['fixed_rows']
        need(free==k and [j for j in range(d) if x[j]!=y[j]]==[free],'wrong changing coordinate')
        need(x[free]==0 and y[free]==1,'stationary/reversed coordinate')
        need(len(fixed)==d-1 and len(set(fixed))==d-1,'incomplete supporting basis')
        need(set(fixed)<=active(x)&active(y),'support rows not common')
        supports=[]
        for i in fixed:
            nz=[j for j in range(d) if rows[i][j]]
            need(len(nz)==1 and nz[0]!=free and abs(rows[i][nz[0]])==1,'non-coordinate support row')
            supports+=nz
        need(set(supports)==set(range(d))-{free},'support slice dimension not one')
        normal=[sum(rows[i][j] for i in fixed) for j in range(d)];maximum=sum(rows[i][-1] for i in fixed)
        need(e['support']==normal and e['maximum']==maximum,'false exposing functional')
        need(sum(a*z for a,z in zip(normal,x))==maximum==sum(a*z for a,z in zip(normal,y)), 'endpoints not exposed')
        need((active(x)&target_rows)<=(active(y)&target_rows),'acquired target row lost')
    return dict(dimension=d,original_rows=len(rows),actual_edges=d,selected_rows=d,
                selected_weight=d,old_all_missing_weight=c['all_missing_weight'],
                unselected_row_levels=c['redundant_row_levels'],selected_K=1,
                original_bound=min(d,len(rows)-d),full_graph_enumerated=False,
                level_count_source='binary expansion formula; not enumeration')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    a.out.mkdir(parents=True,exist_ok=True);certs=[];reports=[]
    for d in (8,16,32,64):
        c=produce(d);r=consume(c);certs.append(c);reports.append(r);print(json.dumps(r),flush=True)
    frozen=json.loads(json.dumps(certs))
    for c in frozen:consume(c)
    bad=[]
    for label,edit in [
        ('wrong binary cap',lambda c:c['rows'][-1].__setitem__(-1,c['rows'][-1][-1]-1)),
        ('missing support row',lambda c:c['edges'][0]['fixed_rows'].pop()),
        ('false selected cost',lambda c:c.update(selected_weight=0)),
        ('wrong level count',lambda c:c.update(redundant_row_levels=1)),
    ]:
        c=deepcopy(certs[0]);edit(c)
        try:consume(c)
        except ValueError:bad.append(dict(case=label,rejected=True))
        else:raise RuntimeError('accepted corruption '+label)
    (a.out/'report.json').write_text(json.dumps(dict(kind='written_family_exact_checks_not_Lean_instances',cases=reports,controls=bad),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(certs,indent=2)+'\n')

if __name__=='__main__':main()
