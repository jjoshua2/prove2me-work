#!/usr/bin/env python3
"""Explicit large original-H routes and sparse inverse certificates.

No large vertex/edge inventory is enumerated. This does not claim that Python
or these concrete certificates are kernel-verified.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,json
import test_affine_roof_routes as t


def setup(n,k):
    N=n+k;A=[tuple(F(j+1,2**(i+1)) for i in range(n)) for j in range(k)]
    c=[F(1)]*k;rows=[]
    for i in range(n):
        e=tuple(F(int(q==i)) for q in range(N));rows += [(*e,F(1)),(*(-x for x in e),F(0))]
    for j in range(k):
        e=tuple(F(int(q==j)) for q in range(k))
        rows += [(*(-x for x in A[j]),*e,c[j]),(*(F(0) for _ in range(n)),*(-x for x in e),F(0))]
    return dict(n=n,k=k,A=A,c=c,rows=rows)


def cert(M,basebits,roofbits):
    n,k=M['n'],M['k'];N=n+k
    z=t.corner(M,tuple(map(F,basebits)),roofbits)
    labels=[2*i+(0 if bit else 1) for i,bit in enumerate(basebits)]
    labels += [2*n+2*j+(0 if bit else 1) for j,bit in enumerate(roofbits)]
    columns=[]
    for i in range(n):
        s=F(1 if basebits[i] else -1);col={i:s}
        col.update({n+j:s*M['A'][j][i] for j in range(k) if roofbits[j]})
        columns.append(col)
    for j in range(k):columns.append({n+j:F(1 if roofbits[j] else -1)})
    return dict(z=z,labels=labels,columns=columns)


def verify_vertex(M,C):
    N=M['n']+M['k'];rows=M['rows'];z=C['z'];labels=C['labels'];cols=C['columns']
    if len(set(labels))!=N or len(cols)!=N:raise ValueError('not a square original-row certificate')
    if any(t.dot(r[:-1],z)>r[-1] for r in rows):raise ValueError('original infeasibility')
    for i,a in enumerate(labels):
        r=rows[a]
        if t.dot(r[:-1],z)!=r[-1]:raise ValueError('inactive claimed label')
        for j,col in enumerate(cols):
            if sum((r[q]*v for q,v in col.items()),F(0))!=int(i==j):raise ValueError('invalid exact inverse')
    return True


def verify_edge(M,U,V,q):
    verify_vertex(M,U);verify_vertex(M,V)
    rows=M['rows'];u=U['z'];v=V['z'];N=len(u)
    if u==v or not 0<=q<N:raise ValueError('degenerate/wrong free coordinate')
    # Omit exactly the changed coordinate's active original row. The retained
    # sparse inverse columns prove rank N-1 without an elimination routine.
    for i,lab in enumerate(U['labels']):
        if i==q:continue
        if t.dot(rows[lab][:-1],v)!=rows[lab][-1]:raise ValueError('not a common original row')
        for j,col in enumerate(U['columns']):
            if j==q:continue
            if sum((rows[lab][p]*a for p,a in col.items()),F(0))!=int(i==j):raise ValueError('common inverse failed')
    direction=t.sub(v,u);lower=[];upper=[]
    for row in rows:
        slope=t.dot(row[:-1],direction);slack=row[-1]-t.dot(row[:-1],u)
        if slope>0:upper.append(slack/slope)
        elif slope<0:lower.append(slack/slope)
        elif slack<0:raise ValueError('infeasible support line')
    if max(lower)!=0 or min(upper)!=1:raise ValueError('not the whole exposed line slice')
    return True


def main(out):
    reports=[];fixtures=[]
    for n,k in [(4,4),(8,8),(16,16),(32,32)]:
        M=setup(n,k);basebits=[0]*n;roofbits=[0]*k;records=[cert(M,basebits,roofbits)];changed=[]
        for j in range(k):
            roofbits[j]=1;records.append(cert(M,basebits,roofbits));changed.append(n+j)
        for i in range(n):
            basebits[i]=1;records.append(cert(M,basebits,roofbits));changed.append(i)
        for a,b,q in zip(records,records[1:],changed):verify_edge(M,a,b,q)
        producer=globals()['cert'];globals()['cert']=lambda *a: (_ for _ in ()).throw(RuntimeError('producer disabled'))
        for a,b,q in zip(records,records[1:],changed):verify_edge(M,a,b,q)
        globals()['cert']=producer
        report=dict(base_dimension=n,roof_count=k,ambient_dimension=n+k,original_rows=len(M['rows']),
                    route_edges=len(changed),exceptional_rows_at_target=k,
                    levels_per_exception_by_written_formula=2**n+1,
                    full_vertex_count_by_written_formula=2**(n+k),
                    enumerated_large_graph=False,exact_inverse_checks=True,producer_disabled_replay=True)
        reports.append(report);fixtures.append(dict(model=M,vertices=records,changed_coordinates=changed))
        print(json.dumps(report),flush=True)
    # This is a genuinely changed certificate, not a no-op negative control.
    M=setup(2,2);a=cert(M,[0,0],[0,0]);a['columns'][0][0]+=1
    try:verify_vertex(M,a)
    except ValueError:rejected=True
    else:raise AssertionError('forged inverse accepted')
    out.mkdir(parents=True,exist_ok=True)
    (out/'large-report.json').write_text(json.dumps(dict(kind='exact_sparse_original_H_checks_not_Lean',models=reports,forged_inverse_rejected=rejected),indent=2)+'\n')
    (out/'large-fixtures.json').write_text(json.dumps(t.asjson(fixtures),indent=2)+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args();main(args.out)
