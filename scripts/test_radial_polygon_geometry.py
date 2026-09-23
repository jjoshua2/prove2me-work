#!/usr/bin/env python3
"""Exact tests for the actual-vertex radial chart and original exposed edges.

The checker uses complete original-H vertices and supporting-line intervals.
It is supporting executable evidence, not a Lean-extracted implementation.
"""
from __future__ import annotations
import argparse, hashlib, json, random
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import test_inverse_rank_reduction as ref


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def encode(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {str(k): encode(v) for k,v in x.items()}
    if isinstance(x, (list,tuple)): return [encode(v) for v in x]
    return x


def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))

def affine(points, k):
    """Invertible integer shears and translations; not pre-normalized coordinates."""
    a,b=Q(k+1),Q(k-2)
    return [(x+a*y+Q(3,7), b*x+(1+a*b)*y-Q(5,11)) for x,y in points]


def chart_and_edges(P, rows, target, variant):
    v=P[target]
    active=[r for r in rows if dot(r[:2],v)==r[2]]
    h=tuple(-sum(Q(j+1+variant)*r[k] for j,r in enumerate(active)) for k in range(2))
    # Change the independent coordinate without changing its independence.
    e=(-h[1]+variant*h[0],h[0]+variant*h[1])
    require(h[0]*e[1]-h[1]*e[0]!=0,'dependent chart')
    H={i:dot(h,sub(z,v)) for i,z in enumerate(P) if i!=target}
    require(all(x>0 for x in H.values()),'not a strict target exposure')
    order=sorted(H,key=lambda i:dot(e,sub(P[i],v))/H[i])
    w=[dot(e,sub(P[i],v))/H[i] for i in order]
    a=[1/H[i] for i in order]
    require(all(x<y for x,y in zip(w,w[1:])),'noninjective radial coordinate')
    triple_records=[]
    for i,j,k in combinations(range(len(order)),3):
        lhs=(a[j]-a[i])*(w[k]-w[j]);rhs=(a[k]-a[j])*(w[j]-w[i])
        r=(w[k]-w[j])/(w[k]-w[i]);s=(w[j]-w[i])/(w[k]-w[i])
        alpha=H[order[j]]*r*a[i];beta=H[order[j]]*s*a[k]
        require(r>0 and s>0 and r+s==1,'bad normalized weights')
        require(tuple(alpha*x+beta*y for x,y in zip(sub(P[order[i]],v),sub(P[order[k]],v)))==sub(P[order[j]],v),'wrong original radial interpolation')
        require(alpha+beta>1 and lhs<rhs,'actual vertex is not strictly below chord')
        triple_records.append([i,j,k,alpha+beta-1,rhs-lhs])
    edge_records=[]
    for j in range(len(order)-1):
        s=(a[j+1]-a[j])/(w[j+1]-w[j]);t=a[j]-s*w[j]
        f=tuple(s*x+t*y for x,y in zip(e,h));M=dot(f,v)+1
        slacks=[M-dot(f,z) for z in P]
        ends={order[j],order[j+1]}
        require(all(x>=0 for x in slacks) and {i for i,x in enumerate(slacks) if x==0}==ends,'secant fails full original support')
        supports=ref.interval_edge(rows,P[order[j]],P[order[j+1]])
        require(bool(supports),'no original supporting row')
        edge_records.append(dict(ends=sorted(ends),normal=f,max=M,original_support_rows=supports,slacks=slacks))
    for j,sign in [(0,Q(-1)),(len(order)-1,Q(1))]:
        f=tuple(sign*x-sign*w[j]*y for x,y in zip(e,h));M=dot(f,v)
        slacks=[M-dot(f,z) for z in P]
        require(all(x>=0 for x in slacks) and {i for i,x in enumerate(slacks) if x==0}=={target,order[j]},'ray fails full original support')
        supports=ref.interval_edge(rows,v,P[order[j]])
        edge_records.append(dict(ends=sorted([target,order[j]]),normal=f,max=M,original_support_rows=supports,slacks=slacks))
    routes=[]
    for j,u in enumerate(order):
        left=list(reversed(order[:j+1]))+[target]
        right=order[j:]+[target]
        path=left if len(left)<=len(right) else right
        L=min(j,len(order)-1-j)+1
        require(len(path)-1==L and 2*L<=len(P),'wrong walk count')
        require(len(path)==len(set(path)),'repeated vertex')
        for x,y in zip(path,path[1:]):ref.interval_edge(rows,P[x],P[y])
        distance=min((u-target)%len(P),(target-u)%len(P))
        require(L==distance,'reference polygon distance mismatch')
        routes.append(dict(source=u,target=target,path=path,length=L))
    return dict(target=target,variant=variant,h=h,e=e,order=order,w=w,a=a,
                triple_records=triple_records,edges=edge_records,routes=routes)


def audit(P, rows, rec):
    """Consumer does not call the chart constructor or use its rank formula."""
    target=rec['target'];v=P[target];h=tuple(map(Q,rec['h']));e=tuple(map(Q,rec['e']))
    require(h[0]*e[1]-h[1]*e[0]!=0,'dependent chart')
    order=rec['order'];require(set(order)==set(range(len(P)))-{target} and len(order)==len(P)-1,'incomplete vertex chart')
    HH=[dot(h,sub(P[i],v)) for i in order];require(all(z>0 for z in HH),'nonpositive exposure')
    ww=[dot(e,sub(P[i],v))/H for i,H in zip(order,HH)];aa=[1/H for H in HH]
    require(list(map(Q,rec['w']))==ww and list(map(Q,rec['a']))==aa,'changed chart coordinates')
    require(all(x<y for x,y in zip(ww,ww[1:])),'chart is not ordered')
    require(len(rec['triple_records'])==len(list(combinations(order,3))),'missing triple')
    for (i,j,k), tr in zip(combinations(range(len(order)),3),rec['triple_records']):
        require(tr[:3]==[i,j,k],'wrong triple binding')
        lam=(ww[k]-ww[j])/(ww[k]-ww[i]);mu=1-lam
        mass=HH[j]*(lam*aa[i]+mu*aa[k])
        defect=(aa[k]-aa[j])*(ww[j]-ww[i])-(aa[j]-aa[i])*(ww[k]-ww[j])
        require(mass>1 and defect>0 and Q(tr[3])==mass-1 and Q(tr[4])==defect,'false convexity witness')
    expected={tuple(sorted([order[i],order[i+1]])) for i in range(len(order)-1)}|{tuple(sorted([target,order[0]])),tuple(sorted([target,order[-1]]))}
    require({tuple(r['ends']) for r in rec['edges']}==expected and len(rec['edges'])==len(expected),'incomplete edge cycle')
    for edge in rec['edges']:
        x,y=edge['ends'];f=tuple(map(Q,edge['normal']));M=Q(edge['max'])
        slacks=[M-dot(f,z) for z in P]
        require(slacks==list(map(Q,edge['slacks'])) and all(z>=0 for z in slacks),'false original support')
        require({i for i,z in enumerate(slacks) if z==0}=={x,y},'support does not expose exactly the segment endpoints')
        require(ref.interval_edge(rows,P[x],P[y])==edge['original_support_rows'],'support-row mismatch')
    require({r['source'] for r in rec['routes']}==set(order),'missing source walk')
    for route in rec['routes']:
        path=route['path'];require(path[0]==route['source'] and path[-1]==target,'wrong endpoints')
        require(route['length']==len(path)-1 and 2*route['length']<=len(P),'false path length')
        require(len(path)==len(set(path)),'repeated point')
        for x,y in zip(path,path[1:]):
            require(tuple(sorted([x,y])) in expected,'jump is not a derived original edge')
            ref.interval_edge(rows,P[x],P[y])


def controls(P,rows,rec):
    import copy
    out=[]
    edits=[('missing vertex',lambda c:c['order'].pop()),
           ('changed height',lambda c:c['a'].__setitem__(0,'999')),
           ('dependent coordinates',lambda c:c.update(e=c['h'])),
           ('reverse chart',lambda c:c['order'].reverse()),
           ('missing edge',lambda c:c['edges'].pop()),
           ('false support maximum',lambda c:c['edges'][0].update(max='-999')),
           ('false convexity margin',lambda c:c['triple_records'][0].__setitem__(4,'0')),
           ('wrong target endpoint',lambda c:c['routes'][0]['path'].__setitem__(-1,c['order'][0])),
           ('false length',lambda c:c['routes'][0].update(length=0))]
    for label,edit in edits:
        changed=copy.deepcopy(rec);edit(changed)
        try:audit(P,rows,changed)
        except (ValueError,IndexError,ZeroDivisionError):out.append(dict(case=label,rejected=True))
        else:raise AssertionError('accepted '+label)
    # A radial midpoint is feasible but not extreme, so the geometric premise checker rejects it.
    bad=P+[tuple((x+y)/2 for x,y in zip(P[0],P[1]))]
    try:ref.original_polygon(bad)
    except (ValueError,AssertionError):out.append(dict(case='nonextreme boundary point',rejected=True))
    else:raise AssertionError('accepted nonextreme point')
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--large',action='store_true');args=ap.parse_args()
    models=[('square',[(0,0),(2,0),(2,2),(0,2)]),
            ('pentagon',[(-1,2),(0,0),(3,0),(4,2),(2,4)]),
            ('heptagon',[(-3,0),(-2,-2),(1,-3),(4,0),(3,3),(0,5),(-3,3)])]
    if args.large:
        n=32
        points=[(Q(1-t*t,1+t*t),Q(2*t,1+t*t)) for t in range(-(n//2),n//2-1)]+[(-1,0)]
        models=[('circle32',points)]
    else:
        models += [(f'affine_{i}',affine(models[i%3][1],i)) for i in range(8)]
    fixtures=[];report=[];negative=[]
    for name,points in models:
        P,rows,systems=ref.original_polygon(points)
        targets=list(range(len(P))) if not args.large else [0,8,16,24]
        records=[]
        for target in targets:
            for variant in ([0,2] if not args.large else [1]):
                rec=json.loads(json.dumps(encode(chart_and_edges(P,rows,target,variant))))
                audit(P,rows,rec);records.append(rec)
        if name=='heptagon':negative=controls(P,rows,records[0])
        row=dict(name=name,vertices=len(P),targets=len(targets),charts=len(records),original_systems=systems,
                 triples=sum(len(x['triple_records']) for x in records),
                 exposed_segments=sum(len(x['edges']) for x in records),routes=sum(len(x['routes']) for x in records),
                 original_edge_occurrences=sum(r['length'] for x in records for r in x['routes']))
        report.append(row);fixtures.append(dict(name=name,points=P,rows=rows,records=records));print(json.dumps(row),flush=True)
    args.out.mkdir(parents=True,exist_ok=True)
    summary=dict(kind='exact_rational_tests_not_Lean',models=report,controls=negative,
                 totals={k:sum(m[k] for m in report) for k in ['charts','triples','exposed_segments','routes','original_edge_occurrences']})
    (args.out/'report.json').write_text(json.dumps(encode(summary),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(encode(fixtures),indent=2)+'\n')
    print(json.dumps(summary['totals']))

if __name__=='__main__':main()
