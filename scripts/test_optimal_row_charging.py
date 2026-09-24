#!/usr/bin/env python3
"""Exact capacitated original-row ledgers and independently checked overloads.
No Lean extraction, no trusted max-flow verdict, and no route-length claim.
"""
from __future__ import annotations
import argparse, copy, hashlib, itertools, json, random
from collections import deque
from fractions import Fraction as Q
from pathlib import Path


def require(ok, message):
    if not ok: raise ValueError(message)

def enc(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [enc(v) for v in x]
    return x

def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def rank(rows,d): return len(eliminate(rows,d)[1])
def eliminate(rows,d):
    a=[list(map(Q,r)) for r in rows];piv=[];k=0
    for j in range(d):
        z=next((t for t in range(k,len(a)) if a[t][j]),None)
        if z is None: continue
        a[k],a[z]=a[z],a[k];scale=a[k][j];a[k]=[x/scale for x in a[k]]
        for t in range(len(a)):
            if t!=k and a[t][j]:
                c=a[t][j];a[t]=[x-c*y for x,y in zip(a[t],a[k])]
        piv.append(j);k+=1
        if k==len(a):break
    return a,piv


def flow_assignment(S,m,k):
    """Integer augmenting-path producer. Edge-row arcs have capacity N+1.
    A failed flow returns reachable row labels, not a trusted solver verdict.
    """
    n=len(S);source=n+m;sink=source+1;size=sink+1
    residual=[{} for _ in range(size)]
    def arc(u,v,c):
        residual[u][v]=c;residual[v].setdefault(u,0)
    for t,rows in enumerate(S):
        arc(source,t,1)
        for i in sorted(rows):arc(t,n+i,n+1)
    for i in range(m):arc(n+i,sink,k)
    amount=0
    while True:
        pred={source:None};todo=deque([source])
        while todo and sink not in pred:
            u=todo.popleft()
            for v,c in sorted(residual[u].items()):
                if c>0 and v not in pred:pred[v]=u;todo.append(v)
        if sink not in pred:
            return None,sorted(i for i in range(m) if n+i in pred)
        v=sink
        while v!=source:
            u=pred[v];residual[u][v]-=1;residual[v][u]+=1;v=u
        amount+=1
        if amount==n:
            assignment=[next(i for i in sorted(rows) if residual[n+i][t]==1) for t,rows in enumerate(S)]
            return assignment,None


def optimize(S,m):
    require(all(S),'empty eligible row set')
    if not S:return dict(K=0,assignment=[],overloaded_rows=[],forced_occurrences=[])
    low=0;high=len(S)
    while low<high:
        mid=(low+high)//2;assignment,_=flow_assignment(S,m,mid)
        if assignment is None:low=mid+1
        else:high=mid
    assignment,_=flow_assignment(S,m,low)
    failed,J=flow_assignment(S,m,low-1)
    require(failed is None,'previous capacity unexpectedly feasible')
    F=[t for t,s in enumerate(S) if s<=set(J)]
    return dict(K=low,assignment=assignment,overloaded_rows=J,forced_occurrences=F)


def audit_ledger(S,m,c):
    """No flow, matching, search, or minimum computation is called here.
    Assignment proves upper bound; explicit forced set proves optimality.
    """
    K=c['K'];f=c['assignment'];J=c['overloaded_rows'];F=c['forced_occurrences']
    require(isinstance(K,int) and 0<=K<=len(S),'invalid capacity')
    require(len(f)==len(S) and all(isinstance(i,int) and i in S[t] for t,i in enumerate(f)),'ineligible label')
    loads=[f.count(i) for i in range(m)]
    require(all(x<=K for x in loads),'capacity exceeded')
    if not S:
        require(K==0 and not J and not F,'nonzero empty ledger');return loads
    require(K>0 and len(set(J))==len(J) and J and all(0<=i<m for i in J),'invalid bottleneck rows')
    expected=[t for t,s in enumerate(S) if s<=set(J)]
    require(F==expected and all(S),'false forced occurrence set')
    require((K-1)*len(J)<len(F)<=K*len(J),'invalid overload certificate')
    require(len(S)<=K*len(set().union(*S)),'global row capacity failed')
    return loads


def subset_formula(S,m):
    ans=0
    for mask in range(1,1<<m):
        J={i for i in range(m) if (mask>>i)&1};count=sum(s<=J for s in S)
        ans=max(ans,(count+len(J)-1)//len(J))
    return ans


def exhaustive():
    count=0;assignments=0
    for m in range(4):
        masks=[{i for i in range(m) if (bits>>i)&1} for bits in range(1,1<<m)]
        for n in range(5):
            for word in itertools.product(range(len(masks)),repeat=n):
                S=[masks[j] for j in word];cert=optimize(S,m);audit_ledger(S,m,cert)
                best=n
                for f in itertools.product(*(sorted(s) for s in S)):
                    assignments+=1;best=min(best,max([f.count(i) for i in range(m)]+[0]))
                require(cert['K']==best==subset_formula(S,m),'independent optimum mismatch')
                count+=1
    return dict(eligible_set_families=count,brute_assignments_checked=assignments)


def vertices(A,b,d):
    out=set();systems=0
    for I in itertools.combinations(range(len(A)),d):
        systems+=1;R,piv=eliminate([list(A[i])+[b[i]] for i in I],d)
        if len(piv)!=d:continue
        x=tuple(row[-1] for row in R)
        if all(dot(a,x)<=z for a,z in zip(A,b)):out.add(x)
    return sorted(out),systems


def edge_check(A,b,x,y,d):
    require(x!=y,'degenerate segment')
    require(all(dot(a,z)<=bb for a,bb in zip(A,b) for z in (x,y)),'infeasible endpoint')
    common=[i for i in range(len(A)) if dot(A[i],x)==b[i]==dot(A[i],y)]
    require(rank([A[i] for i in common],d)==d-1,'support slice not a line')
    delta=tuple(v-u for u,v in zip(x,y));lower=None;upper=None
    for a,bb in zip(A,b):
        speed=dot(a,delta);slack=bb-dot(a,x)
        if speed>0:upper=slack/speed if upper is None else min(upper,slack/speed)
        if speed<0:lower=slack/speed if lower is None else max(lower,slack/speed)
    require(lower==0 and upper==1,'not the whole original segment')
    return common


def eligibility(A,b,v,edges,d):
    require(all(dot(a,v)<=bb for a,bb in zip(A,b)),'infeasible target')
    require(rank([a for a,bb in zip(A,b) if dot(a,v)==bb],d)==d,'target not extreme')
    result=[]
    for x,y in edges:
        require(x!=v and y!=v,'edge contains target endpoint')
        for z in (x,y):require(rank([a for a,bb in zip(A,b) if dot(a,z)==bb],d)==d,'nonextreme endpoint')
        common=edge_check(A,b,x,y,d)
        S={i for i in common if dot(A[i],v)<b[i]}
        require(S,'missing original-row witness');result.append(S)
    return result


def model_certificate(name,A,b,v,edges,d):
    A=[tuple(map(Q,a)) for a in A];b=list(map(Q,b));v=tuple(map(Q,v))
    edges=[(tuple(map(Q,x)),tuple(map(Q,y))) for x,y in edges]
    S=eligibility(A,b,v,edges,d);c=optimize(S,len(A));loads=audit_ledger(S,len(A),c)
    greedy=[min(s) for s in S];greedy_max=max([greedy.count(i) for i in range(len(A))]+[0])
    raw=dict(name=name,dimension=d,A=A,b=b,target=v,edge_occurrences=edges)
    c['input_sha256']=hashlib.sha256(json.dumps(enc(raw),sort_keys=True).encode()).hexdigest()
    record=dict(input=enc(raw),certificate=c)
    verify_record(record)
    return record,dict(name=name,dimension=d,original_rows=len(A),edge_occurrences=len(edges),
                       greedy_max_load=greedy_max,optimal_max_load=c['K'],
                       overload_rows=len(c['overloaded_rows']),forced_edges=len(c['forced_occurrences']))


def verify_record(record):
    r=record['input'];c=record['certificate']
    require(hashlib.sha256(json.dumps(r,sort_keys=True).encode()).hexdigest()==c['input_sha256'],'input hash differs')
    A=[tuple(map(Q,a)) for a in r['A']];b=list(map(Q,r['b']));v=tuple(map(Q,r['target']))
    edges=[(tuple(map(Q,x)),tuple(map(Q,y))) for x,y in r['edge_occurrences']]
    return audit_ledger(eligibility(A,b,v,edges,r['dimension']),len(A),c)


def cube(d):
    A=[];b=[]
    for i in range(d):
        a=tuple(Q(int(i==j)) for j in range(d));A.extend([a,tuple(-z for z in a)]);b.extend([Q(1),Q(0)])
    return A+[(Q(0),)*d,(Q(0),)*d],b+[Q(0),Q(2)]


def geometries():
    models=[]
    for d in (2,3,4):
        A,b=cube(d);models.append((f'cube{d}',d,A,b))
    for d in (2,3):
        A=[tuple(Q(-int(i==j)) for j in range(d)) for i in range(d)]+[(Q(1),)*d]
        models.append((f'simplex{d}',d,A,[Q(0)]*d+[Q(1)]))
    models.append(('octahedron3',3,list(itertools.product((Q(-1),Q(1)),repeat=3)),[Q(1)]*8))
    models.append(('pyramid3',3,[(1,0,1),(-1,0,1),(0,1,1),(0,-1,1),(0,0,-1)],[1,1,1,1,0]))
    models.append(('unbounded2',2,[(-1,0),(0,-1),(-1,-1),(-2,-1)],[0,0,-1,Q(-3,2)]))
    records=[];reports=[];systems=0
    for name,d,A,b in models:
        A=[tuple(map(Q,a)) for a in A];b=list(map(Q,b))
        A += [tuple(2*z for z in A[0]),(Q(0),)*d];b += [2*b[0],Q(0)]
        V,n=vertices(A,b,d);systems+=n
        pairs=[]
        for x,y in itertools.combinations(V,2):
            common=[a for a,bb in zip(A,b) if dot(a,x)==bb==dot(a,y)]
            if rank(common,d)==d-1:edge_check(A,b,x,y,d);pairs.append((x,y))
        for t,v in enumerate(V):
            edges=[e for e in pairs if v not in e]
            rec,report=model_certificate(f'{name}_target{t}',A,b,v,edges,d);records.append(rec);reports.append(report)
    # Repeated occurrences cannot be deduplicated without changing the ledger.
    A,b=cube(3);v=(0,0,0);edge=((1,1,1),(0,1,1))
    rec,report=model_certificate('repeated_edge17',A,b,v,[edge]*17,3);records.append(rec);reports.append(report)
    rec,report=model_certificate('empty_zero_dimension',[],[],(),[],0);records.append(rec);reports.append(report)
    return records,reports,systems


def cube_walks(large):
    records=[];reports=[]
    for d in ((8,16,32,64) if large else (3,4,5,6,7,8)):
        A,b=cube(d);v=(0,)*d;x=[1]*d;path=[tuple(x)]
        for j in reversed(range(d)):x[j]=0;path.append(tuple(x))
        edges=list(zip(path,path[1:]))[:-1]
        rec,row=model_certificate(f'cube{d}_short_preterminal',A,b,v,edges,d);records.append(rec);reports.append(row)
        if not large:
            path=[tuple(((i^(i>>1))>>j)&1 for j in range(d)) for i in reversed(range(1<<d))]
            edges=list(zip(path,path[1:]))[:-1]
            rec,row=model_certificate(f'cube{d}_gray_preterminal',A,b,v,edges,d);records.append(rec);reports.append(row)
    return records,reports


def controls(record):
    changes=[('false capacity',lambda c:c.update(K=0)),('invalid assignment',lambda c:c['assignment'].__setitem__(0,-1)),
             ('missing occurrence',lambda c:c['assignment'].pop()),('empty dual rows',lambda c:c.update(overloaded_rows=[])),
             ('false forced subset',lambda c:c.update(forced_occurrences=[])),('wrong input binding',lambda c:c.update(input_sha256='0'*64)),
             ('inflated capacity',lambda c:c.update(K=c['K']+1)),('duplicate dual rows',lambda c:c['overloaded_rows'].append(c['overloaded_rows'][0]))]
    result=[]
    for name,change in changes:
        r=copy.deepcopy(record);change(r['certificate'])
        try:verify_record(r)
        except (ValueError,IndexError):result.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted '+name)
    try:optimize([set()],3)
    except ValueError:result.append(dict(case='empty_eligible_set',rejected=True))
    else:raise AssertionError('accepted empty eligible set')
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--large',action='store_true');args=ap.parse_args()
    generic=None;systems=0
    if args.large:records,rows=cube_walks(True)
    else:
        generic=exhaustive();records,rows,systems=geometries();rr,ss=cube_walks(False);records+=rr;rows+=ss
    neg=[] if args.large else controls(next(r for r in records if r['input']['name']=='repeated_edge17'))
    result=dict(kind='exact_supporting_execution_not_Lean',scope='selected_high_dimensional_short_walks' if args.large else 'small_geometries_and_exhaustive_finite_families',
                generic=generic,original_H_square_systems=systems,models=rows,controls=neg,
                totals=dict(ledgers=len(rows),edge_occurrences=sum(r['edge_occurrences'] for r in rows),
                            strictly_improved_over_greedy=sum(r['optimal_max_load']<r['greedy_max_load'] for r in rows)))
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'report.json').write_text(json.dumps(result,indent=2)+'\n');(args.out/'fixtures.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(result['totals']));print(json.dumps(generic))

if __name__=='__main__':main()
