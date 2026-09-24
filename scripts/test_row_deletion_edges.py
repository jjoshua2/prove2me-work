#!/usr/bin/env python3
"""Exact original-H edge survival tests, not Lean extraction or a route bound."""
from __future__ import annotations
import argparse,copy,hashlib,itertools,json
from fractions import Fraction as Q
from pathlib import Path
import test_optimal_row_charging as ref

def require(ok,msg):
    if not ok: raise ValueError(msg)

def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))
def enc(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [enc(v) for v in x]
    return x

def interval(A,b,u,w,R):
    delta=sub(w,u);lo=hi=None
    for i in R:
        speed=dot(A[i],delta);slack=b[i]-dot(A[i],u)
        if speed==0:require(slack>=0,'empty supporting line slice')
        elif speed>0:hi=min(hi,slack/speed) if hi is not None else slack/speed
        else:lo=max(lo,slack/speed) if lo is not None else slack/speed
    require(lo is None or hi is None or lo<=hi,'empty line interval')
    return lo,hi

def line_key(u,w):
    D=sub(w,u);j=next(i for i,z in enumerate(D) if z)
    direction=tuple(z/D[j] for z in D)
    base=tuple(x-u[j]*z for x,z in zip(u,direction))
    return base,direction

def produce(A,b,v,u,w,J):
    d=len(v);T=[i for i,a in enumerate(A) if dot(a,u)==b[i]==dot(a,w)]
    S=[i for i in T if dot(A[i],v)<b[i]]
    require(set(S)<=set(J),'edge is not forced into J')
    R=[i for i,a in enumerate(A) if dot(a,v)==b[i] or i in J]
    lo,hi=interval(A,b,u,w,R)
    f=tuple(sum((A[i][j] for i in T),Q(0)) for j in range(d))
    M=sum((b[i] for i in T),Q(0))
    return dict(u=u,w=w,J=sorted(J),kept=R,common=T,eligible=S,
                lower=lo,upper=hi,exposing_normal=f,maximum=M,
                source_extreme_in_relaxation=ref.rank([A[i] for i in R if dot(A[i],u)==b[i]],d)==d,
                target_extreme_in_relaxation=ref.rank([A[i] for i in R if dot(A[i],w)==b[i]],d)==d)

def audit(A,b,v,c):
    u=tuple(map(Q,c['u']));w=tuple(map(Q,c['w']));d=len(v);J=set(c['J'])
    require(u!=w and u!=v and w!=v,'degenerate/target incident edge')
    require(all(dot(a,z)<=bb for a,bb in zip(A,b) for z in (u,w,v)),'infeasible point')
    require(ref.rank([a for a,bb in zip(A,b) if dot(a,v)==bb],d)==d,'nonextreme target')
    T=[i for i,a in enumerate(A) if dot(a,u)==b[i]==dot(a,w)]
    S=[i for i in T if dot(A[i],v)<b[i]]
    require(c['common']==T and c['eligible']==S and S,'incorrect edge rows')
    require(ref.rank([A[i] for i in T],d)==d-1,'not an exposed line')
    require(set(S)<=J,'forced hypothesis false')
    R=[i for i,a in enumerate(A) if dot(a,v)==b[i] or i in J]
    require(c['kept']==R and set(T)<=set(R),'lost active row')
    require(interval(A,b,u,w,list(range(len(A))))==(Q(0),Q(1)),'not whole original edge')
    lo=None if c['lower'] is None else Q(c['lower'])
    hi=None if c['upper'] is None else Q(c['upper'])
    require((lo,hi)==interval(A,b,u,w,R),'incorrect relaxed interval')
    require((lo is None or lo<=0) and (hi is None or hi>=1),'old segment not retained')
    f=tuple(map(Q,c['exposing_normal']));M=Q(c['maximum'])
    require(f==tuple(sum((A[i][j] for i in T),Q(0)) for j in range(d)),'false support sum')
    require(M==sum((b[i] for i in T),Q(0)) and dot(f,u)==M==dot(f,w),'false support value')
    require(dot(f,v)<M,'target not excluded')
    for z,key in ((u,'source_extreme_in_relaxation'),(w,'target_extreme_in_relaxation')):
        require(c[key]==(ref.rank([A[i] for i in R if dot(A[i],z)==b[i]],d)==d),'false endpoint survival')
    probes={Q(0),Q(1),Q(1,2),Q(-1),Q(2)}
    if lo is not None:probes.update((lo,lo-Q(1,7),lo+Q(1,7)))
    if hi is not None:probes.update((hi,hi-Q(1,7),hi+Q(1,7)))
    for t in probes:
        z=tuple(x+t*dd for x,dd in zip(u,sub(w,u)))
        pq=all(dot(A[i],z)<=b[i] for i in R)
        pp=all(dot(a,z)<=bb for a,bb in zip(A,b))
        require(pq==((lo is None or lo<=t) and (hi is None or t<=hi)),'Q line membership')
        require(pp==(0<=t<=1),'P intersection differs from original segment')
        require(dot(f,z)==M,'support not constant on line')
    return dict(probes=len(probes),rays=int(lo is None or hi is None),
                enlarged=int(lo!=Q(0) or hi!=Q(1)),
                lost_endpoints=int(not c['source_extreme_in_relaxation'])+int(not c['target_extreme_in_relaxation']))

def controls(A,b,v,c):
    changes=[('wrong endpoint',lambda x:x.update(u=x['w'])),
      ('missing active row',lambda x:x['common'].pop()),
      ('false support',lambda x:x['exposing_normal'].__setitem__(0,'999')),
      ('false maximum',lambda x:x.update(maximum='-99')),
      ('wrong extension',lambda x:x.update(upper='0')),
      ('missing retained row',lambda x:x['kept'].pop()),
      ('empty forced row subset',lambda x:x.update(J=[])),
      ('false endpoint status',lambda x:x.update(source_extreme_in_relaxation=not x['source_extreme_in_relaxation']))]
    out=[]
    for name,change in changes:
        cc=copy.deepcopy(c);change(cc)
        try:audit(A,b,v,cc)
        except (ValueError,IndexError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted '+name)
    return out

def models():
    out=[]
    for d in (2,3,4):
        A,b=ref.cube(d);out.append((f'cube{d}',A,b))
    out += [('clipped_square',[(1,0),(-1,0),(0,1),(0,-1),(1,1)],[2,0,2,0,3]),
            ('octahedron3',list(itertools.product((-1,1),repeat=3)),[1]*8),
            ('pyramid3',[(1,0,1),(-1,0,1),(0,1,1),(0,-1,1),(0,0,-1)],[1,1,1,1,0]),
            ('square_in3',[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)],[1,0,1,0,0,0]),
            ('segment3',[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)],[1,0,0,0,0,0]),
            ('unbounded2',[(-1,0),(0,-1),(-1,-1),(-2,-1)],[0,0,-1,Q(-3,2)])]
    for name,A,b in out:
        A=[tuple(map(Q,a)) for a in A];b=list(map(Q,b));d=len(A[0])
        A += [tuple(2*x for x in A[0]),(Q(0),)*d];b += [2*b[0],Q(0)]
        yield name,A,b

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--large',action='store_true');args=ap.parse_args()
    fixtures=[];reports=[];negative=[]
    if args.large:
        specs=[]
        for d in (8,16,32,64):
            A,b=ref.cube(d);v=(Q(0),)*d;path=[(Q(1),)*d]
            for j in reversed(range(d)):
                q=list(path[-1]);q[j]=Q(0);path.append(tuple(q))
            specs.append((f'cube{d}_selected',A,b,[v],list(zip(path,path[1:]))[:-1],0))
    else:
        specs=[]
        for name,A,b in models():
            d=len(A[0]);V,n=ref.vertices(A,b,d);edges=[]
            for u,w in itertools.combinations(V,2):
                if ref.rank([a for a,bb in zip(A,b) if dot(a,u)==bb==dot(a,w)],d)==d-1:
                    ref.edge_check(A,b,u,w,d);edges.append((u,w))
            specs.append((name,A,b,V,edges,n))
    for name,A,b,V,edges,systems in specs:
        records=[];stats=dict(charts=0,probes=0,rays=0,enlarged=0,lost_endpoints=0,distinct_carrier_checks=0)
        for v in V:
            I=[i for i,a in enumerate(A) if dot(a,v)<b[i]]
            Js=[set(I)] if args.large else [{i for k,i in enumerate(I) if mask>>k&1} for mask in range(1<<len(I))]
            if args.large:Js=[]
            for u,w in edges:
                if v in (u,w):continue
                T=[i for i,a in enumerate(A) if dot(a,u)==b[i]==dot(a,w)]
                S={i for i in T if i in I}
                allowed=[S] if args.large else [J for J in Js if S<=J]
                for J in allowed:
                    c=json.loads(json.dumps(enc(produce(A,b,v,u,w,J))))
                    st=audit(A,b,v,c)
                    records.append(dict(target=enc(v),certificate=c))
                    stats['charts']+=1
                    for k,val in st.items():stats[k]+=val
                    if name=='clipped_square' and v==(Q(0),Q(0)) and u==(Q(0),Q(2)) and not negative:
                        negative=controls(A,b,v,c)
            # Equal geometric carriers cannot correspond to two different old edges.
            byJ={}
            for r in records:
                if tuple(map(Q,r['target']))!=v:continue
                c=r['certificate'];key=tuple(c['J']);u=tuple(map(Q,c['u']));w=tuple(map(Q,c['w']))
                lk=line_key(u,w);old=frozenset((u,w));table=byJ.setdefault(key,{})
                require(lk not in table or table[lk]==old,'distinct original edges merged')
                table[lk]=old;stats['distinct_carrier_checks']+=1
        reports.append(dict(name=name,dimension=len(A[0]),original_rows=len(A),original_systems=systems,**stats))
        fixtures.append(dict(name=name,A=enc(A),b=enc(b),records=records))
        print(json.dumps(reports[-1]),flush=True)
    totals={k:sum(r[k] for r in reports) for k in ('charts','probes','rays','enlarged','lost_endpoints','distinct_carrier_checks')}
    report=dict(kind='exact_supporting_execution_not_Lean',scope='selected_high_dimensional_edges' if args.large else 'complete_small_H_vertices_and_all_target_slack_subsets',models=reports,totals=totals,controls=negative)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
    print(json.dumps(totals))
if __name__=='__main__':main()
