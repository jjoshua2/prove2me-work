#!/usr/bin/env python3
"""Strict-chain certificates and exact original-polygon applications.

No reference graph is used by the route producer. Original edges are obtained
by moving linear objectives on original active supporting lines. Auditing every
state transition once also checks all occurrences in the delivered paths.
"""
from fractions import Fraction as Q
from itertools import combinations
from copy import deepcopy
from pathlib import Path
import argparse,json,random
import convex_chain_closed_rank as cc
import inverse_rank_planar as sweep
from test_inverse_rank_reduction import original_polygon,improving,interval_edge,sub,dot


def chart(P,v,h):
    e=(-h[1],h[0]);s=[dot(h,sub(z,P[v])) for z in P]
    cc.need(all(a>0 for j,a in enumerate(s) if j!=v),'strict global target exposure')
    I=sorted((j for j in range(len(P)) if j!=v),key=lambda j:dot(e,sub(P[j],P[v]))/s[j])
    w=[dot(e,sub(P[j],P[v]))/s[j] for j in I];a=[1/s[j] for j in I]
    return I,w,a,e,s


def polygon(name,points,targets=None,compare_sweep=False):
    P,rows,systems=original_polygon(points);N=len(P)
    targets=list(range(N)) if targets is None else list(targets)
    active=[{i for i,r in enumerate(rows) if dot(r[:2],z)==r[2]} for z in P]
    records=[];routes=[];count=0;edge_count=0;cells=0;triples=0;pairs=0;weak_steps=0
    for v in targets:
        # Unequal positive original-row weights exercise more than the old unit exposure.
        h=tuple(-sum((Q(i+2)*rows[i][k] for i in active[v]),Q(0)) for k in range(2))
        I,w,a,e,s=chart(P,v,h);cert=cc.produce(w,a)
        stats=cc.audit(w,a,cert,exhaustive_triples=N<=16)
        triples+=stats['triples'];pairs+=stats['pair_checks']
        positions={j:k for k,j in enumerate(I)}
        ranks={v:0,**{j:cert['ranks'][k]+1 for k,j in enumerate(I)}}
        if compare_sweep:
            comparison=sweep.sweep(P,v,list(range(N)),h)
            sweep.audit(P,v,list(range(N)),h,comparison)
            cc.need(all(wit['rank']==ranks[wit['source']] for wit in comparison['chosen']),'closed form disagrees with exhaustive arrangement')
            cells+=len(comparison['samples'])
        next_map={};edge_records=[]
        for x in range(N):
            if x==v:continue
            k=positions[x];entry=cert['choices'][0 if k<=N-2-k else 1]
            t,c=entry['tilt'],entry['shift'];D=tuple(t*ei+c*hi for ei,hi in zip(e,h))
            q=[1+dot(D,sub(z,P[v])) for z in P]
            cc.need(all(z>0 for z in q),'denominator not positive on all actual vertices')
            rx=s[x]/q[x];obj=tuple(-hi+rx*di for hi,di in zip(h,D))
            y=improving(rows,P,x,obj)
            support=interval_edge(rows,P[x],P[y])
            cc.need(ranks[y]<ranks[x],'constructed original edge does not lower exact rank')
            cc.need(active[x]&active[v] <= active[y]&active[v],'lost a target row')
            F=[j for j,A in enumerate(active) if (active[x]&active[v])<=A]
            local_count=len({s[j]/q[j] for j in F if s[j]/q[j]<rx})
            cc.need(local_count==ranks[x],'full chain rank disagrees with current-face rank')
            weak_steps+=(active[x]&active[v])==(active[y]&active[v])
            next_map[x]=y
            edge_records.append(dict(source=x,target=y,rank_before=ranks[x],rank_after=ranks[y],
                                     slope=D,support=support,objective=obj,face=F))
        for u in range(N):
            p=[u]
            while p[-1]!=v:
                p.append(next_map[p[-1]])
                cc.need(len(p)<=N,'route repeats')
            distance=min((u-v)%N,(v-u)%N)
            cc.need(len(p)-1==ranks[u]==distance,'exact rank is not polygon distance')
            routes.append(dict(source=u,target=v,path=p,rank=ranks[u]))
            count+=1;edge_count+=len(p)-1
        records.append(dict(target=v,numerator=h,order=I,chain=cert,states=edge_records))
    fixture=json.loads(json.dumps(cc.encode(dict(name=name,points=P,rows=rows,targets=records,routes=routes))))
    # Consumer reconstructs charts and original support intervals with both producers disabled.
    oldp,olds=cc.produce,sweep.sweep
    def disabled(*args,**kwargs):raise RuntimeError('producer disabled in replay')
    cc.produce=sweep.sweep=disabled
    try:
        bytarget={}
        for target in fixture['targets']:
            v=target['target'];h=tuple(map(Q,target['numerator']))
            I,w,a,e,s=chart(P,v,h);cc.need(I==target['order'],'chart order changed')
            cc.audit(w,a,target['chain'],exhaustive_triples=False)
            transition={}
            for state in target['states']:
                x,y=state['source'],state['target'];D=tuple(map(Q,state['slope']))
                q=[1+dot(D,sub(z,P[v])) for z in P];cc.need(all(qi>0 for qi in q),'nonpositive replay witness')
                F=[j for j,A in enumerate(active) if active[x]&active[v]<=A]
                oldrank=len({s[j]/q[j] for j in F if s[j]/q[j]<s[x]/q[x]})
                cc.need(oldrank==state['rank_before'],'rank replay mismatch')
                cc.need(state['rank_after']==(0 if y==v else min(I.index(y),N-2-I.index(y))+1),'false next rank')
                cc.need(state['rank_after']<oldrank,'rank failed to decrease')
                cc.need(interval_edge(rows,P[x],P[y])==state['support'],'not a whole original edge')
                transition[x]=y
            bytarget[v]=transition
        for route in fixture['routes']:
            p=route['path'];v=route['target']
            cc.need(p[0]==route['source'] and p[-1]==v,'route endpoints changed')
            cc.need(all(bytarget[v][x]==y for x,y in zip(p,p[1:])),'unknown transition')
            cc.need(len(p)-1==route['rank'],'unaccounted route length')
    finally:cc.produce,sweep.sweep=oldp,olds
    return dict(name=name,vertices=N,original_rows=N,targets=len(targets),routes=count,
                original_edge_occurrences=edge_count,unique_original_steps=len(targets)*(N-1),
                nonacquiring_unique_steps=weak_steps,original_H_pair_systems=systems,
                secant_pair_checks=pairs,exhaustive_triples=triples,reference_arrangement_cells=cells,
                maximum_rank=max(r['rank'] for r in routes)),fixture


def controls():
    w=list(map(Q,range(7)));a=[x*x+1 for x in w];good=cc.produce(w,a);out=[]
    edits=[('false rank',lambda c:c['ranks'].__setitem__(3,0)),
           ('inadequate tilt',lambda c:c.update(bound=Q(0))),
           ('missing tilt',lambda c:c['choices'].pop()),
           ('wrong secant',lambda c:c['adjacent_slopes'].__setitem__(0,Q(-100))),
           ('wrong positive witness',lambda c:c['choices'][0]['heights'].__setitem__(0,Q(-1))),
           ('wrong shift',lambda c:c['choices'][0].update(shift=Q(-10000))),
           ('changed input',lambda c:c.update(ordinates=(Q(10000),)+tuple(c['ordinates'][1:])))]
    for name,edit in edits:
        bad=deepcopy(good);edit(bad)
        try:cc.audit(w,a,bad,True)
        except (ValueError,AssertionError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted malformed '+name)
    for name,W,A in [('unsorted',[0,2,1],[1,4,5]),('weak_convex',list(range(5)),[1]*5),
                     ('concave',list(range(5)),[-i*i for i in range(5)])]:
        try:cc.produce(W,A)
        except (ValueError,AssertionError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted invalid '+name)
    return out


def random_hull(seed):
    rng=random.Random(seed);P=sorted(set((rng.randrange(-100,101),rng.randrange(-100,101)) for _ in range(30)))
    def cross(a,b,c):return (b[0]-a[0])*(c[1]-b[1])-(b[1]-a[1])*(c[0]-b[0])
    def half(S):
        H=[]
        for z in S:
            while len(H)>=2 and cross(H[-2],H[-1],z)<=0:H.pop()
            H.append(z)
        return H
    return half(P)[:-1]+half(P[::-1])[:-1]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--large',action='store_true');ap.add_argument('--random',type=int,default=0)
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    configs=[('square',[(0,0),(0,1),(1,0),(1,1)],None),
             ('pentagon',[(-1,2),(0,0),(2,4),(3,0),(4,2)],None),
             ('heptagon',[(-3,0),(-2,-2),(1,-3),(4,0),(3,3),(0,5),(-3,3)],None)]
    if args.large:
        n=64
        P=[(Q(1-t*t,1+t*t),Q(2*t,1+t*t)) for t in range(-n//2,n//2-1)]+[(Q(-1),Q(0))]
        configs=[('circle64_eight_targets',P,list(range(0,64,8)))]
    if args.random:configs=[(f'random_{k}',random_hull(k),None) for k in range(args.random)]
    reports=[];fixtures=[]
    for name,P,targets in configs:
        r,f=polygon(name,P,targets,compare_sweep=not args.large)
        reports.append(r);fixtures.append(f);print(json.dumps(r),flush=True)
    finite=[]
    for N in (1,2,3,7,20):
        W=[Q(i*i+i,2) for i in range(N)];A=[x*x-Q(5)*x-Q(9) for x in W]
        c=cc.produce(W,A);r=cc.audit(W,A,c,True);finite.append(dict(input=cc.encode(c),audit=r))
    report=dict(kind='executed_exact_checks_not_Lean',models=reports,finite_chains=finite,controls=controls())
    (args.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
if __name__=='__main__':main()
