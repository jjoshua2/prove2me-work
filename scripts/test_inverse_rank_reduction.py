#!/usr/bin/env python3
"""Exact finite-data and original-planar-edge tests; not Lean verification."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse,json,time
import inverse_rank_planar as ir
need=ir.require; dot=ir.dot


def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def cross(a,b): return a[0]*b[1]-a[1]*b[0]


def hull(points):
    P=sorted(set(tuple(map(Q,p)) for p in points))
    need(len(P)>=3,'polygon requires three points')
    def chain(seq):
        out=[]
        for p in seq:
            while len(out)>=2 and cross(sub(out[-1],out[-2]),sub(p,out[-1]))<=0:out.pop()
            out.append(p)
        return out
    H=chain(P)[:-1]+chain(P[::-1])[:-1]
    need(len(H)==len(P),'input has redundant/interior points')
    return H


def original_polygon(points):
    P=hull(points); rows=[]
    for x,y in zip(P,P[1:]+P[:1]):
        dx,dy=sub(y,x); a=(dy,-dx); rows.append((*a,dot(a,x)))
    for i,row in enumerate(rows):
        vals=[dot(row[:2],z)-row[2] for z in P]
        need(all(v<=0 for v in vals),'non-supporting row')
        need({j for j,v in enumerate(vals) if v==0}=={i,(i+1)%len(P)},'not a whole original edge')
    found=set();systems=0
    for r,s in combinations(rows,2):
        det=cross(r[:2],s[:2]);systems+=1
        if not det:continue
        z=((r[2]*s[1]-r[1]*s[2])/det,(r[0]*s[2]-r[2]*s[0])/det)
        if all(dot(a[:2],z)<=a[2] for a in rows):found.add(z)
    need(found==set(P),'complete original-H vertex enumeration mismatch')
    return P,rows,systems


def interval_edge(rows,x,y):
    need(x!=y,'stationary edge')
    direction=sub(y,x);lower=[];upper=[];common=[]
    for i,row in enumerate(rows):
        slack=row[2]-dot(row[:2],x);slope=dot(row[:2],direction)
        need(slack>=0 and slack-slope>=0,'infeasible edge endpoint')
        if not slope:
            if not slack:common.append(i)
        elif slope>0:upper.append(slack/slope)
        else:lower.append(slack/slope)
    need(common and any(rows[i][0] or rows[i][1] for i in common),'no original support line')
    need(lower and upper and max(lower)==0 and min(upper)==1,'support slice not whole segment')
    return common


def improving(rows,P,x,objective):
    """Compute endpoints along actual active supporting lines, without a graph."""
    for row in rows:
        if dot(row[:2],P[x])!=row[2]:continue
        for sign in (-1,1):
            direction=(sign*row[1],-sign*row[0])
            if dot(direction,objective)<=0:continue
            bounds=[(r[2]-dot(r[:2],P[x]))/dot(r[:2],direction)
                    for r in rows if dot(r[:2],direction)>0]
            if not bounds or min(bounds)<=0:continue
            t=min(bounds);y=tuple(a+t*b for a,b in zip(P[x],direction))
            need(y in P,'support endpoint absent from complete original vertices')
            interval_edge(rows,P[x],y)
            return P.index(y)
    raise ValueError('no improving original edge')


def run_polygon(name,points,targets=None):
    P,rows,systems=original_polygon(points);N=len(P);active=[{i for i,r in enumerate(rows) if dot(r[:2],z)==r[2]} for z in P]
    cache={};audits={};states={};routes=[];inverse_checks=nonacq=extra=0
    selected=list(range(N)) if targets is None else list(targets)
    for v in selected:
        h=tuple(-sum((rows[i][k] for i in active[v]),Q(0)) for k in range(2))
        for x in range(N):
            locks=active[x]&active[v];F=tuple(i for i,a in enumerate(active) if locks<=a)
            key=f'{v}:'+','.join(map(str,F))
            if key not in cache:
                cache[key]=ir.sweep(P,v,F,h);audits[key]=ir.audit(P,v,F,h,cache[key])
            entry=next(c for c in audits[key]['states'] if c['source']==x)
            states[f'{x}:{v}']=dict(face=list(F),numerator=h,rank=entry['rank'],slope=entry['slope'],sweep=key)
        for u in range(N):
            path=[u];edges=[]
            while path[-1]!=v:
                x=path[-1];entry=states[f'{x}:{v}'];D=tuple(entry['slope'])
                def ratio(z):return dot(h,sub(P[z],P[v]))/(1+dot(D,sub(P[z],P[v])))
                rx=ratio(x);objective=tuple(-a+rx*b for a,b in zip(h,D));y=improving(rows,P,x,objective)
                nextentry=states[f'{y}:{v}'];oldnew=len({ratio(z) for z in nextentry['face'] if ratio(z)<ratio(y)})
                need(nextentry['rank']<=oldnew<entry['rank'],'reoptimized rank did not decrease')
                need((active[x]&active[v])<=(active[y]&active[v]),'target lock lost')
                nonacq+=(active[x]&active[v])==(active[y]&active[v]);extra+=nextentry['rank']<oldnew
                support=interval_edge(rows,P[x],P[y]);inverse_checks+=1
                edges.append(dict(x=x,y=y,old_rank=entry['rank'],old_slope_next_rank=oldnew,
                                  next_rank=nextentry['rank'],support=support,objective=objective))
                path.append(y)
                need(len(path)<=N,'unexpected route cycle')
            distance=min((u-v)%N,(v-u)%N)
            need(len(path)-1<=states[f'{u}:{v}']['rank'],'length exceeds rank')
            routes.append(dict(source=u,target=v,path=path,edges=edges,rank=states[f'{u}:{v}']['rank'],distance=distance))
    # Replay disables the sweep producer and does not call the original-edge producer.
    frozen=json.loads(json.dumps(ir.encoded(dict(points=P,rows=rows,sweeps=cache,states=states,routes=routes))))
    saved=ir.sweep;ir.sweep=lambda *a,**kw: (_ for _ in ()).throw(RuntimeError('producer disabled'))
    try:
        for key,c in frozen['sweeps'].items():ir.audit(P,c['target'],c['face'],c['numerator'],c)
        for c in frozen['routes']:
            v=c['target'];p=c['path'];need(p[0]==c['source'] and p[-1]==v,'replay endpoints')
            for x,y,e in zip(p,p[1:],c['edges']):
                need(e['x']==x and e['y']==y,'replay edge binding');interval_edge(rows,P[x],P[y])
                entry=frozen['states'][f'{x}:{v}'];h=tuple(map(Q,entry['numerator']));D=tuple(map(Q,entry['slope']))
                def r(z):return dot(h,sub(P[z],P[v]))/(1+dot(D,sub(P[z],P[v])))
                nxt=frozen['states'][f'{y}:{v}'];lower=len({r(z) for z in nxt['face'] if r(z)<r(y)})
                need(e['next_rank']==nxt['rank'] and e['old_rank']==entry['rank'],'replay ranks')
                need(nxt['rank']<=lower==e['old_slope_next_rank']<entry['rank'],'replay descent')
                need(tuple(map(Q,e['objective']))==tuple(-a+r(x)*b for a,b in zip(h,D)),'replay objective')
    finally:ir.sweep=saved
    report=dict(name=name,vertices=N,original_rows=N,original_pair_systems=systems,targets=len(selected),
                routes=len(routes),edges=inverse_checks,shortest_edges=sum(c['distance'] for c in routes),
                nonshortest_routes=sum(len(c['edges'])>c['distance'] for c in routes),
                ranks_above_distance=sum(c['rank']>c['distance'] for c in routes),nonacquiring_steps=nonacq,
                strict_reoptimization_improvements=extra,arrangements=len(cache),
                crossing_pair_checks=sum(a['pair_checks'] for a in audits.values()),
                arrangement_cells=sum(a['cells'] for a in audits.values()),
                nonpositive_unshifted_witnesses=sum(a['nonpositive_unshifted_witnesses'] for a in audits.values()),
                maximum_rank=max(c['rank'] for c in routes))
    return report,frozen


def finite_checks():
    cases=[]
    for d in (1,2,3,8,16,64):
        v=(Q(0),)*d;h=(Q(1),)+(Q(0),)*(d-1)
        P=[v]+[tuple([Q(k+1)]+[Q(((k+2)*(j+3))%11-5, j+1) for j in range(1,d)]) for k in range(10)]
        S=[0,1,3,6,9];x=1;D=tuple(Q((-1)**j*(j+3),j+1) for j in range(d))
        n=[dot(h,z) for z in P];heights={i:(1+dot(D,z))/n[i] for i,z in enumerate(P) if i}
        c=1-min(heights.values());E=tuple(a+c*b for a,b in zip(D,h));q=[1+dot(E,z) for z in P]
        need(all(a>0 for a in q),'finite global positivity')
        U={heights[i] for i in S if i and heights[x]<heights[i]}
        r=[n[i]/q[i] for i in S];R={a for a in r if a<n[x]/q[x]}
        need(len(R)==len(U)+1,'finite reciprocal rank')
        for i in heights:need(q[i]/n[i]==heights[i]+c,'finite translation')
        for i,j in combinations(heights,2):
            direction=sub(tuple(a/n[i] for a in P[i]),tuple(a/n[j] for a in P[j]))
            need(dot(h,direction)==0,'not in numerator kernel')
        cases.append(dict(dimension=d,global_points=len(P),local_points=len(S),shift=c,
                          lower_rank=len(R),upper_rank=len(U),minimum_denominator=min(q)))
    return cases


def controls(fixture):
    c=next(c for c in fixture['sweeps'].values() if c['breakpoints']);P=fixture['points'];out=[]
    def verify(z):ir.audit(P,c['target'],c['face'],c['numerator'],z)
    edits=[('missing crossing',lambda z:z['breakpoints'].pop()),
           ('missing open cell',lambda z:z['interval_samples'].pop()),
           ('false crossing',lambda z:z['breakpoints'].append('999999')),
           ('omitted line',lambda z:z['lines'].pop()),
           ('false rank',lambda z:z['candidate_ranks'][0].__setitem__(0,0)),
           ('missing source',lambda z:z['chosen'].pop()),
           ('wrong target',lambda z:z.update(target=-1)),
           ('wrong numerator',lambda z:z.update(numerator=[0,0]))]
    for name,edit in edits:
        z=deepcopy(c);edit(z)
        try:verify(z)
        except (ValueError,AssertionError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    # Keep the claimed parameter and slope relation consistent while forcing
    # a genuinely nonpositive denominator; an algebraic witness must still fail.
    z=deepcopy(c);w=next(w for w in z['chosen'] if w['source']!=c['target'])
    t=Q(w['parameter']);H=tuple(map(Q,c['numerator']));e=(-H[1],H[0]);target=c['target']
    points=[tuple(map(Q,p)) for p in P]
    levels=[(1+t*dot(e,sub(p,points[target])))/dot(H,sub(p,points[target]))
            for j,p in enumerate(points) if j!=target]
    badshift=-1-min(levels);w['shift']=badshift;w['slope']=tuple(t*a+badshift*b for a,b in zip(e,H))
    try:verify(z)
    except (ValueError,AssertionError):out.append(dict(case='nonpositive global denominator',rejected=True))
    else:raise AssertionError('accepted nonpositive witness')
    z=deepcopy(c);next(w for w in z['chosen'] if w['source']!=c['target'])['rank']=0
    try:verify(z)
    except (ValueError,AssertionError):out.append(dict(case='false witness optimum',rejected=True))
    else:raise AssertionError('accepted false optimum')
    return out


def models(large=False):
    cases=[('square2',[(0,0),(0,1),(1,0),(1,1)],None),
           ('pentagon2',[(-1,2),(0,0),(2,4),(3,0),(4,2)],None),
           ('hexagon2',[(-2,0),(-1,-2),(2,-1),(3,1),(1,4),(-2,3)],None),
           ('heptagon2',[(-3,0),(-2,-2),(1,-3),(4,0),(3,3),(0,5),(-3,3)],None),
           ('parabola12',[(i,i*i) for i in range(-6,6)],None)]
    if large:
        for n in (24,64):
            P=[(Q(1-t*t,1+t*t),Q(2*t,1+t*t)) for t in range(-(n//2),n//2-1)]+[(Q(-1),Q(0))]
            cases.append((f'rational_circle{n}',P,list(range(0,n,max(1,n//8)))))
    return cases


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--only',default='all');ap.add_argument('--large',action='store_true');ap.add_argument('--target-count',type=int,default=None)
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);reports=[];fixtures=[];negative=[]
    for name,P,targets in models(a.large):
        if a.only not in ('all',name):continue
        if a.target_count is not None:
            need(0<a.target_count<=len(P),'invalid target count');targets=list(range(a.target_count))
        r,f=run_polygon(name,P,targets);reports.append(r);fixtures.append(f);print(json.dumps(r),flush=True)
        if name=='heptagon2':negative=controls(f)
    (a.out/'report.json').write_text(json.dumps(ir.encoded(dict(kind='exact_supporting_tests_not_Lean',models=reports,
                                                               finite_dimension_checks=finite_checks(),controls=negative)),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')

if __name__=='__main__':main()
