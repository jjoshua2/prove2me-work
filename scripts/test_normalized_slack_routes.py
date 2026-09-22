#!/usr/bin/env python3
"""Exact supporting tests, not Lean or verified Python/JSON.

The producer linearizes a fractional slack, calls the unchanged original-edge
constructor, and charges only a minimum-weight determining set. The consumer
independently enumerates subsets, recomputes ratios, and checks whole edge faces.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old


def need(ok, message):
    if not ok:
        raise ValueError(message)


def exact_rank(rows, d):
    M=[list(map(Q,row)) for row in rows]; r=0
    for j in range(d):
        p=next((i for i in range(r,len(M)) if M[i][j]),None)
        if p is None: continue
        M[r],M[p]=M[p],M[r]; a=M[r][j]; M[r]=[x/a for x in M[r]]
        for i in range(r+1,len(M)):
            a=M[i][j]
            if a: M[i]=[x-a*y for x,y in zip(M[i],M[r])]
        r+=1
    return r


def ratio(row, den, x):
    value=den[-1]+g.dot(den[:-1],x)
    need(value>0,'nonpositive affine denominator')
    return (row[-1]-g.dot(row[:-1],x))/value


def spectra(model, rows, dens):
    need(len(rows)==len(dens),'wrong denominator count')
    d=len(model['vertices'][0])
    need(all(len(z)==d+1 for z in dens),'wrong denominator dimension')
    return [sorted({ratio(r,z,x) for x in model['vertices']}) for r,z in zip(rows,dens)]


def select(model,rows,values,u,v):
    V=model['vertices'];d=len(V[0]);G=old.active(rows,V[u])&old.active(rows,V[v]);T=old.active(rows,V[v])-G
    options=[]
    for n in range(min(d,len(T))+1):
        for S in combinations(sorted(T),n):
            if g.rank([rows[i][:-1] for i in G|set(S)])==d:
                options.append((sum(len(values[i])-1 for i in S),n,S))
    need(options,'no determining set')
    w,_,S=min(options)
    return list(S),w,G,T


def produce(model,rows,dens,u,v):
    V=model['vertices'];values=spectra(model,rows,dens)
    S,budget,G,T=select(model,rows,values,u,v);target=old.active(rows,V[v]);p=[u];phases=[];edges=[]
    while p[-1]!=v:
        due=set(S)-old.active(rows,V[p[-1]]);need(due,'lost determining condition')
        j=min(due);start=len(p)-1
        while j not in old.active(rows,V[p[-1]]):
            x=p[-1];r=ratio(rows[j],dens[j],V[x]);need(r>0,'missing row has zero slack')
            f=tuple(A+r*D for A,D in zip(rows[j][:-1],dens[j][:-1]))
            locks=target&old.active(rows,V[x])
            F=frozenset(i for i,z in enumerate(V) if locks<=old.active(rows,z))
            y,edge=g.improving_edge(model,F,x,f)
            need(ratio(rows[j],dens[j],V[y])<r,'fractional progress failed')
            need(locks<=old.active(rows,V[y]),'lost target row')
            edges.append(dict(row=j,entry_ratio=r,edge=edge));p.append(y)
            need(len(p)-1-start<=len(values[j])-1,'phase cost exceeded')
        phases.append(dict(row=j,start=start,end=len(p)-1))
    return dict(u=u,v=v,selected=S,shared=sorted(G),missing=sorted(T),spectra=values,
                budget=budget,path=p,phases=phases,edges=edges)


def consume(model,rows,dens,c):
    old.validate_h(model,rows);V=model['vertices'];d=len(V[0]);n=len(V)
    u=c['u'];v=c['v'];p=c['path'];S=c['selected'];need(0<=u<n and 0<=v<n,'endpoint index')
    values=spectra(model,rows,dens);need([list(map(Q,s)) for s in c['spectra']]==values,'false complete spectra')
    G=old.active(rows,V[u])&old.active(rows,V[v]);target=old.active(rows,V[v]);T=target-G
    need(c['shared']==sorted(G) and c['missing']==sorted(T),'false initial labels')
    need(len(S)==len(set(S)) and set(S)<=T and len(S)<=min(d,len(rows)-d),'illegal selected set')
    need(exact_rank([rows[i][:-1] for i in G|set(S)],d)==d,'nontrivial determining kernel')
    budget=sum(len(values[i])-1 for i in S);need(c['budget']==budget,'wrong normalized budget')
    labels=sorted(T);count=0
    for mask in range(1<<len(labels)):
        R={labels[k] for k in range(len(labels)) if mask>>k&1}
        if len(R)>d or exact_rank([rows[i][:-1] for i in G|R],d)!=d:continue
        count+=1;need(budget<=sum(len(values[i])-1 for i in R),'nonminimum selected budget')
    need(count>0,'empty competitor family')
    need(p and p[0]==u and p[-1]==v and all(0<=x<n for x in p),'wrong route endpoints')
    need(len(p)-1<=budget and len(c['edges'])==len(p)-1,'wrong route length')
    K=max([0]+[len(values[i])-1 for i in S]);need(budget<=K*min(d,len(rows)-d),'dimension bound')
    charged=set();cursor=0;long_phases=0;nonacq=0;linear_changes=0
    for phase in c['phases']:
        j=phase['row'];lo=phase['start'];hi=phase['end']
        need(j in S and j not in charged,'invalid or repeated charge')
        need(lo==cursor and lo<hi<len(p) and hi-lo<=len(values[j])-1,'phase partition/cost')
        need(j not in old.active(rows,V[p[lo]]) and j in old.active(rows,V[p[hi]]),'phase endpoints')
        prev_obj=None
        for k in range(lo,hi):
            x,y=p[k:k+2];rec=c['edges'][k];e=rec['edge'];r=ratio(rows[j],dens[j],V[x])
            need(rec['row']==j and Q(rec['entry_ratio'])==r,'wrong phase ratio')
            obj=tuple(A+r*D for A,D in zip(rows[j][:-1],dens[j][:-1]))
            need(tuple(map(Q,e['objective']))==obj,'objective not current linearization')
            need(ratio(rows[j],dens[j],V[y])<r,'not decreasing normalized slack')
            before=target&old.active(rows,V[x]);after=target&old.active(rows,V[y])
            need(before<=after,'target-lock violation')
            F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
            need(e['u']==x and e['v']==y and set(e['face'])==F,'wrong whole locked face')
            g.verify_record(model,e)
            nonacq+=before==after;linear_changes+=prev_obj is not None and prev_obj!=obj;prev_obj=obj
        charged.add(j);cursor=hi;long_phases+=hi-lo>1
    need(cursor==len(p)-1,'uncovered edge')
    return dict(candidates=count,multiedge_phases=long_phases,nonacquiring_steps=nonacq,
                within_phase_objective_changes=linear_changes)


def models():
    for name,points in g.models()[:10]:
        M=g.reference(points);rows=old.h_rows(M);d=len(points[0])
        for mode in ('constant','rowwise'):
            dens=[]
            for j in range(len(rows)):
                c=tuple(Q(((j+2)*(i+3))%7-3,7) if mode=='rowwise' else Q(0) for i in range(d))
                a=Q(1,2**30)-min(g.dot(c,x) for x in M['vertices']) if mode=='rowwise' else Q(1)
                dens.append((*c,a))
            yield name+'_'+mode,M,rows,dens
    hexagon=[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]
    for name,points in [('cube2',list(product((0,1),repeat=2))),('cube3',list(product((0,1),repeat=3))),('hexagon',hexagon)]:
        base=g.reference(points);rs=old.h_rows(base);d=len(points[0]);w=tuple(Q(2**j,8) for j in range(d))
        newpts=[tuple(z/(1+g.dot(w,x)) for z in x) for x in base['points']]
        need(all(1+g.dot(w,x)>0 for x in base['points']),'projective chart crossing')
        M=g.reference(newpts);rows=[tuple(A+b*t for A,t in zip(row[:-1],w))+(row[-1],) for row in rs for b in [row[-1]]]
        dens=[tuple(-t for t in w)+(Q(1),) for _ in rows]
        yield 'projective_'+name,M,rows,dens


def controls(M,rows,dens,c):
    cases=[('wrong budget',lambda z:z.update(budget=0)),
      ('missing ratio value',lambda z:z['spectra'][z['selected'][0]].pop()),
      ('empty determining set',lambda z:z.update(selected=[])),
      ('wrong current ratio',lambda z:z['edges'][0].update(entry_ratio=-1)),
      ('stationary edge',lambda z:z['edges'][0]['edge'].update(v=z['path'][0])),
      ('wrong linearization',lambda z:z['edges'][0]['edge'].update(objective=[0]*len(M['vertices'][0])))]
    out=[]
    for name,edit in cases:
        bad=deepcopy(c);edit(bad)
        try:consume(M,rows,dens,bad)
        except (ValueError,AssertionError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted '+name)
    for name,den in [('zero denominator',[(Q(0),)*(len(M['vertices'][0])+1)]*len(rows)),
                     ('negative denominator',[(Q(0),)*len(M['vertices'][0])+(Q(-1),)]*len(rows))]:
        try:consume(M,rows,den,c)
        except (ValueError,AssertionError):out.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted '+name)
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True);p.add_argument('--only',default='all');a=p.parse_args()
    a.out.mkdir(parents=True,exist_ok=True);reports=[];fixtures=[];bad=[]
    for name,M,rows,dens in models():
        if a.only!='all' and a.only!=name:continue
        old.validate_h(M,rows);certs=[];counts=dict(routes=0,edges=0,shortest_edges=0,nonshortest=0,candidates=0,multiedge_phases=0,nonacquiring_steps=0,within_phase_objective_changes=0)
        for u in range(len(M['vertices'])):
            distances=old.distances(M,u)
            for v in range(len(M['vertices'])):
                c=produce(M,rows,dens,u,v);r=consume(M,rows,dens,c);certs.append(c);L=len(c['path'])-1
                counts['routes']+=1;counts['edges']+=L;counts['shortest_edges']+=distances[v];counts['nonshortest']+=L>distances[v]
                for k,val in r.items():counts[k]+=val
                if name=='projective_cube2' and L and not bad:bad=controls(M,rows,dens,c)
        frozen=json.loads(json.dumps(g.encoded(certs)));orig=(globals()['select'],globals()['produce'],g.improving_edge)
        def disabled(*args,**kwargs):raise RuntimeError('producer disabled')
        globals()['select']=globals()['produce']=g.improving_edge=disabled
        try:
            for c in frozen:consume(M,rows,dens,c)
        finally:globals()['select'],globals()['produce'],g.improving_edge=orig
        report=dict(name=name,dimension=len(M['vertices'][0]),vertices=len(M['vertices']),original_rows=len(rows),**counts)
        reports.append(report);fixtures.append(dict(name=name,points=M['points'],rows=rows,denominators=dens,certificates=frozen));print(json.dumps(report),flush=True)
    (a.out/'report.json').write_text(json.dumps(dict(kind='exact_supporting_tests_not_Lean',models=reports,controls=bad),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')

if __name__=='__main__':main()
