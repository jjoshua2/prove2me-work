#!/usr/bin/env python3
"""Exact target-row phase certificates; supporting tests, not Lean verification.

The producer uses a geometric improving-edge construction, not the independent
reference graph. The consumer checks full original-H bindings, actual row-value
sets, disjoint phase labels, target locks and every whole exposed edge certificate.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old


def require(condition, message):
    if not condition:
        raise ValueError(message)


def row_values(model, rows):
    return [sorted({g.dot(row[:-1], x) for x in model['vertices']}) for row in rows]


def produce(model, rows, u, v):
    V=model['vertices']; values=row_values(model,rows)
    T=old.active(rows,V[v]); initial=T-old.active(rows,V[u]); path=[u]; phases=[]; edges=[]
    while path[-1]!=v:
        missing=T-old.active(rows,V[path[-1]])
        require(bool(missing),'active target rows did not determine vertex')
        j=min(missing); start=len(path)-1; phase_values=[g.dot(rows[j][:-1],V[path[-1]])]
        while j not in old.active(rows,V[path[-1]]):
            x=path[-1]; before=T & old.active(rows,V[x])
            F=frozenset(i for i,z in enumerate(V) if before<=old.active(rows,z))
            w,record=g.improving_edge(model,F,x,rows[j][:-1])
            after=T & old.active(rows,V[w])
            require(before<=after,'lost original target row')
            edges.append(dict(edge=record,row=j,before=sorted(before),after=sorted(after)))
            path.append(w); phase_values.append(g.dot(rows[j][:-1],V[w]))
            require(len(phase_values)<=len(values[j]),'phase exceeded distinct-value budget')
        phases.append(dict(row=j,start=start,end=len(path)-1,values=phase_values))
    return dict(u=u,v=v,path=path,phases=phases,edges=edges,
                row_values=values,initial_missing=sorted(initial),
                budget=sum(len(values[j])-1 for j in initial),
                K=max([0]+[len(values[j])-1 for j in T]),
                m=len(rows),d=len(V[0]))


def consume(model, rows, c):
    V=model['vertices']; n=len(V); m=len(rows); d=len(V[0]); p=c['path']; u=c['u'];v=c['v']
    require(0<=u<n and 0<=v<n,'endpoint index')
    require(p and p[0]==u and p[-1]==v and all(0<=x<n for x in p),'route endpoints')
    values=row_values(model,rows)
    require([[Q(x) for x in S] for S in c['row_values']]==values,'incorrect full vertex-value sets')
    T=old.active(rows,V[v]); initial=T-old.active(rows,V[u]); weights=[len(S)-1 for S in values]
    require(c['initial_missing']==sorted(initial),'incorrect initial missing labels')
    budget=sum(weights[j] for j in initial); K=max([0]+[weights[j] for j in T])
    require(c['m']==m and c['d']==d and c['budget']==budget and c['K']==K,'incorrect input/budget')
    require(len(initial)<=m-d and len(p)-1<=budget<=K*(m-d),'weighted/original bound')
    require(len(c['edges'])==len(p)-1,'edge count')
    cursor=0; charged=set(); cost=0
    for phase in c['phases']:
        j=phase['row']; lo=phase['start']; hi=phase['end']
        require(lo==cursor and lo<hi<len(p),'phase partition')
        require(j in initial and j not in charged,'recharged label')
        require(j not in old.active(rows,V[p[lo]]) and j in old.active(rows,V[p[hi]]),'phase acquisition')
        vals=[g.dot(rows[j][:-1],V[p[t]]) for t in range(lo,hi+1)]
        require(vals==list(map(Q,phase['values'])) and all(a<b for a,b in zip(vals,vals[1:])),
                'phase not strictly increasing in selected original row')
        require(all(x in values[j] for x in vals) and hi-lo<=weights[j],'phase cardinal budget')
        require(all(c['edges'][t]['row']==j for t in range(lo,hi)),'changed phase objective')
        before_missing=T-old.active(rows,V[p[lo]]); after_missing=T-old.active(rows,V[p[hi]])
        require(after_missing<=before_missing-{j},'unpaid set did not shrink')
        require(sum(weights[i] for i in after_missing)+weights[j]<=sum(weights[i] for i in before_missing),
                'weighted phase accounting')
        charged.add(j);cost+=weights[j];cursor=hi
    require(cursor==len(p)-1 and cost<=budget,'uncovered edges or overcharged rows')
    for (x,y),r in zip(zip(p,p[1:]),c['edges']):
        before=T&old.active(rows,V[x]); after=T&old.active(rows,V[y]);j=r['row']
        require(before<=after and r['before']==sorted(before) and r['after']==sorted(after),'false target locks')
        e=r['edge']; F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
        require(e['u']==x and e['v']==y and set(e['face'])==F,'false whole locked face')
        require(tuple(map(Q,e['objective']))==rows[j][:-1],'wrong original-row objective')
        g.verify_record(model,e)
    return True


def controls(model, rows, good):
    cases=[
        ('missing vertex value',lambda c:c['row_values'][c['phases'][0]['row']].pop()),
        ('recharged label',lambda c:c['phases'].append(deepcopy(c['phases'][0]))),
        ('wrong phase endpoint',lambda c:c['phases'][0].update(end=c['phases'][0]['start'])),
        ('understated original bound',lambda c:c.update(budget=0)),
        ('wrong K',lambda c:c.update(K=c['K']+1)),
        ('stationary edge',lambda c:c['edges'][0]['edge'].update(v=c['path'][0])),
        ('zero objective',lambda c:c['edges'][0]['edge'].update(objective=[0]*c['d'])),
        ('wrong row values',lambda c:c['phases'][0]['values'].reverse()),
    ]
    out=[]
    for name,edit in cases:
        c=deepcopy(good);edit(c)
        try:consume(model,rows,c)
        except (ValueError,AssertionError):out.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted corruption: '+name)
    return out


def small(out, only='all'):
    cases=[(n,p,False) for n,p in g.models()]
    cases += [('moment4',[(i,i*i,i**3,i**4) for i in range(7)],False),
              ('hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],False),
              ('redundant_hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1),(1,1)],True)]
    results=[];fixtures=[];bad=[]
    for name,points,extra in cases:
        if only!='all' and only!=name:continue
        model=g.reference(points); rows=old.h_rows(model);V=model['vertices'];d=len(V[0])
        if extra:rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])]
        old.validate_h(model,rows);vals=row_values(model,rows)
        certs=[];total=shortest=nonshort=longphases=noacq=0
        multi=[sum(len(vals[j])>2 for j in old.active(rows,x)) for x in V]
        for u in range(len(V)):
            distances=old.distances(model,u)
            for v in range(len(V)):
                c=produce(model,rows,u,v);consume(model,rows,c);certs.append(c)
                L=len(c['path'])-1;total+=L;shortest+=distances[v];nonshort+=L>distances[v]
                longphases+=sum(s['end']-s['start']>1 for s in c['phases'])
                noacq+=sum(e['before']==e['after'] for e in c['edges'])
                if not bad and L and name=='hexagon':bad=controls(model,rows,c)
        frozen=json.loads(json.dumps(g.encoded(certs)))
        originals=(globals()['produce'],g.improving_edge)
        def disabled(*a,**kw):raise RuntimeError('producer disabled')
        globals()['produce']=g.improving_edge=disabled
        try:
            for c in frozen:consume(model,rows,c)
        finally:globals()['produce'],g.improving_edge=originals
        r=dict(name=name,vertices=len(V),rows=len(rows),dimension=d,routes=len(certs),edges=total,
               shortest_edges=shortest,nonshortest=nonshort,multistep_phases=longphases,
               nonacquiring_steps=noacq,targets_with_over_three_multilevel_rows=sum(k>3 for k in multi),
               max_multilevel_target_rows=max(multi),max_target_K=max([0]+[len(S)-1 for S in vals]))
        print(json.dumps(r),flush=True);results.append(r)
        fixtures.append(dict(name=name,points=model['points'],rows=rows,certificates=frozen))
    out.mkdir(parents=True,exist_ok=True)
    (out/'report.json').write_text(json.dumps({'kind':'exact_tests_not_Lean_verification','models':results},indent=2)+'\n')
    (out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    (out/'negative-controls.json').write_text(json.dumps({'controls':bad},indent=2)+'\n')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--only',default='all');args=ap.parse_args();small(args.out,args.only)

if __name__=='__main__':main()
