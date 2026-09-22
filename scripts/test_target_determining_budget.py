#!/usr/bin/env python3
"""Exact supporting tests, not Lean or JSON-parser verification.

The producer chooses small original-row subsets. The consumer independently
exhausts all bitmasks, tests rank, and checks each phase and whole original edge.
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
import test_target_row_level_budget as prior

require=prior.require


def choose_set(rows,V,u,v,values):
    d=len(V[0]);G=old.active(rows,V[u])&old.active(rows,V[v]);T=old.active(rows,V[v])-old.active(rows,V[u])
    weights=[len(x)-1 for x in values];choices=[]
    for n in range(min(d,len(T))+1):
        for s in combinations(sorted(T),n):
            if g.rank([rows[i][:-1] for i in G|set(s)])==d:
                choices.append((sum(weights[i] for i in s),len(s),s))
    require(bool(choices),'no determining completion')
    weight,_,S=min(choices)
    return dict(selected=list(S),shared=sorted(G),missing=sorted(T),weight=weight,
                candidate_count=len(choices),common_rank=g.rank([rows[i][:-1] for i in G]))


def produce(model,rows,u,v):
    V=model['vertices'];values=prior.row_values(model,rows)
    selection=choose_set(rows,V,u,v,values);selected=set(selection['selected'])
    target=old.active(rows,V[v]);path=[u];phases=[];records=[]
    while path[-1]!=v:
        due=selected-old.active(rows,V[path[-1]])
        require(bool(due),'selected/common rows did not determine target')
        j=min(due);start=len(path)-1;pv=[g.dot(rows[j][:-1],V[path[-1]])]
        while j not in old.active(rows,V[path[-1]]):
            x=path[-1];before=target&old.active(rows,V[x])
            F=frozenset(i for i,z in enumerate(V) if before<=old.active(rows,z))
            y,edge=g.improving_edge(model,F,x,rows[j][:-1]);after=target&old.active(rows,V[y])
            require(before<=after,'lost target lock')
            records.append(dict(row=j,edge=edge,before=sorted(before),after=sorted(after)))
            path.append(y);pv.append(g.dot(rows[j][:-1],V[y]))
            require(len(pv)<=len(values[j]),'phase exceeded level count')
        phases.append(dict(row=j,start=start,end=len(path)-1,values=pv))
    return dict(u=u,v=v,selection=selection,row_values=values,path=path,phases=phases,edges=records,
                prior_budget=sum(len(values[i])-1 for i in selection['missing']),
                selected_K=max([0]+[len(values[i])-1 for i in selected]))


def audit_selection(rows,V,u,v,values,s):
    d=len(V[0]);G=old.active(rows,V[u])&old.active(rows,V[v]);T=old.active(rows,V[v])-old.active(rows,V[u]);S=s['selected']
    require(len(S)==len(set(S)) and set(S)<=T and len(S)<=d,'illegal selected labels')
    require(s['shared']==sorted(G) and s['missing']==sorted(T),'false shared/missing set')
    require(g.rank([rows[i][:-1] for i in G|set(S)])==d,'nontrivial selected/common kernel')
    require(s['common_rank']==g.rank([rows[i][:-1] for i in G]),'wrong common rank')
    weights=[len(x)-1 for x in values];weight=sum(weights[i] for i in S)
    require(s['weight']==weight,'wrong selected weight')
    labels=sorted(T);valid=0
    # Independent bitmask enumeration, without calling choose_set.
    for mask in range(1<<len(labels)):
        candidate={labels[i] for i in range(len(labels)) if mask>>i&1}
        if len(candidate)>d or g.rank([rows[i][:-1] for i in G|candidate])!=d:continue
        valid+=1;require(weight<=sum(weights[i] for i in candidate),'nonminimum weight')
    require(valid==s['candidate_count'] and valid>0,'wrong candidate count')
    require(len(S)<=min(d,len(rows)-d),'original cardinality bound')
    return G,T,set(S),weights


def consume(model,rows,c):
    V=model['vertices'];u=c['u'];v=c['v'];p=c['path'];d=len(V[0]);m=len(rows)
    require(0<=u<len(V) and 0<=v<len(V),'invalid endpoint')
    values=prior.row_values(model,rows)
    require([list(map(Q,s)) for s in c['row_values']]==values,'false actual row levels')
    G,T,S,weights=audit_selection(rows,V,u,v,values,c['selection'])
    require(p and p[0]==u and p[-1]==v and all(0<=x<len(V) for x in p),'route endpoints')
    require(len(c['edges'])==len(p)-1,'edge record count')
    K=max([0]+[weights[i] for i in S]);budget=c['selection']['weight'];previous=sum(weights[i] for i in T)
    require(c['selected_K']==K and c['prior_budget']==previous,'wrong bound summaries')
    require(len(p)-1<=budget<=previous and budget<=K*min(d,m-d),'weighted bound')
    charged=set();cursor=0;target=old.active(rows,V[v])
    for phase in c['phases']:
        j=phase['row'];lo=phase['start'];hi=phase['end']
        require(j in S and j not in charged,'unchosen/repeated phase')
        require(lo==cursor and lo<hi<len(p),'phase partition')
        before=S-old.active(rows,V[p[lo]]);after=S-old.active(rows,V[p[hi]])
        require(j in before and after<=before-{j},'due set did not shrink')
        actual=[g.dot(rows[j][:-1],V[p[t]]) for t in range(lo,hi+1)]
        require(actual==list(map(Q,phase['values'])) and all(a<b for a,b in zip(actual,actual[1:])), 'nonincreasing phase')
        require(actual[-1]==rows[j][-1] and hi-lo<=weights[j],'phase endpoint/cost')
        require(sum(weights[i] for i in after)+weights[j]<=sum(weights[i] for i in before),'phase accounting')
        require(all(c['edges'][t]['row']==j for t in range(lo,hi)),'mixed objectives')
        charged.add(j);cursor=hi
    require(cursor==len(p)-1,'uncovered edges')
    for x in p:require(G<=old.active(rows,V[x]),'lost common equation')
    for (x,y),r in zip(zip(p,p[1:]),c['edges']):
        before=target&old.active(rows,V[x]);after=target&old.active(rows,V[y])
        require(before<=after and r['before']==sorted(before) and r['after']==sorted(after),'false target locks')
        edge=r['edge'];j=r['row'];F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
        require(edge['u']==x and edge['v']==y and set(edge['face'])==F,'whole locked face')
        require(tuple(map(Q,edge['objective']))==rows[j][:-1],'wrong objective')
        g.verify_record(model,edge)
    return True


def cases():
    vals=[(n,p,'ordinary') for n,p in g.models()]
    vals += [('moment4',[(i,i*i,i**3,i**4) for i in range(7)],'ordinary'),
             ('hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],'ordinary'),
             ('octahedron3',[tuple(s if i==j else 0 for i in range(3)) for j in range(3) for s in (-1,1)],'ordinary'),
             ('binary_redundant_cube',list(product((0,1),repeat=3)),'binary'),
             ('duplicate_hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],'duplicates')]
    return vals


def negative_controls(model,rows,good):
    mutations=[
        ('empty nondetermining set',lambda x:x['selection'].update(selected=[])),
        ('false shared equations',lambda x:x['selection'].update(shared=[])),
        ('wrong minimum cost',lambda x:x['selection'].update(weight=x['selection']['weight']+1)),
        ('wrong candidate count',lambda x:x['selection'].update(candidate_count=0)),
        ('duplicate selected label',lambda x:x['selection']['selected'].append(x['selection']['selected'][0])),
        ('unchosen phase',lambda x:x['phases'][0].update(row=-1)),
        ('recharged phase',lambda x:x['phases'].append(deepcopy(x['phases'][0]))),
        ('missing actual level',lambda x:x['row_values'][x['selection']['selected'][0]].pop()),
        ('stationary edge',lambda x:x['edges'][0]['edge'].update(v=x['path'][0])),
        ('zero objective',lambda x:x['edges'][0]['edge'].update(objective=[0]*len(model['vertices'][0]))),
    ];out=[]
    for name,edit in mutations:
        c=deepcopy(good);edit(c)
        try:consume(model,rows,c)
        except (ValueError,AssertionError):out.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted malformed certificate: '+name)
    return out


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--only',default='all')
    args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True);reports=[];fixtures=[];controls=[]
    for name,points,mode in cases():
        if args.only!='all' and args.only!=name:continue
        model=g.reference(points);rows=old.h_rows(model);V=model['vertices'];d=len(V[0])
        if mode=='binary':rows=rows+[(Q(1),Q(2),Q(4),Q(7))]
        if mode=='duplicates':rows=rows+[tuple(Q(2)*x for x in row) for row in rows]+[rows[0]]
        old.validate_h(model,rows);certs=[]
        total=shortest=nonshort=improved=common_saved=largeT=longphases=nonacq=candidates=best_gap=0
        for u in range(len(V)):
            distances=old.distances(model,u)
            for v in range(len(V)):
                c=produce(model,rows,u,v);consume(model,rows,c);certs.append(c)
                L=len(c['path'])-1;total+=L;shortest+=distances[v];nonshort+=L>distances[v]
                improved+=c['selection']['weight']<c['prior_budget']
                common_saved+=c['selection']['common_rank']>0 and u!=v
                largeT+=len(c['selection']['missing'])>d
                best_gap=max(best_gap,c['prior_budget']-c['selection']['weight'])
                longphases+=sum(p['end']-p['start']>1 for p in c['phases'])
                nonacq+=sum(r['before']==r['after'] for r in c['edges'])
                candidates+=c['selection']['candidate_count']
                if name=='hexagon' and not controls and L and c['selection']['shared']:controls=negative_controls(model,rows,c)
        frozen=json.loads(json.dumps(g.encoded(certs)));originals=(globals()['choose_set'],globals()['produce'],g.improving_edge)
        def disabled(*a,**kw):raise RuntimeError('producer disabled')
        globals()['choose_set']=globals()['produce']=g.improving_edge=disabled
        try:
            for c in frozen:consume(model,rows,c)
        finally:globals()['choose_set'],globals()['produce'],g.improving_edge=originals
        report=dict(name=name,dimension=d,vertices=len(V),original_rows=len(rows),routes=len(certs),edges=total,
                    shortest_edges=shortest,nonshortest_routes=nonshort,strictly_smaller_budgets=improved,
                    nontrivial_shared_cases=common_saved,cases_with_more_than_d_missing_rows=largeT,
                    maximum_budget_saving=best_gap,multi_edge_phases=longphases,nonacquiring_steps=nonacq,
                    determining_candidates_checked=candidates)
        reports.append(report);fixtures.append(dict(name=name,points=model['points'],rows=rows,certificates=frozen));print(json.dumps(report),flush=True)
    (args.out/'report.json').write_text(json.dumps(dict(kind='exact_supporting_tests_not_Lean_verification',models=reports),indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    (args.out/'negative-controls.json').write_text(json.dumps(dict(controls=controls),indent=2)+'\n')

if __name__=='__main__':main()
