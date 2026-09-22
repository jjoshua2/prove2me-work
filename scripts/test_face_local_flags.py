#!/usr/bin/env python3
"""Exact supporting computations, not Lean or JSON-parser verification.

DP selects an ordered original-row flag. An independent permutation enumeration
checks optimality. Whole-edge records use unchanged original-hull geometry;
no reference edge table is read by the route producer.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old


def need(ok, message):
    if not ok:
        raise ValueError(message)


def exact_rank(rows, dimension):
    """Independent rational row reduction, separate from the producer's SymPy."""
    M=[list(map(Q,row)) for row in rows]; rank=0
    for col in range(dimension):
        pivot=next((i for i in range(rank,len(M)) if M[i][col]),None)
        if pivot is None: continue
        M[rank],M[pivot]=M[pivot],M[rank];v=M[rank][col]
        M[rank]=[x/v for x in M[rank]]
        for i in range(rank+1,len(M)):
            a=M[i][col]
            if a:M[i]=[x-a*y for x,y in zip(M[i],M[rank])]
        rank+=1
    return rank


class OriginalData:
    def __init__(self, model, rows):
        self.model=model; self.rows=rows; self.V=model['vertices']; self.d=len(self.V[0])
        self.active=[old.active(rows,x) for x in self.V]
        self.values=[[g.dot(row[:-1],x) for x in self.V] for row in rows]
        old.validate_h(model,rows)
    @lru_cache(None)
    def face(self,H):
        return tuple(i for i,a in enumerate(self.active) if set(H)<=a)
    @lru_cache(None)
    def rank(self,H):
        return g.rank([self.rows[i][:-1] for i in H])
    @lru_cache(None)
    def consumer_rank(self,H):
        return exact_rank([self.rows[i][:-1] for i in H],self.d)
    def charge(self,H,j):
        vals=sorted({self.values[j][i] for i in self.face(H)})
        need(vals,'empty target face')
        return vals,len(vals)-1


def select(D,u,v):
    target=D.active[v];G=tuple(sorted(D.active[u]&target));T=tuple(sorted(target-D.active[u]))
    cap=min(D.d,len(D.rows)-D.d)
    @lru_cache(None)
    def visit(chosen):
        H=tuple(sorted(set(G)|set(chosen)))
        if D.rank(H)==D.d:return (0,())
        if len(chosen)>=cap:return None
        choices=[]
        for j in T:
            if j in chosen:continue
            tail=visit(tuple(sorted((*chosen,j))))
            if tail is not None:
                choices.append((D.charge(H,j)[1]+tail[0],(j,)+tail[1]))
        return min(choices,key=lambda x:(x[0],len(x[1]),x[1])) if choices else None
    found=visit(())
    need(found is not None,'no eligible determining flag')
    return list(found[1]),found[0],G,T


def produce(D,u,v):
    J,budget,G,T=select(D,u,v); target=D.active[v];H=set(G);p=[u];phases=[];edges=[]
    for j in J:
        before_face=list(D.face(tuple(sorted(H))));vals,cost=D.charge(tuple(sorted(H)),j)
        lo=len(p)-1
        while j not in D.active[p[-1]]:
            x=p[-1];locked=D.active[x]&target
            F=frozenset(D.face(tuple(sorted(locked))))
            y,edge=g.improving_edge(D.model,F,x,D.rows[j][:-1])
            need(H<=D.active[y] and locked<=D.active[y],'lost original target equality')
            edges.append(dict(row=j,edge=edge));p.append(y)
            need(len(p)-1-lo<=cost,'local phase exceeded actual level count')
        phases.append(dict(row=j,entry_rows=sorted(H),face=before_face,
                           values=vals,charge=cost,start=lo,end=len(p)-1))
        H.add(j)
    need(p[-1]==v,'flag endpoint does not equal target')
    return dict(u=u,v=v,order=J,shared=list(G),missing=list(T),budget=budget,
                phases=phases,path=p,edges=edges)


def verify_optimal(D,u,v,J,budget):
    G=tuple(sorted(D.active[u]&D.active[v]));T=tuple(sorted(D.active[v]-D.active[u]))
    cap=min(D.d,len(D.rows)-D.d)
    need(len(J)==len(set(J)) and set(J)<=set(T) and len(J)<=cap,'illegal selected order')
    need(D.consumer_rank(tuple(sorted(set(G)|set(J))))==D.d,'not determining')
    valid=0;best_global=None;best_local=None
    # All eligible permutations, not just producer DP transitions or its output.
    for n in range(min(cap,len(T))+1):
        for R in permutations(T,n):
            if D.consumer_rank(tuple(sorted(set(G)|set(R))))!=D.d:continue
            H=set(G);local=0
            for j in R:
                face=[x for x,a in enumerate(D.active) if H<=a]
                local+=len({D.values[j][x] for x in face})-1;H.add(j)
            global_cost=sum(len(set(D.values[j]))-1 for j in R)
            need(budget<=local,'selected flag is not minimum local cost')
            best_global=global_cost if best_global is None else min(best_global,global_cost)
            best_local=local if best_local is None else min(best_local,local);valid+=1
    need(valid>0 and budget==best_local,'missing candidate or understated minimum')
    return valid,best_global


def consume(D,c):
    u=c['u'];v=c['v'];p=c['path'];J=c['order'];budget=c['budget']
    need(0<=u<len(D.V) and 0<=v<len(D.V),'invalid endpoints')
    G=D.active[u]&D.active[v];target=D.active[v];T=target-D.active[u]
    need(c['shared']==sorted(G) and c['missing']==sorted(T),'false original row binding')
    count,global_min=verify_optimal(D,u,v,J,budget)
    need(p and p[0]==u and p[-1]==v and all(0<=x<len(D.V) for x in p),'bad path')
    need(len(c['phases'])==len(J) and len(c['edges'])==len(p)-1,'record lengths')
    need(len(p)-1<=budget,'route exceeds local budget')
    H=set(G);cursor=0;sum_cost=0;long_phases=no_acquisition=0
    for j,phase in zip(J,c['phases']):
        F=[x for x,a in enumerate(D.active) if H<=a]
        vals=sorted({D.values[j][x] for x in F});cost=len(vals)-1
        need(phase['row']==j and phase['entry_rows']==sorted(H) and phase['face']==F,'false entry face')
        need(list(map(Q,phase['values']))==vals and phase['charge']==cost,'false conditional values')
        lo=phase['start'];hi=phase['end']
        need(lo==cursor and lo<=hi<len(p) and hi-lo<=cost,'phase partition or bound')
        need(j in D.active[p[hi]],'selected row not acquired')
        need(all(H<=D.active[p[t]] for t in range(lo,hi+1)),'left planned face')
        for t in range(lo,hi):
            x,y=p[t:t+2];r=c['edges'][t];e=r['edge']
            need(r['row']==j and D.values[j][x]<D.values[j][y],'nonincreasing phase')
            locked=D.active[x]&target;after=D.active[y]&target
            need(locked<=after,'target lock lost')
            need(e['u']==x and e['v']==y and set(e['face'])==set(D.face(tuple(sorted(locked)))),'wrong locked edge')
            need(tuple(map(Q,e['objective']))==D.rows[j][:-1],'wrong objective')
            g.verify_record(D.model,e);no_acquisition+=locked==after
        sum_cost+=cost;long_phases+=hi-lo>1;H.add(j);cursor=hi
    need(cursor==len(p)-1 and sum_cost==budget,'wrong total or uncovered edges')
    return dict(candidates=count,global_min=global_min,long_phases=long_phases,nonacquiring=no_acquisition)


def corruptions(D,c):
    edits=[('duplicate row',lambda x:x['order'].append(x['order'][0])),
      ('false cost',lambda x:x.update(budget=x['budget']+1)),
      ('missing face vertex',lambda x:x['phases'][0]['face'].pop()),
      ('missing local value',lambda x:x['phases'][0]['values'].pop()),
      ('wrong entry face',lambda x:x['phases'][0]['entry_rows'].append(x['order'][0])),
      ('wrong phase end',lambda x:x['phases'][0].update(end=-1)),
      ('stationary edge',lambda x:x['edges'][0]['edge'].update(v=x['path'][0])),
      ('wrong objective',lambda x:x['edges'][0]['edge'].update(objective=[0]*D.d)),
      ('wrong source',lambda x:x.update(u=x['v']))]
    results=[]
    for name,edit in edits:
        bad=deepcopy(c);edit(bad)
        try:consume(D,bad)
        except (ValueError,AssertionError):results.append(dict(case=name,rejected=True))
        else:raise AssertionError('accepted corruption '+name)
    return results


def models():
    cases=[(n,p) for n,p in g.models()]
    cases += [('moment4',[(i,i*i,i**3,i**4) for i in range(7)]),
      ('hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]),
      ('octahedron3',[tuple(s if i==j else 0 for i in range(3)) for j in range(3) for s in (-1,1)]),
      ('hexagonal_pyramid',[(x,y,0) for x,y in [(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]]+[(1,1,2)])]
    return cases


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--only',default='all')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);reports=[];fixtures=[];controls=[]
    for name,points in models():
        if a.only!='all' and a.only!=name:continue
        model=g.reference(points);rows=old.h_rows(model);D=OriginalData(model,rows)
        certs=[];totals=dict(routes=0,edges=0,shortest_edges=0,nonshortest=0,local_better_than_global_min=0,
                           candidate_orders=0,multi_edge_phases=0,nonacquiring_steps=0)
        for u in range(len(D.V)):
            distances=old.distances(model,u)
            for v in range(len(D.V)):
                c=produce(D,u,v);r=consume(D,c);certs.append(c);L=len(c['path'])-1
                totals['routes']+=1;totals['edges']+=L;totals['shortest_edges']+=distances[v]
                totals['nonshortest']+=L>distances[v]
                totals['local_better_than_global_min']+=c['budget']<r['global_min']
                totals['candidate_orders']+=r['candidates'];totals['multi_edge_phases']+=r['long_phases']
                totals['nonacquiring_steps']+=r['nonacquiring']
                if name=='hexagon' and L and not controls:controls=corruptions(D,c)
        frozen=json.loads(json.dumps(g.encoded(certs)))
        originals=(globals()['select'],globals()['produce'],g.improving_edge)
        def disabled(*args,**kwargs):raise RuntimeError('producer disabled')
        globals()['select']=globals()['produce']=g.improving_edge=disabled
        try:
            for c in frozen:consume(D,c)
        finally:globals()['select'],globals()['produce'],g.improving_edge=originals
        report=dict(name=name,dimension=D.d,vertices=len(D.V),original_rows=len(rows),**totals)
        reports.append(report);fixtures.append(dict(name=name,points=model['points'],rows=rows,certificates=frozen))
        print(json.dumps(report),flush=True)
    (a.out/'report.json').write_text(json.dumps(dict(kind='executed_exact_tests_not_Lean',models=reports),indent=2)+'\n')
    (a.out/'fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    (a.out/'negative-controls.json').write_text(json.dumps(dict(controls=controls),indent=2)+'\n')

if __name__=='__main__':main()
