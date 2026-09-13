#!/usr/bin/env python3
"""Find and independently check bounded-additive-spill portal repair trees.

A parent of excess e>b admits children of total excess <=e+b, each <=e.
Smaller excesses terminate using an explicit intrinsic-face edge walk.
The resulting bound is C*e+(1+b*C)*h*max(e-b,0), with C=1 for b<=3 and
C=2*2^(b-3) otherwise. These constants use the project's classical small-
excess / intrinsic Larman inputs, not a new unrestricted diameter oracle.
Enumeration is in the complete explicit vertex model, not polynomial in H-size.
"""
from __future__ import annotations
import argparse
from collections import deque
from functools import lru_cache
import json
from pathlib import Path

from portal_detour_optimizer import ExactSimplePolytope, NoCertificate, jsonable, require


def leaf_rate(b):
    require(type(b) is int and 1 <= b <= 12, 'allowance must be an integer in 1..12')
    return 1 if b <= 3 else 2*2**(b-3)


def polynomial_budget(b,h,e):
    C=leaf_rate(b)
    return C*e+(1+b*C)*h*max(e-b,0)


def face_shortest_route(P,start,end):
    F=P.carrier(start,end);parent={start:None};todo=deque([start])
    while todo and end not in parent:
        u=todo.popleft()
        for v in sorted(P.graph[u]&F['vertices']):
            if v not in parent:parent[v]=u;todo.append(v)
    require(end in parent,'face graph disconnected')
    out=[];v=end
    while v is not None:out.append(v);v=parent[v]
    return out[::-1]


class AllowanceSolver:
    def __init__(self,P,b=2):
        self.P=P;self.b=b;self.C=leaf_rate(b);self.cache={};self.states=0;self.transitions=0

    def solve(self,start,end,slack=1):
        require(type(slack) is int and 0 <= slack <= 12,'invalid detour slack')
        key=start,end,slack
        if key in self.cache:
            if self.cache[key] is None:raise NoCertificate('no admitted additive-allowance tree')
            return self.cache[key]
        P=self.P;F=P.carrier(start,end);h,e=F['dimension'],F['excess']
        if e<=self.b:
            route=face_shortest_route(P,start,end)
            require(len(route)-1<=self.C*e,'small-excess leaf exceeds its classical rate')
            result={'kind':'small','start':start,'end':end,'dimension':h,'excess':e,
                    'allowance':self.b,'cost':len(route)-1,'route':route}
            self.cache[key]=result
            return result
        _,available,G,targets,D=P.setup(start,end)
        INF=10**30
        @lru_cache(None)
        def child(x,y):
            require(P.carrier(x,y)['dimension']<h,'nondecreasing geometric recursion')
            require(P.carrier(x,y)['excess']<=e,'child excess is not parent-monotone')
            try:return self.solve(x,y,slack)['cost']
            except NoCertificate:return INF
        @lru_cache(None)
        def dp(left,row,entry,remaining):
            self.states+=1
            if row not in D or D[row]+1>left:return INF,()
            best=INF,()
            terminal_mass=P.carrier(entry,end)['excess']
            if row in targets and terminal_mass<=remaining:
                value=child(entry,end)
                if value<INF:best=value,((row,entry,end),)
            if left>1:
                for nxt in sorted(G[row]):
                    if nxt not in D or D[nxt]+1>left-1:continue
                    for portal in sorted(F['regions'][row]&F['regions'][nxt]):
                        mass=P.carrier(entry,portal)['excess']
                        if mass>remaining:continue
                        value=child(entry,portal)
                        if value>=INF:continue
                        self.transitions+=1
                        tail_value,tail=dp(left-1,nxt,portal,remaining-mass)
                        candidate=value+tail_value,((row,entry,portal),)+tail
                        if (candidate[0],len(candidate[1]),candidate[1]) < \
                           (best[0],len(best[1]),best[1]):best=candidate
            return best
        best=None
        for old in sorted(P.graph[start]&F['vertices']):
            first=next(iter((P.active[old]-P.active[start])&available))
            if first not in D:continue
            value,legs=dp(D[first]+1+slack,first,old,e+self.b)
            candidate=value,len(legs),old,legs
            if best is None or candidate<best:best=candidate
        if best is None or best[0]>=INF:
            self.cache[key]=None
            raise NoCertificate('no admitted additive-allowance tree')
        plan={'old_vertex':best[2],'legs':[list(x)for x in best[3]],'slack_limit':slack,
              'objective':'recursive','objective_value':best[0],'policy':'additive_allowance'}
        metrics=P.verify_plan(start,end,plan)
        require(metrics['carrier_mass']<=e+self.b,'sibling budget violated')
        children=[self.solve(x,y,slack)for _,x,y in plan['legs']]
        result={'kind':'node','start':start,'end':end,'dimension':h,'excess':e,
                'allowance':self.b,'cost':1+sum(c['cost']for c in children),
                'plan':plan,'children':children}
        self.cache[key]=result
        return result


def verify_allowance(P,start,end,cert,b):
    """No discovery, DP, or leaf path search. Rechecks all supplied witnesses."""
    C=leaf_rate(b);F=P.carrier(start,end);h,e=F['dimension'],F['excess']
    for key,value in [('start',start),('end',end),('dimension',h),('excess',e),('allowance',b)]:
        require(type(cert[key])is int and cert[key]==value,'false '+key)
    if cert['kind']=='small':
        require(e<=b,'high-excess carrier mislabeled as a small leaf')
        route=cert['route']
        require(isinstance(route,list) and route and all(type(v)is int and v in F['vertices']for v in route),
                'leaf route leaves its intrinsic face')
        require(route[0]==start and route[-1]==end,'leaf endpoints changed')
        require(all(v in P.graph[u]for u,v in zip(route,route[1:])),'leaf contains a non-edge')
        cost=len(route)-1
        require(cost<=C*e,'small leaf rate failed')
        nodes=0;leaf_mass=e;leaves=1
    else:
        require(cert['kind']=='node' and e>b and h>0,'invalid internal-node regime')
        plan=cert['plan'];metrics=P.verify_plan(start,end,plan)
        require(metrics['carrier_mass']<=e+b,'additive sibling budget failed')
        children=cert['children'];legs=plan['legs']
        require(len(children)==len(legs),'missing child occurrence')
        route=[start,plan['old_vertex']];cost=nodes=1;leaf_mass=0;leaves=0;shifted=0
        for (_,x,y),child in zip(legs,children):
            G=P.carrier(x,y)
            require(G['excess']<=e and G['dimension']<h,'nonmonotone child')
            shifted+=max(G['excess']-b,0)
            got=verify_allowance(P,x,y,child,b)
            require(route[-1]==got['route'][0],'broken child chain')
            route+=got['route'][1:];cost+=got['cost'];nodes+=got['internal_nodes']
            leaf_mass+=got['leaf_mass'];leaves+=got['leaves']
        require(shifted<=e-b,'shifted large-child mass is not conserved')
        require(plan['objective_value']==cost-1,'forged recursive cost objective')
    require(type(cert['cost'])is int and cert['cost']==cost,'forged total cost')
    require(len(route)-1==cost and all(v in P.graph[u]for u,v in zip(route,route[1:])),
            'assembled walk is not an ordinary-edge route')
    require(cost<=polynomial_budget(b,h,e),'additive-spill polynomial bound failed')
    require(nodes<=h*max(e-b,0),'large-node count bound failed')
    require(leaf_mass<=e+b*nodes,'global leaf mass telescoping failed')
    return {'route':route,'cost':cost,'internal_nodes':nodes,'leaves':leaves,'leaf_mass':leaf_mass,
            'allowance':b,'leaf_rate':C,'dimension':h,'excess':e,
            'polynomial_bound':polynomial_budget(b,h,e)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path);parser.add_argument('--allowance',type=int,default=2)
    parser.add_argument('--slack',type=int,default=1);parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        data=json.loads(args.input.read_text());P=ExactSimplePolytope(data);s,t=P.endpoints(data)
        solver=AllowanceSolver(P,args.allowance);cert=solver.solve(s,t,args.slack)
        result={'certificate':cert,'verified':verify_allowance(P,s,t,cert,args.allowance),
                'complete_vertex_count':P.N,'dp_states':solver.states,
                'scope':'Exact finite certificate, not Lean or platform acceptance.'}
        text=json.dumps(jsonable(result),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError)as exc:
        parser.exit(2,f'Certificate not produced: {exc}\n')


if __name__=='__main__':main()
