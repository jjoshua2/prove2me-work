#!/usr/bin/env python3
"""Exact nested face routing and cross-level neutral-facet accounting.

This is an exponential finite research oracle, NOT a polynomial algorithm.
All vertices are enumerated from rational H-rows; boundedness, strict interior,
facet irredundancy and simplicity are checked. The router never uses ambient
vertex-graph distances. Those are computed separately only in the test suite.

Modes: 'lex' freezes first geodesic and portals; 'local' minimizes immediate
child dimension mass; 'recursive' optimizes all descendant costs over all
metric-shortest facet paths; 'relaxed' allows one extra region edge at every
node. A separate verifier rechecks every tree node with its declared slack.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
import json
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok: raise ValueError(message)


def rational(x: Any) -> Q:
    require(type(x) in (int, str) or isinstance(x, Q), 'use integers/rational strings, not floats or booleans')
    return Q(x)


def dot(a, b): return sum((x*y for x,y in zip(a,b)), Q(0))


def rank(rows):
    a = [list(row) for row in rows]
    if not a: return 0
    k = 0
    for j in range(len(a[0])):
        p = next((i for i in range(k,len(a)) if a[i][j]), None)
        if p is None: continue
        a[k],a[p] = a[p],a[k]
        v=a[k][j]; a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v: a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return k


def solve(rows, rhs):
    n=len(rows); a=[list(row)+[b] for row,b in zip(rows,rhs)]
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None: return None
        a[j], a[p] = a[p], a[j]
        v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return tuple(row[-1] for row in a)


def distances(g, start):
    out={start:0};todo=deque([start])
    while todo:
        v=todo.popleft()
        for w in sorted(g[v]):
            if w not in out:out[w]=out[v]+1;todo.append(w)
    return out


class Model:
    """Validated irredundant, bounded, full-dimensional SIMPLE H-polytope."""
    def __init__(self, data):
        self.A=[[rational(x) for x in row] for row in data['A']]
        self.b=[rational(x) for x in data['b']]
        require(bool(self.A) and bool(self.A[0]),'positive dimension required')
        self.d=len(self.A[0]);self.n=len(self.A)
        require(len(self.b)==self.n and all(len(row)==self.d for row in self.A),'row shape')
        o=[rational(x) for x in data['interior']]
        lam=[rational(x) for x in data['positive_balance']]
        require(len(o)==self.d and all(dot(a,o)<b for a,b in zip(self.A,self.b)),'strict interior failed')
        require(len(lam)==self.n and all(x>0 for x in lam),'strictly positive balance required')
        require(rank(self.A)==self.d,'normals must span')
        require(all(sum((lam[i]*self.A[i][j] for i in range(self.n)),Q(0))==0 for j in range(self.d)),
                'normal balance failed')
        # Positive balance + full rank excludes every nonzero recession direction.
        vertices=set()
        for ids in combinations(range(self.n),self.d):
            x=solve([self.A[i] for i in ids],[self.b[i] for i in ids])
            if x is not None and all(dot(a,x)<=b for a,b in zip(self.A,self.b)):vertices.add(x)
        require(bool(vertices),'no vertices')
        self.vertices=sorted(vertices)
        self.active=[frozenset(i for i,(a,b) in enumerate(zip(self.A,self.b)) if dot(a,x)==b)
                     for x in self.vertices]
        require(all(len(s)==self.d for s in self.active),'nonsimple or redundant active presentation')
        for j in range(self.n):
            pts=[x for x,s in zip(self.vertices,self.active) if j in s]
            require(bool(pts) and rank([[x-y for x,y in zip(p,pts[0])] for p in pts[1:]])==self.d-1,
                    'every original row must define a genuine distinct facet')
        self.graph=[set() for _ in self.vertices]
        for u,v in combinations(range(len(self.vertices)),2):
            if len(self.active[u]&self.active[v])==self.d-1:
                self.graph[u].add(v);self.graph[v].add(u)
        self.stats=Counter()
        self._cache={}

    def dim(self,u,v): return self.d-len(self.active[u]&self.active[v])

    @lru_cache(None)
    def face(self,u,v):
        common=self.active[u]&self.active[v]
        pts=frozenset(i for i,s in enumerate(self.active) if common<=s)
        h=self.dim(u,v)
        facets={j:frozenset(i for i in pts if j in self.active[i]) for j in range(self.n) if j not in common}
        facets={j:fs for j,fs in facets.items() if fs}
        require(all(len((self.active[i]-common))==h for i in pts),'intrinsic simple incidence failed')
        return common,pts,facets

    def regions(self,u,v):
        common,pts,facets=self.face(u,v)
        regions={-1:frozenset([u]),**facets,-2:frozenset([v])}
        g={j:set() for j in regions}
        for j,k in combinations(regions,2):
            if regions[j]&regions[k]:g[j].add(k);g[k].add(j)
        ds=distances(g,-1);dt=distances(g,-2)
        require(-2 in ds,'disconnected facet regions')
        return regions,g,ds,dt

    def route(self,u,v,mode='recursive'):
        require(mode in ('lex','local','recursive','relaxed'),'unknown mode')
        require(type(u) is int and type(v) is int and 0<=u<len(self.vertices) and 0<=v<len(self.vertices),'invalid endpoints')
        key=(u,v,mode)
        if key in self._cache:return self._cache[key]
        self.stats[mode+'_subproblems']+=1
        h=self.dim(u,v)
        if h<=1:
            tree={'u':u,'v':v,'dimension':h,'neutral_rows':[], 'labels':[], 'portals':[u] if u==v else [u,v], 'children':[]}
        else:
            regions,g,ds,dt=self.regions(u,v);L=ds[-2]
            nexts={j:[k for k in sorted(g[j]) if ds.get(k)==ds[j]+1 and ds[k]+dt[k]==L]
                   for j in regions if j in ds and j in dt and ds[j]+dt[j]==L}
            if mode=='relaxed':
                @lru_cache(None)
                def relaxed_dp(j,entry,left):
                    best=None
                    for k in sorted(g[j]):
                        if k==-1 or dt.get(k,left+1)>left-1:continue
                        if (k==-2)!=(left==1):continue
                        for z in sorted(regions[j]&regions[k]):
                            self.stats['relaxed_portal_candidates']+=1
                            require(self.dim(entry,z)<h,'nonproper recursive carrier')
                            c=self.route(entry,z,mode)['length']
                            if k==-2:cand=(c,(j,-2),(entry,z))
                            else:
                                rest=relaxed_dp(k,z,left-1)
                                if rest is None:continue
                                score,labs,ps=rest;cand=(c+score,(j,)+labs,(entry,)+ps)
                            if best is None or cand<best:best=cand
                    return best
                candidates=[]
                for extra in (0,1):
                    for j in sorted(g[-1]):
                        if j==-2:continue
                        cand=relaxed_dp(j,u,L+extra-1)
                        if cand is not None:candidates.append(cand)
                require(bool(candidates),'no relaxed continuation')
                _,tail,ps=min(candidates);labels=[-1,*tail];portals=list(ps)
            elif mode=='lex':
                labels=[-1]
                while labels[-1]!=-2:labels.append(nexts[labels[-1]][0])
                portals=[min(regions[j]&regions[k]) for j,k in zip(labels,labels[1:])]
            else:
                @lru_cache(None)
                def dp(j,entry):
                    best=None
                    for k in nexts[j]:
                        for z in sorted(regions[j]&regions[k]):
                            self.stats[mode+'_portal_candidates']+=1
                            localdim=self.dim(entry,z)
                            require(localdim<h,'nonproper recursive carrier')
                            localcost=localdim if mode=='local' else self.route(entry,z,mode)['length']
                            if k==-2:
                                score=localcost;labs=(j,-2);verts=(entry,z)
                            else:
                                rest,tail,ps=dp(k,z)
                                score=localcost+rest;labs=(j,)+tail;verts=(entry,)+ps
                            candidate=(score,labs,verts)
                            if best is None or candidate<best:best=candidate
                    require(best is not None,'no layered continuation')
                    return best
                best=min(dp(j,u) for j in nexts[-1])
                _,tail,ps=best;labels=[-1,*tail];portals=list(ps)
            require(portals[0]==u and portals[-1]==v,'portal endpoints')
            children=[self.route(x,y,mode)['tree'] for x,y in zip(portals,portals[1:])]
            neutral=sorted(set().union(*(self.active[p] for p in portals))-(self.active[u]|self.active[v]))
            tree={'u':u,'v':v,'dimension':h,'neutral_rows':neutral,'labels':labels,
                  'portals':portals,'children':children}
        result=verify_tree(self,tree,u,v,max_slack=1 if mode=='relaxed' else 0)
        result['tree']=tree
        self._cache[key]=result
        return result


def verify_tree(model,tree,expected_u=None,expected_v=None,max_slack=0):
    """No discovery, optimization, or alleged lengths are trusted here."""
    require(type(max_slack) is int and 0<=max_slack<=1,'unsupported slack limit')
    u=tree['u'];v=tree['v']
    require(type(u) is int and type(v) is int and 0<=u<len(model.vertices) and 0<=v<len(model.vertices),'bad tree endpoint')
    if expected_u is not None:require(u==expected_u,'changed source')
    if expected_v is not None:require(v==expected_v,'changed destination')
    h=model.dim(u,v);require(tree['dimension']==h,'false intrinsic dimension')
    require(type(tree['dimension']) is int,'integer dimension required')
    portals=tree['portals'];labels=tree['labels'];children=tree['children']
    if h<=1:
        require(not children and not labels and tree['neutral_rows']==[],'invalid leaf')
        require(portals==([u] if u==v else [u,v]),'false leaf route')
        if h==1:require(v in model.graph[u],'leaf is not ordinary edge')
        return {'route':portals,'length':h,'debt':0,'row_charges':{},'internal_nodes':0,'max_depth':0,
                'dimension_mass':h,'local_debt':0}
    require(len(portals)>=2 and portals[0]==u and portals[-1]==v,'invalid portal chain')
    require(all(type(p) is int and 0<=p<len(model.vertices) for p in portals),'invalid portal vertex')
    require(len(children)==len(portals)-1 and len(labels)==len(portals)+1,'tree shape')
    regions,g,ds,dt=model.regions(u,v)
    require(labels[0]==-1 and labels[-1]==-2 and all(j in regions for j in labels),'invalid region labels')
    require(len(labels)==len(set(labels)) and all(k in g[j] for j,k in zip(labels,labels[1:])),'invalid region walk')
    slack=len(labels)-1-ds[-2]
    require(type(max_slack) is int and 0<=max_slack<=1,'unsupported slack limit')
    require(0<=slack<=max_slack,'facet path exceeds the declared slack limit')
    for i,p in enumerate(portals):require(p in regions[labels[i]]&regions[labels[i+1]],'invalid shared portal')
    common,pts,facets=model.face(u,v)
    for j in facets:
        positions=[i for i,p in enumerate(portals) if j in model.active[p]]
        require(not positions or max(positions)-min(positions)<=slack+1,'portal locality violated')
    neutral=sorted(set().union(*(model.active[p] for p in portals))-(model.active[u]|model.active[v]))
    require(tree['neutral_rows']==neutral,'false neutral-facet charge')
    mass=sum(model.dim(x,y) for x,y in zip(portals,portals[1:]))
    local=Counter()
    for j in range(model.n):
        bits=[int(j in model.active[p]) for p in portals]
        transitions=sum(x!=y for x,y in zip(bits,bits[1:]))
        local[j]=(transitions-abs(bits[0]-bits[-1]))//2
    require(mass==h+sum(local.values()),'exact dimension conservation failed')
    if slack==0:
        require(+local==Counter(neutral),'geodesic has non-neutral or repeated local charges')
        require(mass<=len(facets)-h,'single-node excess budget failed')
    route=[];charges=+local;debt=sum(local.values());nodes=1;depth=0
    for child,x,y in zip(children,portals,portals[1:]):
        require(model.dim(x,y)<h,'child carrier must be proper')
        res=verify_tree(model,child,x,y,max_slack=max_slack)
        require(all(p in pts for p in res['route']),'child left parent face')
        route+=res['route'] if not route else res['route'][1:]
        charges.update({int(j):c for j,c in res['row_charges'].items()})
        debt+=res['debt'];nodes+=res['internal_nodes'];depth=max(depth,res['max_depth']+1)
    length=len(route)-1
    require(length==h+debt,'cross-level length/debt identity failed')
    require(all(y in model.graph[x] for x,y in zip(route,route[1:])),'assembled step is not an ordinary edge')
    # Stronger row-by-row identity: each charge is one extra on/off cycle.
    for j in range(model.n):
        bits=[int(j in model.active[p]) for p in route]
        toggles=sum(x!=y for x,y in zip(bits,bits[1:]))
        boundary=abs(bits[0]-bits[-1])
        require(toggles==boundary+2*charges[j],'rowwise excursion identity failed')
    return {'route':route,'length':length,'debt':debt,'row_charges':dict(sorted(charges.items())),
            'internal_nodes':nodes,'max_depth':depth,'dimension_mass':mass,'local_debt':sum(local.values()),'facet_slack':slack,'local_charges':dict(+local)}


def jsonable(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):jsonable(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [jsonable(v) for v in x]
    return x


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path);ap.add_argument('--source',type=int,default=0)
    ap.add_argument('--target',type=int,required=True);ap.add_argument('--mode',choices=['lex','local','recursive','relaxed'],default='recursive')
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    try:
        model=Model(json.loads(args.input.read_text()))
        result=model.route(args.source,args.target,args.mode)
        out={'scope':'Exact finite simple-polytope route certificate; exponential research oracle, not a Lean verdict.',
             'vertices':model.vertices,'slack_limit':int(args.mode=='relaxed'),'result':result,'statistics':dict(model.stats)}
        text=json.dumps(jsonable(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,OSError) as exc:ap.exit(2,f'Certificate rejected: {exc}\n')

if __name__=='__main__':main()
