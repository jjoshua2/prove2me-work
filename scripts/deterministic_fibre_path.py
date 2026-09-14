#!/usr/bin/env python3
"""Exact deterministic fibre paths in a finite Minkowski presentation.

A fixed core vertex and two strict exposing objectives are input. Finite root
avoidance replaces probabilistic genericity. Independent verification checks
whole component support faces, not merely two tied points. No product-point
sets are enumerated by construct/verify. This is not Lean-extracted code.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
from typing import Any, Sequence

Point=tuple[F,...]
def need(p: bool,msg: str)->None:
    if not p: raise ValueError(msg)
def point(x: Sequence[Any])->Point:
    need(all(isinstance(a,(F,int,str)) and not isinstance(a,bool) for a in x),'inexact coordinate')
    return tuple(F(a) for a in x)
def add(x:Point,y:Point)->Point:
    need(len(x)==len(y),'dimension mismatch');return tuple(a+b for a,b in zip(x,y))
def sub(x:Point,y:Point)->Point:
    need(len(x)==len(y),'dimension mismatch');return tuple(a-b for a,b in zip(x,y))
def scale(a:F,x:Point)->Point:return tuple(a*b for b in x)
def dot(x:Point,y:Point)->F:
    need(len(x)==len(y),'dimension mismatch');return sum((a*b for a,b in zip(x,y)),F(0))
def total(xs:Sequence[Point],n:int)->Point:
    return tuple(sum((x[j] for x in xs),F(0)) for j in range(n))
def encode(v:Any)->Any:
    if isinstance(v,F):return str(v)
    if isinstance(v,dict):return {k:encode(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)):return [encode(x) for x in v]
    return v
def direction(x:Point)->Point:
    a=next((v for v in x if v),None)
    need(a is not None,'zero direction');return scale(1/a,x)
def coeff(x:Point,e:Point)->F|None:
    j=next((j for j,a in enumerate(e) if a),None);need(j is not None,'zero edge')
    a=x[j]/e[j];return a if scale(a,e)==x else None
def on_segment(x:Point,a:Point,b:Point)->bool:
    if a==b:return x==a
    t=coeff(sub(x,a),sub(b,a));return t is not None and 0<=t<=1
def unique_pick(s:Sequence[Point],f:Point)->int:
    vals=[dot(f,x) for x in s];mx=max(vals);active=[i for i,v in enumerate(vals) if v==mx]
    need(all(s[i]==s[active[0]] for i in active),'nonunique geometric maximizer')
    return active[0]

@dataclass(frozen=True)
class Model:
    core:tuple[Point,...]
    fixed:Point
    factors:tuple[tuple[Point,...],...]
    first:Point
    last:Point
    @property
    def dim(self)->int:return len(self.fixed)
    def data(self)->dict:return encode(dict(core=self.core,fixed=self.fixed,factors=self.factors,
                                            first=self.first,last=self.last))
    def digest(self)->str:
        return hashlib.sha256(json.dumps(self.data(),sort_keys=True,separators=(',',':')).encode()).hexdigest()
    @staticmethod
    def read(d:dict)->Model:
        return Model(tuple(point(x) for x in d['core']),point(d['fixed']),
                     tuple(tuple(point(x) for x in s) for s in d['factors']),point(d['first']),point(d['last']))
    def validate(self)->tuple[tuple[int,...],tuple[int,...]]:
        need(self.dim>0 and self.core and self.fixed in self.core,'invalid fixed core vertex')
        need(all(self.factors),'empty summand')
        pts=(*self.core,self.fixed,self.first,self.last,*(x for s in self.factors for x in s))
        need(all(len(x)==self.dim and all(isinstance(a,F) for a in x) for x in pts),'inexact/wrong dimension')
        picks=[]
        for f in (self.first,self.last):
            need(all(x==self.fixed or dot(f,sub(x,self.fixed))<0 for x in self.core),'core vertex not strictly exposed')
            picks.append(tuple(unique_pick(s,f) for s in self.factors))
        return tuple(picks)

def deduplicate_directions(vectors:Sequence[Point])->list[Point]:
    return list(dict.fromkeys(direction(x) for x in vectors if any(x)))

def avoid(base:Point,strict:Sequence[Point],forms:Sequence[Point])->tuple[Point,dict]:
    """Finite polynomial-root avoidance, preserving a strict negative cone."""
    n=len(base);need(all(dot(base,c)<0 for c in strict),'strict cone input failed')
    forms=deduplicate_directions(forms)
    bound=len(forms)*max(n-1,0)+1
    chosen=None
    for k in range(bound):
        h=tuple(F(k**j) for j in range(n))
        if all(dot(h,v)!=0 for v in forms):chosen=k;break
    need(chosen is not None,'nonzero polynomial root bound failed')
    comparisons=(*strict,*forms)
    epsilon=min([F(1)]+[abs(dot(base,c))/(2*(abs(dot(h,c))+1)) for c in comparisons if dot(base,c)])
    ans=add(base,scale(epsilon,h))
    need(all(dot(ans,c)<0 for c in strict),'strict endpoint cone changed')
    need(all(dot(ans,c)!=0 for c in forms),'forbidden hyperplane hit')
    return ans,dict(parameter=chosen,trials=chosen+1,trial_bound=bound,forms=len(forms),epsilon=epsilon,direction=h)

def construct(model:Model)->dict:
    start,end=model.validate();n=model.dim
    ds=deduplicate_directions([sub(x,y) for s in model.factors for x,y in itertools.combinations(s,2)])
    def constraints(picks):
        return [sub(x,model.fixed) for x in model.core if x!=model.fixed]+[
            sub(x,s[p]) for s,p in zip(model.factors,picks) for x in s if x!=s[p]]
    f,firstlog=avoid(model.first,constraints(start),ds)
    obstructions=[sub(scale(dot(f,d),e),scale(dot(f,e),d)) for d,e in itertools.combinations(ds,2)]
    need(all(any(w) for w in obstructions),'distinct direction classes became dependent')
    g,lastlog=avoid(model.last,constraints(end),[*ds,*obstructions])
    # Construct upper envelopes independently in each factor. M pair times,
    # not a Cartesian product of all factor states.
    roots=set()
    for s in model.factors:
        for x,y in itertools.combinations(s,2):
            d=sub(x,y)
            a,b=dot(f,d),dot(g,d)
            if a!=b:
                t=a/(a-b)
                if 0<t<1:roots.add(t)
    roots=sorted(roots);bounds=[F(0),*roots,F(1)]
    picks=[tuple(unique_pick(s,add(scale(1-t,f),scale(t,g))) for s in model.factors)
           for t in ((a+b)/2 for a,b in zip(bounds,bounds[1:]))]
    nodes=[picks[0]];edges=[]
    for j,t in enumerate(roots):
        before,after=nodes[-1],picks[j+1]
        if all(s[a]==s[b] for s,a,b in zip(model.factors,before,after)):continue
        normal=add(scale(1-t,f),scale(t,g))
        left=add(model.fixed,total([s[a] for s,a in zip(model.factors,before)],n))
        right=add(model.fixed,total([s[a] for s,a in zip(model.factors,after)],n))
        e=sub(right,left);need(any(e),'cancelling factor transition')
        factors=[]
        for s,a,b in zip(model.factors,before,after):
            eta=coeff(sub(s[b],s[a]),e);need(eta is not None and eta>=0,'oppositely oriented tie')
            factors.append(dict(lo=a,hi=b,eta=eta,support=dot(normal,s[a])))
        edges.append(dict(time=t,normal=normal,left=left,right=right,factors=factors,
                          support=dot(normal,model.fixed)+sum((q['support'] for q in factors),F(0))))
        nodes.append(after)
    data=dict(model_sha256=model.digest(),first=f,last=g,first_search=firstlog,last_search=lastlog,
              difference_directions=len(ds),pair_obstructions=len(obstructions),
              candidate_crossing_times=len(roots),nodes=nodes,edges=edges,
              factor_budget=sum(len(set(s))-1 for s in model.factors))
    verify(model,data)
    return data

def verify(model:Model,data:dict)->dict:
    """Independent full-face path verification; no genericity search rerun."""
    start,end=model.validate();need(data['model_sha256']==model.digest(),'input hash mismatch')
    f,g=point(data['first']),point(data['last']);need(len(f)==len(g)==model.dim,'wrong objective dimension')
    nodes=data['nodes'];edges=data['edges'];need(len(nodes)==len(edges)+1,'bad route length')
    times=[F(e['time']) for e in edges];need(all(0<t<1 for t in times),'crossing outside interval')
    need(all(a<b for a,b in zip(times,times[1:])),'crossing times not increasing')
    nodepoints=[];ranks=[];bounds=[F(0),*times,F(1)]
    slopes=[{x:dot(sub(g,f),x) for x in s} for s in model.factors]
    for idx,row in enumerate(nodes):
        need(len(row)==len(model.factors),'missing factor state')
        need(all(isinstance(i,int) and not isinstance(i,bool) and 0<=i<len(s) for s,i in zip(model.factors,row)),
             'bad state index')
        t=(bounds[idx]+bounds[idx+1])/2;normal=add(scale(1-t,f),scale(t,g))
        need(all(x==model.fixed or dot(normal,sub(x,model.fixed))<0 for x in model.core),'path left core fibre')
        for s,i in zip(model.factors,row):
            need(s[unique_pick(s,normal)]==s[i],'state not the interval maximizer')
        nodepoints.append(add(model.fixed,total([s[i] for s,i in zip(model.factors,row)],model.dim)))
        ranks.append(tuple(sorted(set(v.values())).index(v[s[i]]) for s,i,v in zip(model.factors,row,slopes)))
    for endpoint,requested,chosen in ((f,start,nodes[0]),(g,end,nodes[-1])):
        need(all(x==model.fixed or dot(endpoint,sub(x,model.fixed))<0 for x in model.core),'endpoint left core cone')
        for s,p,i in zip(model.factors,requested,chosen):
            need(s[unique_pick(s,endpoint)]==s[p]==s[i],'requested endpoint changed')
    comparisons=0;parallel_switches=0
    for idx,record in enumerate(edges):
        t=times[idx];normal=add(scale(1-t,f),scale(t,g))
        need(point(record['normal'])==normal,'wrong crossing normal')
        left,right=nodepoints[idx],nodepoints[idx+1];e=sub(right,left);need(any(e),'stationary step recorded as edge')
        need(point(record['left'])==left and point(record['right'])==right,'disconnected edge endpoints')
        need(all(x==model.fixed or dot(normal,sub(x,model.fixed))<0 for x in model.core),'crossing loses core vertex')
        need(len(record['factors'])==len(model.factors),'missing factor support certificate')
        supports=[];etas=[];changes=0
        for s,i,j,c in zip(model.factors,nodes[idx],nodes[idx+1],record['factors']):
            need(c['lo']==i and c['hi']==j,'support slice endpoints mismatch')
            eta=F(c['eta']);beta=F(c['support']);need(eta>=0,'negative parallel length')
            need(sub(s[j],s[i])==scale(eta,e),'nonparallel simultaneous face')
            need(dot(normal,s[i])==dot(normal,s[j])==beta,'untied support endpoints')
            for x in s:
                val=dot(normal,x);need(val<=beta,'omitted dominating point')
                need(val!=beta or on_segment(x,s[i],s[j]),'higher-dimensional/omitted support face')
                comparisons+=1
            etas.append(eta);supports.append(beta);changes+=int(s[i]!=s[j])
        need(sum(etas,F(0))==1,'wrong summed segment length')
        need(F(record['support'])==dot(normal,model.fixed)+sum(supports,F(0)),'wrong full support value')
        need(all(a<=b for a,b in zip(ranks[idx],ranks[idx+1])) and sum(ranks[idx])<sum(ranks[idx+1]),
             'affine slope potential did not increase')
        if changes>1:parallel_switches+=1
    budget=sum(len(set(s))-1 for s in model.factors)
    need(data['factor_budget']==budget,'wrong factor budget')
    need(len(edges)<=sum(ranks[-1])-sum(ranks[0])<=budget,'additive budget failed')
    return dict(edges=len(edges),factor_budget=budget,full_face_comparisons=comparisons,
                simultaneous_parallel_switches=parallel_switches,requested_endpoints_preserved=True)

def exhaustive(model:Model,data:dict,cap:int=100000)->dict:
    from math import prod
    number=prod([len(model.core),*(len(s) for s in model.factors)])
    need(number<=cap,'product audit cap exceeded')
    comparisons=0
    for record in data['edges']:
        normal=point(record['normal']);beta=F(record['support'])
        left,right=point(record['left']),point(record['right']);lo=hi=False
        for choices in itertools.product(model.core,*model.factors):
            x=total(choices,model.dim);val=dot(normal,x)
            need(val<=beta,'global support violation')
            if val==beta:
                need(choices[0]==model.fixed,'exposed global face left fibre')
                need(on_segment(x,left,right),'global maximizing face exceeds segment')
            lo |= x==left;hi |= x==right;comparisons+=1
        need(lo and hi,'endpoints absent from point sum')
    return dict(point_tuples=number,edge_tuple_comparisons=comparisons)

def main()->None:
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);ap.add_argument('--out',type=Path);args=ap.parse_args()
    model=Model.read(json.loads(args.input.read_text()))
    result=verify(model,json.loads(args.certificate.read_text())) if args.certificate else encode(construct(model))
    text=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(text)
    else:print(text,end='')
if __name__=='__main__':main()
