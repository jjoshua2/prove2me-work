#!/usr/bin/env python3
"""Exact H-description routes for x_head-x_tail<=bound, x_0=0.

Constructive specialization of the classical dual-network-flow pivot method.
Degenerate bases are handled by explicit zero-length tree exchanges; no RHS
perturbation, vertex enumeration or graph-distance oracle is used by the router.
The independent checker validates every tree, cut, ratio, lock, and actual edge.
The input defines its whole polyhedron; no Minkowski decomposition is required.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok: raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int,str) or isinstance(x,Q), 'exact integers/rational strings required')
    return Q(x)


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [serial(v) for v in x]
    return x


class UnionFind:
    def __init__(self,n): self.p=list(range(n))
    def root(self,i):
        while self.p[i]!=i:
            self.p[i]=self.p[self.p[i]]; i=self.p[i]
        return i
    def join(self,i,j):
        i,j=self.root(i),self.root(j)
        if i==j:return False
        self.p[max(i,j)]=min(i,j); return True
    def labels(self):return [self.root(i) for i in range(len(self.p))]


class Network:
    def __init__(self,data):
        n=data['nodes']; require(type(n)is int and n>=1,'nodes must be a positive integer')
        self.n=n; self.arcs=[]
        for arc in data['arcs']:
            require(isinstance(arc,(tuple,list)) and len(arc)==3,'arc shape')
            a,b,c=arc
            require(type(a)is int and type(b)is int and 0<=a<n and 0<=b<n and a!=b,'invalid arc endpoints')
            self.arcs.append((a,b,rat(c)))
        self.m=len(self.arcs)
        self.start=self.point(data['source']);self.target=self.point(data['target'])
        require(self.start[0]==self.target[0]==0,'node zero must be fixed at zero')
        self.check_point(self.start);self.check_point(self.target)
        self.tree(self.active(self.start));self.tree(self.active(self.target))
        normalized={'nodes':n,'arcs':self.arcs,'source':self.start,'target':self.target}
        self.digest=hashlib.sha256(json.dumps(serial(normalized),sort_keys=True,separators=(',',':')).encode()).hexdigest()
    def point(self,x):
        require(isinstance(x,(tuple,list)) and len(x)==self.n,'point dimension')
        return tuple(map(rat,x))
    def check_point(self,x):
        require(len(x)==self.n and x[0]==0,'invalid gauged point')
        require(all(x[b]-x[a]<=c for a,b,c in self.arcs),'infeasible point')
    def active(self,x):return {i for i,(a,b,c) in enumerate(self.arcs) if x[b]-x[a]==c}
    def labels(self,edges):
        u=UnionFind(self.n)
        for i in edges:
            a,b,_=self.arcs[i];u.join(a,b)
        return u.labels()
    def tree(self,allowed,mandatory=()):
        require(all(type(i)is int and 0<=i<self.m for i in allowed),'invalid allowed arc')
        u=UnionFind(self.n);out=[]
        for i in mandatory:
            require(i in allowed,'mandatory tree edge unavailable')
            a,b,_=self.arcs[i];require(u.join(a,b),'mandatory edges contain a cycle');out.append(i)
        for i in sorted(set(allowed)-set(out)):
            a,b,_=self.arcs[i]
            if u.join(a,b):out.append(i)
        require(len(out)==self.n-1,'tight graph is not connected: not a vertex')
        return set(out)
    def check_tree(self,tree,x):
        require(isinstance(tree,(list,set,tuple)) and len(tree)==self.n-1,'wrong tree size')
        require(len(tree)==len(set(tree)),'duplicate tree edge')
        require(set(tree)<=self.active(x),'tree contains slack edge')
        self.tree(set(tree),list(tree))
    def path(self,tree,r,s):
        adj=[[]for _ in range(self.n)]
        for i in tree:
            a,b,_=self.arcs[i];adj[a].append((b,i));adj[b].append((a,i))
        prev={r:None};q=deque([r])
        while q and s not in prev:
            a=q.popleft()
            for b,i in sorted(adj[a]):
                if b not in prev:prev[b]=(a,i);q.append(b)
        require(s in prev,'tree path disconnected')
        out=[];b=s
        while b!=r:
            a,i=prev[b];out.append((a,b,i));b=a
        return out[::-1]
    def component(self,edges,start):
        adj=[[]for _ in range(self.n)]
        for i in edges:
            a,b,_=self.arcs[i];adj[a].append(b);adj[b].append(a)
        seen={start};todo=[start]
        while todo:
            a=todo.pop()
            for b in adj[a]:
                if b not in seen:seen.add(b);todo.append(b)
        return seen
    def protected(self,tree,locked,s):
        """Nodes reaching s using locked edges in either direction and other arcs forward."""
        reverse=[[]for _ in range(self.n)]
        for i in tree:
            a,b,_=self.arcs[i];reverse[b].append(a)
            if i in locked:reverse[a].append(b)
        seen={s};todo=[s]
        while todo:
            b=todo.pop()
            for a in reverse[b]:
                if a not in seen:seen.add(a);todo.append(a)
        return seen


def initial_state(P):
    common=P.active(P.start)&P.active(P.target)
    forest=[];u=UnionFind(P.n)
    for i in sorted(common):
        a,b,_=P.arcs[i]
        if u.join(a,b):forest.append(i)
    return P.tree(P.active(P.start),forest),P.tree(P.active(P.target),forest),set(forest)


def construct(data):
    P=Network(data);tree,target_tree,locked=initial_state(P)
    x=P.start;phases=[]
    for wanted in sorted(target_tree-locked):
        r,s,_=P.arcs[wanted];events=[]
        while wanted not in P.active(x):
            path=P.path(tree,r,s)
            backwards=[i for a,b,i in path if i not in locked and P.arcs[i][0]==b]
            require(bool(backwards),'slack target arc has no backward unlocked tree edge')
            leave=backwards[-1]
            S=P.component(tree-{leave},s)
            blockers=[(c-(x[b]-x[a]),i) for i,(a,b,c) in enumerate(P.arcs) if a not in S and b in S]
            require(bool(blockers),'target does not block cut')
            step,enter=min(blockers)
            y=tuple(v+step*(int(j in S)-int(0 in S)) for j,v in enumerate(x))
            events.append({'leave':leave,'enter':enter,'step':str(step),'moving_nodes':sorted(S)})
            tree=(tree-{leave})|{enter};x=y
            require(len(events)<=P.m,'phase pivot bound exceeded')
        # If the desired arc became tight with another blocker, exchange a basis
        # edge at ZERO distance before locking it. No perturbation of P occurs.
        exchange=None
        if wanted not in tree:
            choices=[i for _,_,i in P.path(tree,r,s) if i not in locked]
            require(bool(choices),'target-tree edge creates a locked cycle')
            exchange=min(choices);tree=(tree-{exchange})|{wanted}
        locked.add(wanted)
        phases.append({'target_arc':wanted,'pivots':events,'final_exchange':exchange})
    require(x==P.target,'target tree did not determine target endpoint')
    cert={'input_sha256':P.digest,'start_tree':sorted(initial_state(P)[0]),
          'target_tree':sorted(target_tree),'initial_locked':sorted(initial_state(P)[2]),'phases':phases}
    return {'certificate':cert,'verified':verify(data,cert)}


def verify(data,cert):
    """Independently replay finite certificate; no call to construct() or graph BFS."""
    P=Network(data);require(isinstance(cert,dict) and cert['input_sha256']==P.digest,'source problem changed')
    tree=set(cert['start_tree']);target_tree=set(cert['target_tree']);locked=set(cert['initial_locked'])
    P.check_tree(cert['start_tree'],P.start);P.check_tree(cert['target_tree'],P.target)
    require(len(locked)==len(cert['initial_locked']),'duplicate locked arc')
    require(locked<=tree&target_tree,'locked arcs absent from endpoint bases')
    common=P.active(P.start)&P.active(P.target)
    require(P.labels(locked)==P.labels(common),'initial locks must span ALL common tight equalities')
    h=P.n-1-len(locked);row_count=sum(P.labels(common)[a]!=P.labels(common)[b] for a,b,_ in P.arcs)
    x=P.start;route=[x];positive=zero=swaps=0;records=[]
    require(len(cert['phases'])==h,'wrong number of contraction phases')
    for phase in cert['phases']:
        wanted=phase['target_arc'];require(type(wanted)is int and wanted in target_tree-locked,'invalid target phase')
        r,s,cwant=P.arcs[wanted];labels=P.labels(locked);components=len(set(labels))
        deleted=set();deleted_pairs=set();permanent=P.protected(tree,locked,s)
        before_pos=positive;before_zero=zero
        for event in phase['pivots']:
            require(wanted not in P.active(x),'pivots continue after target acquisition')
            leave=event['leave'];enter=event['enter'];step=rat(event['step'])
            require(type(leave)is int and type(enter)is int,'noninteger arc label')
            require(leave in tree-locked and 0<=enter<P.m,'invalid basis exchange')
            a,b,_=P.arcs[leave]
            pair=tuple(sorted((labels[a],labels[b])))
            require(leave not in deleted and pair not in deleted_pairs,'deleted arc or quotient pair reused')
            path=P.path(tree,r,s)
            backwards=[i for u,v,i in path if i not in locked and P.arcs[i][0]==v]
            require(backwards and leave==backwards[-1],'not the final backward unlocked edge')
            S=P.component(tree-{leave},s);R=set(range(P.n))-S
            require(r in R and s in S and a in S and b in R,'incorrect cut orientation')
            require(event['moving_nodes']==sorted(S),'forged moving component')
            require(permanent<=S,'protected arborescence escaped moving side')
            for j in locked:
                u,v,_=P.arcs[j];require((u in S)==(v in S),'locked equality would change')
            blockers=[(cost-(x[v]-x[u]),i)for i,(u,v,cost)in enumerate(P.arcs)if u in R and v in S]
            require(blockers and step>=0 and (step,enter)in blockers and step==min(t for t,_ in blockers),
                    'false maximal feasible step or blocker')
            require(enter not in tree,'entering arc already in basis')
            u,v,_=P.arcs[enter];require(u in R and v in S,'entering arc direction')
            y=tuple(val+step*(int(j in S)-int(0 in S))for j,val in enumerate(x))
            P.check_point(y)
            next_tree=(tree-{leave})|{enter};P.check_tree(sorted(next_tree),y)
            if step:
                # Tree minus leaving edge supplies connected sides in the COMMON
                # active graph. Nonzero cut movement excludes every crossing arc.
                both=P.active(x)&P.active(y)
                require(len(set(P.labels(both)))==2,'claimed move is not an ordinary edge')
                require(y not in route[-1:],'nonpositive paid move')
                require(common<=both,'left the original smallest common face')
                positive+=1;route.append(y)
            else:
                require(y==x,'zero pivot moved the point');zero+=1
            # The former directed suffix plus newly inserted forward arc protects
            # all previously protected nodes and the tail of the removed edge.
            new_protected=P.protected(next_tree,locked,s)
            require(permanent|{a}<=new_protected,'protected arborescence shrank')
            deleted.add(leave);deleted_pairs.add(pair);permanent=new_protected
            tree=next_tree;x=y
        require(wanted in P.active(x),'phase failed to reach requested target equality')
        exchange=phase['final_exchange']
        if wanted not in tree:
            require(type(exchange)is int and exchange in tree-locked,'invalid terminal zero exchange')
            require(exchange in {i for _,_,i in P.path(tree,r,s)},'terminal exchange not on cycle')
            tree=(tree-{exchange})|{wanted};P.check_tree(sorted(tree),x);swaps+=1
        else:require(exchange is None,'unnecessary terminal exchange')
        require(len(deleted_pairs)<=components*(components-1)//2,'phase unordered-pair bound')
        records.append({'components':components,'positive_edges':positive-before_pos,
                        'zero_pivots':zero-before_zero,'distinct_deleted_pairs':len(deleted_pairs),
                        'target_arc':wanted})
        locked.add(wanted)
    require(locked==target_tree and x==P.target,'wrong final requested vertex')
    require(positive+zero<=min(h*row_count,h*(h+1)*(h+2)//6),'polynomial pivot bound')
    return {'status':'PASS','route':serial(route),'ordinary_edges':positive,'zero_pivots':zero,
            'terminal_basis_exchanges':swaps,'carrier_dimension':h,'nonconstant_input_rows':row_count,
            'linear_row_budget':h*row_count,'dimension_budget':h*(h+1)*(h+2)//6,'phases':records,
            'source_tight_count':len(P.active(P.start)),'target_tight_count':len(P.active(P.target)),
            'scope':'Exact original-inequality and spanning-forest checks; no vertex enumeration or Lean/platform verdict.'}


def recognize_rows(data):
    """Recognize coordinate-difference H-rows up to a positive scale, exactly.
    With x_0 fixed, a one-entry row is an arc involving node zero. No row drops.
    This is NOT automatic recognition under arbitrary unknown affine changes.
    """
    A=data['A'];b=data['b'];require(A and len(A)==len(b),'H-row shape')
    d=len(A[0]);arcs=[];scales=[]
    for row,bound in zip(A,b):
        require(len(row)==d,'ragged H matrix')
        row=list(map(rat,row));nz=[(i+1,x)for i,x in enumerate(row)if x]
        require(len(nz)in (1,2),'not a coordinate-difference row')
        if len(nz)==1:
            i,x=nz[0];a,j=(0,i)if x>0 else(i,0);sc=abs(x)
        else:
            (i,x),(j,y)=nz
            require(x+y==0,'two coefficients do not sum to zero')
            a,j=(i,j)if x<0 else(j,i);sc=abs(x)
        arcs.append([a,j,rat(bound)/sc]);scales.append(sc)
    out={'nodes':d+1,'arcs':arcs,'source':[0]+list(data['source']),'target':[0]+list(data['target'])}
    Network(out)
    return out,scales


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    try:
        data=json.loads(args.input.read_text())
        if 'A'in data:data,_=recognize_rows(data)
        ans=verify(data,json.loads(args.certificate.read_text()))if args.certificate else construct(data)
        txt=json.dumps(serial(ans),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(txt)
        else:print(txt,end='')
    except(ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError)as exc:
        ap.exit(2,f'Certificate rejected: {exc}\n')

if __name__=='__main__':main()
