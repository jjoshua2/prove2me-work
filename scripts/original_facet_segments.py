#!/usr/bin/env python3
"""Classical combinatorial segments, discovered from original H inequalities.

The input supplies A,b,start,target for a simple bounded full-dimensional
polytope. No vertex graph, facet graph, incidence catalogue or flag certificate
is supplied. Each queried intersection has an independently checked original-
row feasible witness or a dual strict-separation witness. Adiprasito--Benedetti
prove nonrevisiting for FLAG normal complexes; that condition is NOT asserted
for arbitrary inputs. Returned routes always get direct original-edge audits,
an exact facet-reentry ledger, and explicit caps on discovery effort.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json
import exact_farkas_lp as lp
import simple_tangent_policy_audit as basis

require, rat, serial, dot = lp.require, lp.rat, lp.serial, lp.dot


def parse(data):
    A,b=lp.parse(data['A'],data['b']); d=len(A[0])
    u=tuple(map(rat,data['start']));v=tuple(map(rat,data['target']))
    require(len(u)==len(v)==d,'endpoint dimension mismatch')
    return A,b,u,v


def key(S):return ','.join(map(str,sorted(S)))


def labels(raw,m):
    require(type(raw)is list and all(type(i)is int and 0<=i<m for i in raw)
            and raw==sorted(set(raw)),'invalid facet labels')
    return frozenset(raw)


def input_hash(A,b,u,v):
    return hashlib.sha256(json.dumps(serial([A,b,u,v]),separators=(',',':')).encode()).hexdigest()


def objective(A,S):
    return tuple(sum((A[i][j] for i in S),Q(0)) for j in range(len(A[0])))


def intersection_audit(A,b,S,record):
    """No rank/LP/search. A nonempty intersection is tied to ALL original rows."""
    require(labels(record['rows'],len(A))==S,'wrong queried intersection')
    if record['kind']=='present':
        x=tuple(map(rat,record['point']))
        require(len(x)==len(A[0]) and all(dot(a,x)<=t for a,t in zip(A,b)),'infeasible intersection witness')
        require(all(dot(A[i],x)==b[i] for i in S),'intersection equality not satisfied')
        return True,x
    require(record['kind']=='absent','unknown intersection answer')
    W=labels(record['separated_rows'],len(A));require(W and W<=S,'invalid smaller excluded intersection')
    val=lp.verify_dual(A,b,objective(A,W),record['dual'])
    require(val==rat(record['bound'])<sum((b[i] for i in W),Q(0)),
            'dual witness does not strictly exclude the selected equalities')
    return False,None


class Discovery:
    def __init__(self,A,b,u,v,pivot_cap,query_cap):
        self.A,self.b=A,b;self.cache={};self.known=[u,v];self.absent=[]
        self.solver=lp.ExactLP(A,b,u,pivot_cap);self.query_cap=query_cap
        self.lp_calls=0;self.memo_answers=0
        self.bounds=[]
        for j in range(len(u)):
            for sign in(-1,1):
                f=tuple(Q(sign*(i==j)) for i in range(len(u)))
                out=self.solver.maximize(f);self.lp_calls+=1
                self.bounds.append({'coordinate':j,'sign':sign,'dual':out['dual'],'bound':out['value']})
    def ask(self,S):
        S=frozenset(S);k=key(S)
        if k in self.cache:return self.cache[k]['kind']=='present'
        require(len(self.cache)<self.query_cap,'intersection-query cap; no completed route claimed')
        answer=None
        for W,old in self.absent:
            if W<=S:
                answer={**old,'rows':sorted(S)};self.memo_answers+=1;break
        if answer is None:
            for x in self.known:
                if all(dot(self.A[i],x)==self.b[i] for i in S):
                    answer={'rows':sorted(S),'kind':'present','point':serial(x)};self.memo_answers+=1;break
        if answer is None:
            out=self.solver.maximize(objective(self.A,S));self.lp_calls+=1
            x,val=lp.verify_optimum(self.A,self.b,objective(self.A,S),out)
            bound=sum((self.b[i] for i in S),Q(0));require(val<=bound,'impossible intersection support value')
            if val==bound:
                answer={'rows':sorted(S),'kind':'present','point':serial(x)}
                if x not in self.known:self.known.append(x)
            else:
                answer={'rows':sorted(S),'kind':'absent','separated_rows':sorted(S),
                        'dual':out['dual'],'bound':out['value']}
                self.absent.append((S,answer))
        intersection_audit(self.A,self.b,S,answer);self.cache[k]=answer
        return answer['kind']=='present'
    def point(self,F):
        require(self.ask(F),'claimed vertex intersection is empty')
        return tuple(map(rat,self.cache[key(F)]['point']))


class Certified:
    def __init__(self,A,b,records):
        require(type(records)is list,'intersection records must be a list')
        self.A,self.b=A,b;self.cache={};self.used=set()
        for c in records:
            S=labels(c['rows'],len(A));k=key(S);require(k not in self.cache,'duplicate intersection answer')
            intersection_audit(A,b,S,c);self.cache[k]=c
    def ask(self,S):
        k=key(S);require(k in self.cache,'missing exact facet-intersection answer')
        self.used.add(k);return self.cache[k]['kind']=='present'
    def point(self,F):
        require(self.ask(F),'claimed vertex intersection is empty')
        return tuple(map(rat,self.cache[key(F)]['point']))


def distances(graph,Y):
    require(Y and set(Y)<=set(graph),'empty or invalid graph target set')
    D={y:0 for y in Y};q=deque(sorted(Y))
    while q:
        x=q.popleft()
        for y in sorted(graph[x]):
            if y not in D:D[y]=D[x]+1;q.append(y)
    require(len(D)==len(graph),'disconnected link graph: class assumption or certificate failure')
    return D


class Segment:
    def __init__(self,m,d,oracle,edge_cap,node_cap):
        self.m,self.d,self.oracle=m,d,oracle;self.edge_cap=edge_cap;self.node_cap=node_cap
        self.graphs={};self.events=[];self.calls=0;self.leaf_edges=0
        self.max_depth=0;self.traces=[]
    def call(self,S,F,mode,Y):
        self.calls+=1;require(self.calls<=self.node_cap,'recursion-call cap; no completion claimed')
        self.max_depth=max(self.max_depth,len(S))
        require(len(F)==self.d and S<=F,'invalid current dual facet')
        self.events.append({'kind':mode,'locked':sorted(S),'start':sorted(F),'goal':sorted(Y)})
    def graph(self,S):
        if S in self.graphs:return self.graphs[S]
        require(len(S)<=self.d-2,'zero-dimensional link has no graph-distance stage')
        V=[i for i in range(self.m) if i not in S and self.oracle.ask(S|{i})]
        G={i:set()for i in V}
        for i,j in combinations(V,2):
            if self.oracle.ask(S|{i,j}):G[i].add(j);G[j].add(i)
        self.graphs[S]=G
        return G
    def to_set(self,S,F,Y):
        S,F,Y=frozenset(S),frozenset(F),frozenset(Y)
        self.call(S,F,'set',Y)
        require(Y and not(S&Y),'invalid target vertices in link')
        if F&Y:return [F]
        if len(S)==self.d-1:
            p=min(Y);H=S|{p};require(self.oracle.ask(H),'zero-link target absent')
            self.leaf_edges+=1;require(self.leaf_edges<=self.edge_cap,'original-edge cap')
            return [F,H]
        G=self.graph(S);D=distances(G,Y)
        p=min(F-S,key=lambda i:(D[i],i));near=Y
        path=[F];pearls=[]
        while not(F&Y):
            dp=distances(G,{p});k=min(dp[y]for y in near)
            near=frozenset(y for y in near if dp[y]==k)
            D=distances(G,near);T=frozenset(z for z in G[p]if D[z]==D[p]-1)
            require(T and not(F&T),'zero-length pearl transition breaks distance descent')
            oldp=p;oldk=D[p]
            segment=self.to_set(S|{p},F,T)
            require(len(segment)>1,'nonprogressing recursive segment')
            F=segment[-1];path+=segment[1:]
            p=min(F&T);dp=distances(G,{p});kk=min(dp[y]for y in near)
            near=frozenset(y for y in near if dp[y]==kk)
            require(kk==oldk-1,'necklace distance did not drop by one')
            pearls.append({'from':oldp,'to':p,'distance_before':oldk,'distance_after':kk,
                           'segment_edges':len(segment)-1})
        self.traces.append({'locked':sorted(S),'start':sorted(path[0]),'goal':sorted(Y),
                            'pearls':pearls,'path':[sorted(f)for f in path]})
        return path
    def between(self,S,F,H):
        S,F,H=frozenset(S),frozenset(F),frozenset(H)
        self.call(S,F,'facet',H)
        require(S<=H and len(H)==self.d,'invalid target dual facet')
        if F==H:return[F]
        first=self.to_set(S,F,H-S);Z=first[-1]
        if Z==H:return first
        p=min((Z&H)-S)
        last=self.between(S|{p},Z,H)
        return first+last[1:]


def ledger(path,m,d):
    require(path,'empty original route')
    seen=set(path[0]);reentries=[];last=set(path[0]);runs={i:1 for i in path[0]}
    for k,F in enumerate(path[1:],1):
        entered=set(F)-last;left=last-set(F)
        require(len(entered)==len(left)==1,'not one original-facet exchange')
        i=next(iter(entered))
        if i in seen:reentries.append({'edge':k,'facet':i})
        seen.add(i);runs[i]=runs.get(i,0)+1;last=set(F)
    L=len(path)-1;R=len(reentries)
    require(L==len(seen)-d+R,'facet-entry identity failed')
    return {'original_edges':L,'distinct_facets_seen':len(seen),'reentries':reentries,
            'reentry_debt':R,'nonrevisiting':R==0,'hirsch_slack':m-d-L,
            'identity':'L = distinct_seen - d + facet_reentries'}


def audit_bounds(A,b,raw):
    d=len(A[0]);seen=set()
    for c in raw:
        i,s=c['coordinate'],c['sign']
        require(type(i)is int and type(s)is int and 0<=i<d and s in(-1,1)and(i,s)not in seen,'bad boundedness label')
        seen.add((i,s));f=tuple(Q(s*(j==i))for j in range(d))
        require(lp.verify_dual(A,b,f,c['dual'])==rat(c['bound']),'false original-coordinate bound')
    require(len(seen)==2*d,'missing original-coordinate bound')


def verify(data,c):
    A,b,u,v=parse(data);d=len(u);m=len(A)
    require(c['format']=='original-facet-segment-v1'and c['problem_sha256']==input_hash(A,b,u,v),'changed original input')
    audit_bounds(A,b,c['boundedness'])
    packets=c['vertices'];require(type(packets)is list,'invalid vertex records')
    V={}
    for p in packets:
        q={'point':list(map(rat,p['point'])),'active':p['active'],
           'directions':[list(map(rat,z))for z in p['directions']]}
        x,J,D=basis.audit_basis(A,b,q);F=frozenset(J)
        require(key(F)not in V,'duplicate vertex packet');V[key(F)]=(tuple(x),D)
    F=frozenset(basis.active_rows(A,b,u));H=frozenset(basis.active_rows(A,b,v))
    require(len(F)==len(H)==d and V[key(F)][0]==u and V[key(H)][0]==v,'wrong original vertex endpoints')
    for f in c['path']:labels(f,m)
    for ev in c['events']:
        labels(ev['locked'],m);labels(ev['start'],m);labels(ev['goal'],m)
    require(all(type(c['limits'][k])is int and c['limits'][k]>0 for k in('edges','nodes')),'invalid replay caps')
    oracle=Certified(A,b,c['intersections'])
    alg=Segment(m,d,oracle,c['limits']['edges'],c['limits']['nodes']);path=alg.between(F&H,F,H)
    require([sorted(f)for f in path]==c['path'],'path differs from exact recursive construction')
    require(alg.events==c['events'],'recursive trace changed')
    require(set(V)==set(key(f)for f in path),'unbound or missing route vertex')
    for F,H in zip(path,path[1:]):
        require(len(F&H)==d-1,'not adjacent original vertices')
        x,D=V[key(F)];y,_=V[key(H)];J=sorted(F);i=J.index(next(iter(F-H)))
        alpha,blocker=basis.maximal_step(A,b,x,D[i])
        require(alpha>0 and tuple(a+alpha*t for a,t in zip(x,D[i]))==y,'not maximal ORIGINAL edge')
    out=ledger(path,m,d)
    out.update({'status':'PASS','dimension':d,'original_rows':m,'intersection_queries':len(oracle.cache),
      'routing_queries_used':len(oracle.used),'visited_link_graphs':len(alg.graphs),'recursive_calls':alg.calls,
      'max_locked_depth':alg.max_depth,'no_vertex_or_facet_graph_supplied':True,
      'route_auditor_replays_BFS':True,
      'scope':'Exact original edge path and reentry ledger. Classical flag-class theorem is conditional; no universal polynomial route or LP-pivot bound.'})
    require(alg.calls<=(4*d+4)*(out['original_edges']+1),'recursive call/edge bookkeeping bound failed')
    require(len(oracle.used)<=len(alg.graphs)*(m+m*(m-1)//2)+out['original_edges'],
            'link-intersection query count exceeded combinatorial bound')
    return out


def diagnostic_obstruction(A,b,alg,oracle,limit,facet):
    """Seek a missing triangle in a USED link, not a global flag classifier.
    Each searched triangle contains the FIRST reentered original facet. A cap or
    absence of a found witness is not a flagness or nonexistence claim.
    """
    tried=0
    for S,G in sorted(alg.graphs.items(),key=lambda a:(len(a[0]),sorted(a[0]))):
        if facet not in G:continue
        for p,q in combinations(sorted(G[facet]),2):
            i,j,k=sorted((facet,p,q))
            if q in G[p]:
                if tried>=limit:return {'status':'cap','triple_queries':tried}
                tried+=1
                if not oracle.ask(S|{i,j,k}):
                    return {'status':'witness','reentered_facet':facet,'locked':sorted(S),'triangle':[i,j,k],
                      'pair_intersections':[key(S|set(p))for p in combinations((i,j,k),2)],
                      'empty_triple':key(S|{i,j,k}),'triple_queries':tried}
    return {'status':'none_found_in_scanned_links','triple_queries':tried}


def verify_obstruction(A,b,records,obs):
    require(obs['status']=='witness','not an obstruction witness')
    O=Certified(A,b,records);S=labels(obs['locked'],len(A));W=labels(obs['triangle'],len(A))
    require(len(W)==3 and not S&W,'invalid link triangle')
    require(type(obs['reentered_facet'])is int and obs['reentered_facet']in W,'missing triangle does not contain the claimed reentered facet')
    require(all(O.ask(S|set(p))for p in combinations(W,2)),'pairwise link intersection missing')
    require(not O.ask(S|W),'alleged missing triangle is a face')
    return True


def construct(data,edge_cap=10000,node_cap=100000,query_cap=100000,pivot_cap=20000,diagnose=2000):
    require(all(type(v)is int and v>0 for v in(edge_cap,node_cap,query_cap,pivot_cap)),'invalid cap')
    A,b,u,v=parse(data);d=len(u);m=len(A)
    pu=basis.basis_packet(A,b,u);pv=basis.basis_packet(A,b,v)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    O=Discovery(A,b,u,v,pivot_cap,query_cap);alg=Segment(m,d,O,edge_cap,node_cap)
    path=alg.between(F&H,F,H);vert={key(F):pu,key(H):pv}
    for V in path:
        if key(V)not in vert:
            p=basis.basis_packet(A,b,O.point(V));require(frozenset(p['active'])==V,'nonsimple or wrong reconstructed vertex')
            vert[key(V)]=p
    debt=ledger(path,m,d)
    obs=diagnostic_obstruction(A,b,alg,O,diagnose,debt['reentries'][0]['facet'])if debt['reentry_debt']else {'status':'not_requested_nonrevisiting'}
    if obs['status']=='witness':verify_obstruction(A,b,list(O.cache.values()),obs)
    cert={'format':'original-facet-segment-v1','problem_sha256':input_hash(A,b,u,v),
          'limits':{'edges':edge_cap,'nodes':node_cap},'boundedness':O.bounds,
          'vertices':list(vert.values()),'intersections':list(O.cache.values()),
          'events':alg.events,'path':[sorted(f)for f in path]}
    report=verify(data,cert)
    return {'certificate':serial(cert),'verified':report,'obstruction':obs,
      'discovery_work':{'lp_maximizations':O.lp_calls,'simplex_pivots':O.solver.pivots,
                        'memo_derived_answers':O.memo_answers},
      'proof_boundary':'Adiprasito--Benedetti supplies the flag-class guarantee; producer and Python parser are not Lean-verified.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',type=Path)
    p.add_argument('--edge-cap',type=int,default=10000);p.add_argument('--query-cap',type=int,default=100000)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=verify(data,json.loads(a.certificate.read_text()))if a.certificate else construct(data,a.edge_cap,query_cap=a.query_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except(ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError)as e:
        p.exit(2,f'No completed original-facet segment: {e}\n')
if __name__=='__main__':main()
