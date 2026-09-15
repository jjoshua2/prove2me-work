"""Dependency excerpt: distances, Segment and ledger from repository #258.

Read at 13fd398df7dc224deccef4cd2c1506069ed042a3, file
scripts/original_facet_segments.py, Git blob a53ad5cfc43b085d50733dbe96aabea8de4b9a51.
The algorithm bodies below are copied unchanged; only imports and require are
standalone here. This classical/reference algorithm is NOT a new contribution.
"""
from collections import deque
from itertools import combinations

def require(p, msg):
    if not p: raise ValueError(msg)


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
