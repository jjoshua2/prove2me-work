#!/usr/bin/env python3
"""Counted graphical flag refinements from private-marker defect assignments.

Uses #262's exact finite-complex type unchanged and #266's nested-set theorem.
Only this marker recognition/orientation/registry specialization is new. The
complete minimal-nonface list is an input, not discovered in polynomial time.
Normality/polytopality must be justified separately. No Lean verification.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from itertools import combinations
from pathlib import Path
import argparse, json
import stellar_defect_budget as base
from cactus_reference_segments import Segment, ledger

require = base.require


def bind_markers(K, markers=None):
    H = K.higher(); degree = Counter(x for N in H for x in N)
    require(all(len(N) == 3 for N in H), 'private-marker theorem requires higher triples')
    if markers is None:
        require(all(any(degree[x] == 1 for x in N) for N in H), 'a defect has no private marker')
        markers = [min(x for x in N if degree[x] == 1) for N in H]
    require(type(markers) is list and len(markers) == len(H), 'wrong marker count')
    require(all(type(w) is int and w in N and degree[w] == 1 for N, w in zip(H, markers)),
            'marker is absent or occurs in another higher defect')
    require(len(set(markers)) == len(markers), 'markers are not private')
    edges = [tuple(sorted(N-{w})) for N, w in zip(H, markers)]
    require(not(set(markers) & {x for E in edges for x in E}), 'marker is also a public endpoint')
    return markers, edges


def assignment_network(edges):
    """Unit-capacity network. Marginal load cost is 1,2,4,... per public label."""
    U = sorted({x for E in edges for x in E}); q = len(edges)
    index = {x: q+1+j for j, x in enumerate(U)}; sink = q+len(U)+1
    arcs = []; owner_arc = {}; slot_arc = defaultdict(list)
    def arc(u, v, cost):
        arcs.append((u, v, cost)); return len(arcs)-1
    source_arc = [arc(0, j+1, 0) for j in range(q)]
    for j, E in enumerate(edges):
        for x in E: owner_arc[j,x] = arc(j+1, index[x], 0)
    degree = Counter(x for E in edges for x in E)
    for x in U:
        for j in range(degree[x]): slot_arc[x].append(arc(index[x], sink, 2**j))
    return sink+1, sink, arcs, source_arc, owner_arc, slot_arc


def residual(arcs, flow):
    return [(u,v,c,j,1) if not f else (v,u,-c,j,-1)
            for j, ((u,v,c),f) in enumerate(zip(arcs, flow))]


def min_cost_assignment(edges):
    """Successive shortest augmentations; certificate is checked without this solver.
    Minimizes the unconstrained star SIZE UPPER BOUND, not actual face count or
    route length when some marker subsets are original nonfaces.
    """
    n, sink, arcs, source, owners, slots = assignment_network(edges)
    flow = [0]*len(arcs)
    for _ in edges:
        d = [None]*n; d[0] = 0; prev = [None]*n; R = residual(arcs, flow)
        for _ in range(n-1):
            change = False
            for u,v,c,j,sign in R:
                if d[u] is not None and (d[v] is None or d[u]+c < d[v]):
                    d[v] = d[u]+c; prev[v] = (u,j,sign); change = True
            if not change: break
        require(d[sink] is not None, 'assignment flow cannot reach sink')
        v = sink; seen = set()
        while v:
            require(v not in seen and prev[v] is not None, 'invalid shortest-path predecessor')
            seen.add(v); u,j,sign = prev[v]; flow[j] += sign; v = u
    chosen = [next(x for x in E if flow[owners[j,x]]) for j,E in enumerate(edges)]
    # Residual shortest labels from a super-source give a global optimality witness.
    d = [0]*n; R = residual(arcs, flow)
    for iteration in range(n):
        change = False
        for u,v,c,_,_ in R:
            if d[v] > d[u]+c: d[v] = d[u]+c; change = True
        if not change: break
        require(iteration < n-1, 'negative residual cycle after min-cost assignment')
    proof = {'owners': chosen, 'potentials': d,
             'upper_cost': sum(c*f for (_,_,c),f in zip(arcs,flow))}
    verify_assignment(edges, proof)
    return proof


def verify_assignment(edges, proof):
    """Arithmetic residual optimality audit; no flow or orientation discovery."""
    chosen = proof['owners']; n,sink,arcs,source,owners,slots = assignment_network(edges)
    require(type(chosen) is list and len(chosen)==len(edges) and
            all(type(x) is int and x in E for x,E in zip(chosen,edges)), 'invalid assigned endpoint')
    p = proof['potentials']; require(type(p) is list and len(p)==n and
            all(type(x) is int for x in p), 'invalid residual potentials')
    load = Counter(chosen); flow = [0]*len(arcs)
    for j,x in enumerate(chosen): flow[source[j]]=flow[owners[j,x]]=1
    for x,js in slots.items():
        for j in js[:load[x]]: flow[j]=1
    balance = [0]*n
    for (u,v,_),f in zip(arcs,flow): balance[u]-=f; balance[v]+=f
    require(balance[0]==-len(edges) and balance[sink]==len(edges) and
            all(balance[v]==0 for v in range(1,sink)), 'assignment flow is not conserved')
    require(all(c+p[u]-p[v]>=0 for u,v,c,_,_ in residual(arcs,flow)), 'negative reduced residual cost')
    cost = sum(2**d-1 for d in load.values())
    require(type(proof['upper_cost']) is int and proof['upper_cost']==cost, 'wrong orientation upper cost')
    return {'status':'PASS', 'upper_cost':cost, 'maximum_load':max(load.values(),default=0),
            'scope':'Optimal unconstrained star-count upper bound for fixed marker binding, not shortest routes.'}


class Registry:
    def __init__(self, K, markers, owners, cap=100000):
        require(type(cap) is int and cap >= K.n, 'registry cap below original labels')
        self.K = K; self.markers, E = bind_markers(K,markers)
        require(len(owners)==len(E) and all(x in e for x,e in zip(owners,E)), 'bad orientation')
        self.aux = {i:set() for i in range(K.n)}; groups=defaultdict(list)
        for w,x in zip(markers,owners):
            self.aux[x].add(w); self.aux[w].add(x); groups[x].append(w)
        self.tubes = [frozenset([i]) for i in range(K.n)]
        self.group_counts = {}; self.marker_clique = 0
        for x, leaves in sorted(groups.items()):
            count = 0
            def visit(chosen, candidates):
                nonlocal count
                for pos,w in enumerate(candidates):
                    C = chosen+(w,); T = frozenset((x,*C))
                    require(K.face(T), 'claimed private clique is not an original face')
                    self.tubes.append(T); count += 1; self.marker_clique=max(self.marker_clique,len(C))
                    require(len(self.tubes)<=cap, 'registry cap: no complete flag certificate')
                    rest = [z for z in candidates[pos+1:] if K.face((w,z))]
                    visit(C,rest)
            visit((),sorted(leaves)); self.group_counts[x]=count
        self.index={T:i for i,T in enumerate(self.tubes)}; self.n=len(self.tubes)
        require(len(self.index)==self.n, 'duplicate connected face')
        self.neighbors=[0]*self.n
        for i,A in enumerate(self.tubes):
            for j in range(i):
                B=self.tubes[j]
                compatible = (A<=B or B<=A or
                    (not(A&B) and not any(y in self.aux[x] for x in A for y in B)))
                if compatible and K.face(A|B):
                    self.neighbors[i] |= 1<<j; self.neighbors[j] |= 1<<i
        self.cache={}; self.queries=0; self.query_cap=None
    def ask(self, face):
        self.queries+=1
        require(self.query_cap is None or self.queries <= self.query_cap, 'clique query cap: route incomplete')
        F=frozenset(face)
        if F in self.cache: return self.cache[F]
        mask=0; answer=True
        for i in F:
            require(type(i) is int and 0<=i<self.n, 'bad refined index')
            if mask & ~self.neighbors[i]: answer=False; break
            mask |= 1<<i
        self.cache[F]=answer; return answer
    def lift(self,F,common):
        prefix=set(); out=[]
        for x in sorted(F&common)+sorted(F-common):
            prefix.add(x); C={x}; stack=[x]
            while stack:
                for y in self.aux[stack.pop()] & prefix:
                    if y not in C: C.add(y); stack.append(y)
            out.append(self.index[frozenset(C)])
        require(len(set(out))==len(F) and self.ask(out), 'bad nested endpoint lift')
        return frozenset(out)
    def carrier(self,F):
        return frozenset().union(*(self.tubes[i] for i in F))


def construct(K, first=None, last=None, d=None, markers=None, cap=100000, query_cap=2000000):
    markers, edges = bind_markers(K,markers); assign=min_cost_assignment(edges)
    R=Registry(K,markers,assign['owners'],cap)
    certificate={'format':'private-marker-stars-v1','input_sha256':base.fingerprint(K),
        'markers':markers,'assignment':assign,'registry':[sorted(T) for T in R.tubes]}
    if first is not None:
        F,H=frozenset(first),frozenset(last)
        require(len(F)==len(H)==d and K.face(F) and K.face(H), 'invalid original endpoint simplices')
        require(type(query_cap) is int and query_cap > 0, 'invalid route query cap')
        R.query_cap=query_cap
        X,Y=R.lift(F,F&H),R.lift(H,F&H)
        alg=Segment(R.n,d,R,max(1,R.n-d),(4*d+4)*(max(1,R.n-d)+1))
        fine=alg.between(X&Y,X,Y); path=[]
        for f in fine:
            Q=R.carrier(f)
            if not path or Q!=path[-1]: path.append(Q)
        certificate['route']={'dimension':d,'first':sorted(F),'last':sorted(H),
            'refined':[sorted(f) for f in fine],'original':[sorted(f) for f in path]}
        certificate['discovery']={'clique_queries':R.queries,'visited_links':len(alg.graphs),
                                 'refined_maximal_facets_enumerated':0}
    return certificate, verify(K,certificate,cap)


def verify(K,c,cap=100000):
    require(c['format']=='private-marker-stars-v1' and c['input_sha256']==base.fingerprint(K), 'changed original complex')
    markers,edges=bind_markers(K,c['markers']); optimal=verify_assignment(edges,c['assignment'])
    R=Registry(K,markers,c['assignment']['owners'],cap)
    require(c['registry']==[sorted(T) for T in R.tubes], 'omitted or changed connected ORIGINAL face')
    counts={'status':'PASS','original_labels':K.n,'higher_defects':len(edges),
        'refined_vertices':R.n,'subdivisions':R.n-K.n,'orientation_upper_cost':optimal['upper_cost'],
        'maximum_assignment_load':optimal['maximum_load'],'largest_assigned_marker_clique':R.marker_clique}
    if 'route' in c:
        r=c['route']; d=r['dimension']
        require(type(d) is int and d > 0, 'invalid route dimension')
        def face_labels(raw,n):
            require(type(raw) is list and all(type(x) is int and 0 <= x < n for x in raw) and
                    raw==sorted(set(raw)), 'invalid or duplicated face labels')
            return frozenset(raw)
        F,H=face_labels(r['first'],K.n),face_labels(r['last'],K.n)
        require(len(F)==len(H)==d and K.face(F) and K.face(H), 'invalid declared original endpoints')
        fine=[face_labels(f,R.n) for f in r['refined']]
        require(fine and all(len(f)==d and R.ask(f) for f in fine), 'bad refined chamber')
        require(all(len(A&B)==d-1 for A,B in zip(fine,fine[1:])), 'refined nonedge')
        require(fine[0]==R.lift(F,F&H) and fine[-1]==R.lift(H,F&H), 'changed refined endpoints')
        require(ledger(fine,R.n,d)['nonrevisiting'], 'repeated refined label')
        path=[]
        for f in fine:
            Q=R.carrier(f); require(len(Q)==d and K.face(Q), 'carrier is not an original full face')
            require(F&H<=Q, 'lost original common face')
            if not path or path[-1]!=Q: path.append(Q)
        require(path[0]==F and path[-1]==H and r['original']==[sorted(Q) for Q in path], 'changed original route')
        require(all(len(A&B)==d-1 for A,B in zip(path,path[1:])), 'carrier sends edge to chord')
        require(len(path)-1<=len(fine)-1<=R.n-d, 'route bound failed')
        counts.update(original_edges=len(path)-1,refined_edges=len(fine)-1,
            stationary_carriers=len(fine)-len(path),structural_bound=R.n-d,
            original_reentries=ledger(path,K.n,d)['reentry_debt'])
    counts['scope']='Exact marker/registry/route certificate; normality and original H geometry require separate proof. Not Lean.'
    return counts


def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('input',type=Path)
    p.add_argument('--certificate',type=Path); p.add_argument('--output',type=Path,required=True)
    args=p.parse_args(); data=json.loads(args.input.read_text())
    K=base.Complex.create(data['vertices'],data['minimal_nonfaces'])
    if args.certificate: result=verify(K,json.loads(args.certificate.read_text()))
    else:
        c,r=construct(K,data.get('first'),data.get('last'),data.get('dimension'),data.get('markers'))
        result={'certificate':c,'verified':r}
    args.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
if __name__=='__main__': main()
