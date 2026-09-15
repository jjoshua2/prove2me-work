#!/usr/bin/env python3
"""Graphical nested-set refinements with certified ORIGINAL-edge routes.

Refinement vertices are nonempty connected original faces of an auxiliary graph.
The exact flag criterion is <=2 induced graph components per original minimal
nonface. Paths and cycles give quadratic-size sufficient certificates, not a
universal existence claim. Complete original H-to-nonface discovery may be
exponential. Existing Lean/Prove2Me status is not conferred on this Python code.
"""
from __future__ import annotations
from itertools import combinations, permutations
from pathlib import Path
import argparse, hashlib, json, random
import defect_incidence_compression as old

require = old.require


def graph(n, edges):
    require(type(n) is int and n >= 1, 'positive original label count required')
    require(isinstance(edges, (list, tuple)), 'edge list required')
    adj = [set() for _ in range(n)]; seen = set()
    for E in edges:
        require(isinstance(E, (list, tuple)) and len(E) == 2 and
                all(type(i) is int and 0 <= i < n for i in E) and E[0] != E[1],
                'invalid auxiliary edge')
        e = tuple(sorted(E)); require(e not in seen, 'duplicate auxiliary edge')
        seen.add(e); a,b = e; adj[a].add(b); adj[b].add(a)
    return adj


def components(adj, labels):
    left = set(labels); out = []
    require(all(type(i) is int and 0 <= i < len(adj) for i in left), 'invalid induced labels')
    while left:
        a = min(left); left.remove(a); C = {a}; todo = [a]
        while todo:
            x = todo.pop(); fresh = adj[x] & left
            C.update(fresh); todo.extend(sorted(fresh)); left.difference_update(fresh)
        out.append(frozenset(C))
    return out


def ordered_edges(order, cycle=False):
    require(len(order) >= 1 and set(order) == set(range(len(order))) and
            all(type(i) is int for i in order), 'order must be a label permutation')
    edges = [list(e) for e in zip(order, order[1:])]
    if cycle:
        require(len(order) >= 3, 'cycle needs at least three labels')
        edges.append([order[-1], order[0]])
    return edges


def check_criterion(K, adj):
    return [{'nonface': sorted(N), 'components': [sorted(C) for C in components(adj,N)]}
            for N in K.missing if len(components(adj,N)) > 2]


def find_order(K, cycle=False, trial_cap=100000):
    """Capped exact finite search. Exhaustion is reported only if every order is scanned."""
    require(type(trial_cap) is int and trial_cap > 0, 'positive order-search cap required')
    n=K.n; tested=0
    if cycle:
        require(n >= 3, 'cycle needs three vertices')
        orders=((0,)+p for p in permutations(range(1,n)) if p[0] < p[-1])
    else:
        orders=(p for p in permutations(range(n)) if n == 1 or p[0] < p[-1])
    for order in orders:
        if tested >= trial_cap:
            return None, {'status':'search_cap','orders_tested':tested}
        tested += 1; edges = ordered_edges(order,cycle)
        if not check_criterion(K,graph(n,edges)):
            return list(order), {'status':'found','orders_tested':tested}
    return None, {'status':'exhausted','orders_tested':tested}


def search_sparse_graph(K, degree_limit=2, state_cap=100000):
    """Exact branch-and-bound in a finite graph class, with honest caps.

    Every unresolved minimal nonface with >2 current components requires an
    added edge between two of them. These branches cover every feasible
    supergraph. Connected-face count is monotone under adding graph edges.
    A complete search certifies the best count in this degree-bounded class;
    a capped search returns only the best valid graph found, not optimality.
    """
    require(type(degree_limit) is int and 0 <= degree_limit < K.n, 'invalid graph degree cap')
    require(type(state_cap) is int and state_cap > 0, 'invalid graph search cap')
    high=K.high(); seen=set(); best=[None,None]; hit_cap=False; evaluated=0
    def visit(edges,adj):
        nonlocal hit_cap,evaluated
        key=frozenset(edges)
        if key in seen:return
        if len(seen)>=state_cap:hit_cap=True;return
        seen.add(key)
        R=GraphicalRefinement(K,[list(e) for e in sorted(key)])
        cost=len(R.vertices);evaluated+=1
        if best[0] is not None and cost>=best[0]:return
        violations=[]
        for N in high:
            cc=components(adj,N)
            if len(cc)>2:
                choices=sorted({tuple(sorted((a,b))) for C,D in combinations(cc,2)
                     for a in C for b in D if len(adj[a])<degree_limit and len(adj[b])<degree_limit})
                if not choices:return
                violations.append(choices)
        if not violations:
            best[:]=[cost,[list(e) for e in sorted(key)]];return
        opts=min(violations,key=lambda q:(len(q),q))
        opts.sort(key=lambda E:(-sum(set(E)<=N for N in high),E))
        for a,b in opts:
            aa=[set(v) for v in adj];aa[a].add(b);aa[b].add(a)
            visit(key|{(a,b)},aa)
    visit(frozenset(),graph(K.n,[]))
    return best[1], {'status':'capped' if hit_cap else 'complete',
       'states_examined':len(seen),'connected_registries_evaluated':evaluated,
       'degree_limit':degree_limit,'best_refined_vertices':best[0],
       'optimal_within_degree_limit':not hit_cap and best[1] is not None,
       'nonexistence_in_degree_class':not hit_cap and best[1] is None}


class GraphicalRefinement:
    """The nested complex, including its original-face union condition."""
    def __init__(self, K, edges, registry_cap=100000):
        require(type(registry_cap) is int and registry_cap > 0, 'positive registry cap required')
        self.K=K; self.adj=graph(K.n,edges); self.edges=sorted([list(e) for e in combinations(range(K.n),2) if e[1] in self.adj[e[0]]])
        # Every connected face has a spanning-tree growth order. Once a set is
        # not an original face, none of its supersets can be a face. This exact
        # closure therefore enumerates ALL connected faces, not a sample.
        known={frozenset([i]) for i in range(K.n)}
        require(len(known)<=registry_cap,'registry cap')
        todo=sorted(known,key=lambda S:min(S)); pos=0
        while pos<len(todo):
            S=todo[pos];pos+=1; fringe=set().union(*(self.adj[i] for i in S))-S
            for i in sorted(fringe):
                T=S|{i}
                if T not in known and K.ask(T):
                    require(len(known)<registry_cap,'registry cap: incomplete connected-face enumeration')
                    known.add(T);todo.append(T)
        self.vertices=sorted(known,key=lambda S:(len(S),tuple(sorted(S))))
        self.index={S:i for i,S in enumerate(self.vertices)}; self.cache={}

    def compatible(self,A,B):
        if A<=B or B<=A:return True
        if A&B:return False
        return not any(self.adj[i]&B for i in A)

    def ask(self,S):
        S=frozenset(S)
        require(all(type(i) is int and 0<=i<len(self.vertices) for i in S),'invalid refined label')
        if S in self.cache:return self.cache[S]
        tubes=[self.vertices[i] for i in S]
        union=frozenset().union(*tubes)
        ans=self.K.ask(union) and all(self.compatible(A,B) for A,B in combinations(tubes,2))
        self.cache[S]=ans;return ans

    def lift(self,F,common):
        prefix=set();chosen=set()
        for i in sorted(F&common)+sorted(F-common):
            prefix.add(i)
            C=next(C for C in components(self.adj,prefix) if i in C)
            chosen.add(self.index[C])
        require(len(chosen)==len(F) and self.ask(chosen),'invalid nested endpoint lift')
        return frozenset(chosen)

    def carrier(self,F,d):
        require(len(F)==d and self.ask(F),'invalid maximal refined face')
        U=frozenset().union(*(self.vertices[i] for i in F))
        require(len(U)==d and self.K.ask(U),'carrier is not a full original simplex')
        return U


def route(K,F,H,d,edges,registry_cap=100000):
    require(len(F)==len(H)==d and K.ask(F) and K.ask(H),'invalid original endpoints')
    R=GraphicalRefinement(K,edges,registry_cap)
    bad=check_criterion(K,R.adj)
    require(not bad, 'auxiliary graph fails the complete two-component criterion')
    M=len(R.vertices); X,Y=R.lift(F,F&H),R.lift(H,F&H)
    alg=old.old.Segment(M,d,R,max(1,M-d),(4*d+4)*(max(1,M-d)+1))
    fine=alg.between(X&Y,X,Y)
    fine_ledger=old.old.ledger(fine,M,d)
    require(fine_ledger['nonrevisiting'] and len(fine)-1<=M-d,'flag route exceeds normal-flag bound')
    allcarriers=[R.carrier(S,d) for S in fine];path=[allcarriers[0]]
    require(all(A==B or len(A&B)==d-1 for A,B in zip(allcarriers,allcarriers[1:])),
            'carrier map introduces a nonedge')
    for C in allcarriers[1:]:
        if C!=path[-1]:path.append(C)
    require(path[0]==F and path[-1]==H and all(F&H<=C for C in path),'lost original endpoint/common facet')
    packet={'auxiliary_edges':R.edges,'connected_faces':[sorted(S) for S in R.vertices],
            'refined_path':[sorted(S) for S in fine],'original_path':[sorted(S) for S in path]}
    return packet, {'refined_vertices':M,'all_pairs_original_edge_bound':M-d,
       'refined_edges':len(fine)-1,'original_edges':len(path)-1,
       'stationary_steps':len(fine)-len(path),'original_reentries':old.old.ledger(path,K.n,d)['reentry_debt'],
       'auxiliary_edges':len(R.edges),'max_auxiliary_degree':max(map(len,R.adj)),
       'refined_graph_explicitly_enumerated':False,'visited_refined_links':len(alg.graphs),
       'refined_membership_queries':len(R.cache)},path


def construct(data,edges,classification_cap=500000,registry_cap=100000):
    A,b,u,v=old.old.parse(data);m,d=len(A),len(u)
    pu,pv=old.old.basis.basis_packet(A,b,u),old.old.basis.basis_packet(A,b,v)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    O=old.old.Discovery(A,b,u,v,20000,1000000)
    K,work=old.classify(m,d,O,classification_cap)
    packet,summary,path=route(K,F,H,d,edges,registry_cap)
    bases={}
    for C in path:
        if C not in bases:
            p=old.old.basis.basis_packet(A,b,O.point(C));require(frozenset(p['active'])==C,'nonsimple carrier')
            bases[C]=p
    cert={'format':'graphical-flag-refinement-v1','problem_sha256':old.old.input_hash(A,b,u,v),
       'limits':{'classification':classification_cap,'registry':registry_cap},'boundedness':O.bounds,
       'minimal_nonfaces':[sorted(S) for S in K.missing],'refinement':packet,
       'vertices':list(bases.values()),'intersections':list(O.cache.values())}
    cert=old.old.serial(cert)
    return {'certificate':cert,'verified':verify(data,cert),
       'discovery':{'LP_maximizations':O.lp_calls,'internal_LP_pivots':O.solver.pivots},
       'scope':'Complete nonface discovery can be exponential; the auxiliary graph is supplied/certified, not assumed to exist universally.'}


def verify(data,c):
    A,b,u,v=old.old.parse(data);m,d=len(A),len(u)
    require(c['format']=='graphical-flag-refinement-v1' and c['problem_sha256']==old.old.input_hash(A,b,u,v),'input binding')
    old.old.audit_bounds(A,b,c['boundedness']); O=old.old.Certified(A,b,c['intersections'])
    K,work=old.classify(m,d,O,c['limits']['classification'])
    require(c['minimal_nonfaces']==[sorted(S) for S in K.missing],'incomplete or changed nonface catalogue')
    F,H=frozenset(old.old.basis.active_rows(A,b,u)),frozenset(old.old.basis.active_rows(A,b,v))
    packet,rep,path=route(K,F,H,d,c['refinement']['auxiliary_edges'],c['limits']['registry'])
    require(packet==c['refinement'],'incorrect registry, nested route or carrier path')
    V={}
    for p in c['vertices']:
        pp={'point':[old.old.rat(x) for x in p['point']],'active':p['active'],
             'directions':[[old.old.rat(x) for x in row] for row in p['directions']]}
        x,J,D=old.old.basis.audit_basis(A,b,pp);key=frozenset(J)
        require(key not in V,'duplicate vertex witness');V[key]=(tuple(x),J,D)
    require(set(V)==set(path) and V[F][0]==u and V[H][0]==v,'vertex registry mismatch')
    for F,H in zip(path,path[1:]):
        x,J,D=V[F];y,_,_=V[H];col=J.index(next(iter(F-H)))
        alpha,_=old.old.basis.maximal_step(A,b,x,D[col])
        require(alpha>0 and tuple(a+alpha*t for a,t in zip(x,D[col]))==y,'not a maximal original edge')
    return {'status':'PASS','dimension':d,'original_facets':m,**rep,
       'scope':'Exact original-edge certificate with classical normal-flag theorem; written graphical criterion, not Lean or platform acceptance.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('graph',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',type=Path)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());G=json.loads(a.graph.read_text())
        out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data,G['edges'])
        a.output.write_text(json.dumps(old.old.serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,OSError) as e:
        p.exit(2,f'No certified graphical refinement: {e}\n')
if __name__=='__main__':main()
