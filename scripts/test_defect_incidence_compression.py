#!/usr/bin/env python3
"""Independent stellar-update checks and original-H route tests.

Small original graphs are explicitly enumerated as test references, never
passed to the generic producer. The large coupled-simplex models use a proved
stellar history for their original complex and exact original-row edge audits;
those are NOT generic complete-LP classifications or full graph enumerations.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations,product
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,json,random,time
import sympy as sp
import defect_incidence_compression as D
import original_facet_segments as old

ROOT=Path(__file__).resolve().parents[1]


def subsets(n):
    return [frozenset(S) for k in range(n+1) for S in combinations(range(n),k)]


def explicit_facets(K):
    faces=[S for S in subsets(K.n) if K.ask(S)]
    return [S for S in faces if not any(S<T for T in faces)]


def explicit_stellar(facets,E,z):
    F=[]
    for X in facets:
        if E<=X:
            for i in E:F.append((X-{i})|{z})
        else:F.append(X)
    return [X for X in D.ordered(F) if not any(X<Y for Y in F)]


def missing_of_facets(n,facets):
    N=[]
    for S in subsets(n):
        if not any(S<=F for F in facets) and not any(T<=S for T in N):N.append(S)
    return D.ordered(N)


def abstract_tests():
    start=time.monotonic();candidates=[S for S in subsets(4) if len(S)>=2]
    counts={'complexes':0,'exact_stellar_updates':0,'safe_twin_updates':0,'pure_carrier_edges':0,
       'two_defect_size_cases':0,'sunflower_cases':0,'disjoint_cases':0}
    for mask in range(1<<len(candidates)):
        N=[S for j,S in enumerate(candidates) if mask>>j&1]
        if D.minimal(N)!=D.ordered(N):continue
        K=D.Complex(4,N);F=explicit_facets(K);counts['complexes']+=1
        pure=len({len(X) for X in F})==1;d=len(F[0])
        for edge in combinations(range(4),2):
            E=frozenset(edge)
            if not K.ask(E):continue
            J=D.stellar(K,E);G=explicit_stellar(F,E,4)
            D.require(J.missing==missing_of_facets(5,G),'stellar formula differs from explicit simplices')
            D.require(all(J.ask(S)==any(S<=Y for Y in G) for S in subsets(5)),'stellar membership mismatch')
            counts['exact_stellar_updates']+=1
            sig=K.incidence()
            if all(i in sig for i in E) and sig[edge[0]]==sig[edge[1]]:
                want=D.ordered([(N-E)|{4} if E<=N else N for N in K.high()])
                D.require(J.high()==[N for N in want if len(N)>=3],'safe higher update not exact')
                counts['safe_twin_updates']+=1
            if pure:
                for X,Y in combinations(G,2):
                    if len(X&Y)!=d-1:continue
                    U=(X-{4})|E if 4 in X else X
                    V=(Y-{4})|E if 4 in Y else Y
                    D.require(U in F and V in F and (U==V or len(U&V)==d-1),'carrier became chord')
                    counts['pure_carrier_edges']+=1
    # Arbitrarily large size parameters tested as finite antichains, NOT claims
    # that every such abstract complex is a polytope boundary.
    for a in range(1,9):
        for b in range(1,9):
            for c in range(9):
                if a+c<3 or b+c<3:continue
                E=set(range(c))|set(range(c,c+a));F=set(range(c))|set(range(c+a,c+a+b))
                K=D.Complex(a+b+c,[E,F]);st,steps,r=D.compress(K)
                want=a+b+c-(3 if c else 4)
                D.require(not st[-1].high() and len(steps)==want,'two-defect schedule count')
                counts['two_defect_size_cases']+=1
    rng=random.Random(261)
    for _ in range(120):
        q=rng.randrange(1,9);sizes=[rng.randrange(3,12) for _ in range(q)]
        pos=0;N=[]
        for k in sizes:N.append(set(range(pos,pos+k)));pos+=k
        st,steps,r=D.compress(D.Complex(pos,N))
        D.require(not st[-1].high() and len(steps)==sum(k-2 for k in sizes),'disjoint schedule count')
        counts['disjoint_cases']+=1
    for c in range(1,8):
        for q in range(2,8):
            sizes=[rng.randrange(max(1,3-c),9) for _ in range(q)];pos=c;N=[]
            for k in sizes:N.append(set(range(c))|set(range(pos,pos+k)));pos+=k
            st,steps,r=D.compress(D.Complex(pos,N))
            D.require(not st[-1].high() and len(steps)==pos-q-1,'sunflower schedule count')
            counts['sunflower_cases']+=1
    # Fully distinct incidence types need not compress. These are ABSTRACT
    # antichains only; no unproved polytopality is asserted.
    residues=[]
    for q in (3,4):
        sig=[S for S in subsets(q) if S]
        N=[{j for j,T in enumerate(sig) if i in T} for i in range(q)]
        K=D.Complex(len(sig),N);st,steps,r=D.compress(K)
        D.require(not steps and r['residual_exceptional_labels']==2**q-1,'signature extremal case')
        residues.append(r)
    # Actual polytopal mixed edge: product of two triangles. A non-twin
    # subdivision doubles its higher defects from two to four.
    K=D.Complex(6,[{0,1,2},{3,4,5}]);J=D.stellar(K,{0,3})
    D.require(len(J.high())==4,'mixed edge did not split the two original defects')
    return {'status':'PASS','stage':'abstract',**counts,'stalled_abstract_residues':residues,
       'mixed_product_edge_higher_counts':[len(K.high()),len(J.high())],
       'seconds':round(time.monotonic()-start,4)}


def simplex(d):
    return [[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(1)]*d],[Q(0)]*d+[Q(1)]


def cube(d):
    return [[Q(s*(i==j)) for j in range(d)] for i in range(d) for s in (-1,1)],[Q(1)]*(2*d)


def moment(d,n):
    V=[[Q(i)**j for j in range(1,d+1)] for i in range(n)]
    mean=[sum(v[j] for v in V)/n for j in range(d)]
    return [[v[j]-mean[j] for j in range(d)] for v in V],[Q(1)]*n


def reference(A,b):
    d=len(A[0]);V={};tests=0
    for I in combinations(range(len(A)),d):
        tests+=1;M=sp.Matrix([A[i] for i in I])
        if M.det()==0:continue
        x=tuple(Q(str(z)) for z in M.inv()*sp.Matrix([b[i] for i in I]))
        if old.basis.feasible(A,b,x):V[x]=frozenset(old.basis.active_rows(A,b,x))
    D.require(V and all(len(F)==d for F in V.values()),'reference not simple')
    # Every original row is a real facet, not merely a redundant inequality.
    for i in range(len(A)):
        X=[x for x,F in V.items() if i in F]
        avg=tuple(sum(x[j] for x in X)/len(X) for j in range(d))
        D.require(old.basis.active_rows(A,b,avg)==[i],'non-genuine facet in test')
        D.require(sp.Matrix([[x[j]-X[0][j] for j in range(d)] for x in X[1:]]).rank()==d-1,'facet rank')
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    D.require(all(len(a)==d for a in adj.values()),'reference degree mismatch')
    dist={}
    for u in V:
        dd={u:0};queue=deque([u])
        while queue:
            x=queue.popleft()
            for y in adj[x]:
                if y not in dd:dd[y]=dd[x]+1;queue.append(y)
        D.require(len(dd)==len(V),'reference disconnected');dist[u]=dd
    return V,adj,dist,tests


def geometric_tests():
    start=time.monotonic();fixtures=[];totals=[];save=[]
    models=[('simplex3',*simplex(3),0),('simplex5',*simplex(5),6),('cube3',*cube(3),8),
      ('moment3_6',*moment(3,6),0),('moment3_8',*moment(3,8),20),
      ('moment4_7_stalled',*moment(4,7),6),('moment4_8_stalled',*moment(4,8),6)]
    for name,A,b,cap in models:
        V,adj,dist,tested=reference(A,b);pairs=list(combinations(V,2))
        if cap:random.Random(261+len(A)).shuffle(pairs);pairs=pairs[:cap]
        row={'model':name,'dimension':len(A[0]),'original_facets':len(A),'vertices':len(V),
          'edges':sum(map(len,adj.values()))//2,'independent_square_systems':tested,'executed_pairs':0,
          'delivered_edges':0,'raw_258_edges':0,'shortest_edges':0,'nonshortest':0,'original_reentries':0,
          'refined_edges':0,'stationary_steps':0,'LP_maximizations':0,'LP_pivots':0,'all_possible_pairs':len(V)*(len(V)-1)//2}
        for j,(u,v) in enumerate(pairs):
            data={'A':A,'b':b,'start':u,'target':v};o=D.construct(data);r=o['verified']
            raw=old.construct(data)['verified'];p=o['certificate']['refinement']['original_path']
            inv={F:x for x,F in V.items()};path=[inv[frozenset(F)] for F in p]
            D.require(all(y in adj[x] for x,y in zip(path,path[1:])),'new path not in independent original graph')
            row['executed_pairs']+=1;row['delivered_edges']+=r['original_edges'];row['raw_258_edges']+=raw['original_edges']
            row['shortest_edges']+=dist[u][v];row['nonshortest']+=r['original_edges']>dist[u][v]
            row['original_reentries']+=r['original_reentries'];row['refined_edges']+=r['refined_edges']
            row['stationary_steps']+=r['stationary_carrier_steps'];row['LP_maximizations']+=o['discovery']['LP_maximizations']
            row['LP_pivots']+=o['discovery']['internal_LP_pivots']
            row['structural_bound']=r['global_original_edge_bound'];row['stellar_steps']=r['stellar_steps']
            row['higher_defects']=r['initial_higher_defects'];row['residual_high_support']=r['residual_exceptional_labels']
            if j==0 or (r['original_edges']>dist[u][v] and len(fixtures)<20):
                rec={'name':name,'input':D.serial(data),'output':o,'BFS_distance':dist[u][v],'raw_258_edges':raw['original_edges']}
                fixtures.append(rec);save.append((data,o))
        totals.append(row);print('geometry',row,flush=True)
    return {'status':'PASS','stage':'geometry','models':totals,'seconds':round(time.monotonic()-start,4)},fixtures,save


def coupled(p,r):
    """Generalizes #260's coupled triangles to p-dimensional simplex factors.
    Its exact shallow-cut proof is in the note. No generic H classification is
    inferred from this family-specific construction in the large tests.
    """
    D.require(p>=2 and r>=2,'coupled model needs p,r>=2')
    d=p*r;A=[];b=[];high=[];uppers=[]
    for i in range(r):
        labels=[]
        for j in range(p):
            labels.append(len(A));A.append([-Q(k==i*p+j) for k in range(d)]);b.append(Q(0))
        labels.append(len(A));uppers.append(len(A))
        A.append([Q(i*p<=k<(i+1)*p) for k in range(d)]);b.append(Q(1));high.append(labels)
    K=D.Complex(len(A),high);history=[]
    for i in range(r-1):
        edge=[uppers[i],uppers[i+1]];label=K.n;K=D.stellar(K,edge)
        delta=Q(1,10**(i+1));A.append([a+b for a,b in zip(A[edge[0]],A[edge[1]])]);b.append(Q(2)-delta)
        history.append({'edge':edge,'cut_label':label,'cut_depth':str(delta)})
    D.require(len(K.high())==3*r-2 and all(len(N)==p+1 for N in K.high()),'coupled high-nonface formula')
    # High-defect support hypergraph connects ALL labels: no nontrivial join,
    # hence no nontrivial combinatorial Cartesian factorization of the primal.
    seen={0}
    while True:
        nxt=seen|set().union(*(N for N in K.high() if N&seen))
        if nxt==seen:break
        seen=nxt
    D.require(len(seen)==len(A),'coupled defect hypergraph disconnected')
    # Two explicit aggregate vertices (all coefficients strictly positive on
    # their single chosen coordinate) with different tight budgets/split labels.
    aggregate=[]
    for parity in (0,1):
        u=[]
        for i in range(r):
            if i%2==parity:u.append(Q(1))
            else:
                ds=[Q(1,10**(j+1)) for j in (i-1,i) if 0<=j<r-1]
                u.append(Q(1)-max(ds))
        aggregate.append(u)
    x=[Q(0)]*d;y=[Q(0)]*d
    for i in range(r):x[i*p]=aggregate[0][i];y[i*p+p-1]=aggregate[1][i]
    return {'A':A,'b':b,'start':x,'target':y},K,history


def basis_from_labels(A,b,F):
    labels=sorted(F);M=[A[i] for i in labels];inv=old.basis.invert(M)
    x=[sum(inv[j][k]*b[labels[k]] for k in range(len(labels))) for j in range(len(labels))]
    return old.basis.basis_packet(A,b,x)


def family_tests():
    start=time.monotonic();records=[];fixtures=[];abstract_examples=[]
    # Same simplex obstruction noted in #260, now tested as part of a general
    # counted compression schedule rather than advertised as a new observation.
    for d in (3,6,12,24,32):
        K=D.Complex(d+1,[range(d+1)]);F=frozenset(range(d));H=frozenset(range(1,d+1))
        packet,rep,path=D.route(K,F,H,d)
        best_flat=2**((d+1)//2)+2**((d+2)//2)-2
        D.require(rep['stellar_steps']==d-1 and rep['refined_vertices']==2*d,'simplex compression formula')
        abstract_examples.append({'simplex_dimension':d,'original_facets':d+1,'hierarchical_vertices':2*d,
            'best_disjoint_block_vertices':best_flat,'new_global_bound':d,'original_diameter':1,
            'delivered_original_edges':rep['original_edges'],'scope':'exact abstract sphere route; simplex fact from #260 not new'})
    for p,r in ((2,2),(3,2),(3,3),(4,4),(8,4),(16,2)):
        data,K,history=coupled(p,r);A,b,x,y=old.parse(data);d=p*r
        bx,by=old.basis.basis_packet(A,b,x),old.basis.basis_packet(A,b,y)
        packet,rep,path=D.route(K,frozenset(bx['active']),frozenset(by['active']),d)
        vp={}
        for F in path:
            if F not in vp:vp[F]=basis_from_labels(A,b,F)
        V=D.audit_original(A,b,D.serial(list(vp.values())),path)
        D.require(V[path[0]][0]==x and V[path[-1]][0]==y,'family original endpoints mismatch')
        D.require(rep['stellar_steps']==r*(p-1) and rep['residual_higher_defects']==0,'coupled schedule formula')
        D.require(rep['global_original_edge_bound']==r*(p+1)-1,'coupled route bound formula')
        reference_vertices=None;refdist=None;global_H_nf_checked=False
        if p*r<=6:
            VV,adj,dist,sq=reference(A,b)
            nf=missing_of_facets(len(A),list(VV.values()))
            D.require(nf==K.missing,'structural family list differs from independent original geometry')
            reference_vertices=len(VV);refdist=dist[x][y];global_H_nf_checked=True
        rec={'factor_dimension':p,'factors':r,'dimension':d,'original_facets':len(A),
           'initial_higher_defects':len(K.high()),'initial_high_support':len(K.support()),
           'stellar_steps':rep['stellar_steps'],'refined_vertices':rep['refined_vertices'],
           'global_original_edge_bound':rep['global_original_edge_bound'],
           'lower_bound_any_flat_block_vertex_count':2**((p+2)//2)-1,
           'delivered_original_edges':rep['original_edges'],'refined_edges':rep['refined_edges'],
           'original_reentries':rep['original_reentries'],'reference_vertices':reference_vertices,
           'BFS_distance':refdist,'complete_generic_H_classification':False,
           'independent_small_H_nonfaces_checked':global_H_nf_checked,
           'nonproduct_high_defect_hypergraph_connected':True}
        records.append(rec);fixtures.append({'input':D.serial(data),'stellar_model_history':history,
             'structural_minimal_nonfaces':[sorted(S) for S in K.missing],
             'refinement':packet,'original_vertices':D.serial(list(vp.values())),'report':rec})
        print('coupled',rec,flush=True)
    return {'status':'PASS','stage':'family','coupled_models':records,'simplex_controls':abstract_examples,
            'seconds':round(time.monotonic()-start,4)},fixtures


def rejection_tests(saved):
    data,o=saved[0];c=o['certificate'];failures=[]
    def reject(name,f):
        try:f()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):failures.append(name)
        else:raise AssertionError('accepted invalid case '+name)
    for name,change in [
       ('missing_original_intersections',lambda x:x.update(intersections=[])),
       ('incorrect_higher_defects',lambda x:x['minimal_nonfaces'].pop()),
       ('altered_stellar_pair',lambda x:x['refinement']['steps'][0].update(edge=[0,0])),
       ('wrong_refined_path',lambda x:x['refinement']['refined_path'].pop()),
       ('original_chord_or_missing_vertex',lambda x:x['refinement']['original_path'].clear()),
       ('wrong_original_inverse',lambda x:x['vertices'][0]['directions'][0].__setitem__(0,'199')),
       ('changed_original_problem',lambda x:x.update(problem_sha256='00')),
       ('missing_boundedness',lambda x:x['boundedness'].pop()),
       ('wrong_residual_registry',lambda x:x['refinement']['residual_vertices'].pop())]:
        bad=deepcopy(c);change(bad);reject(name,lambda bad=bad:D.verify(data,bad))
    reject('classify_cap',lambda:D.construct(data,classification_cap=1))
    reject('nonface_edge',lambda:D.stellar(D.Complex(4,[{0,1}]),{0,1}))
    # A mixed actual product edge is valid subdivision but NOT a safe step.
    K=D.Complex(6,[{0,1,2},{3,4,5}]);sig=K.incidence()
    reject('mixed_incidence_called_safe',lambda:D.require(sig[0]==sig[3],'not safe'))
    # Consumer can reconstruct certificates without ANY optimization/inversion.
    old_values=(old.lp.ExactLP,old.basis.invert,old.basis.basis_packet,old.Discovery)
    def disabled(*args,**kw):raise AssertionError('consumer called geometric search')
    old.lp.ExactLP=old.basis.invert=old.basis.basis_packet=old.Discovery=disabled
    try:
        for inp,out in saved:D.require(D.verify(inp,json.loads(json.dumps(out['certificate'])))==out['verified'],'disabled replay mismatch')
    finally:old.lp.ExactLP,old.basis.invert,old.basis.basis_packet,old.Discovery=old_values
    return {'negative_controls':failures,'negative_count':len(failures),'search_disabled_audits':len(saved)}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--stage',choices=['abstract','geometry','family'],required=True);args=parser.parse_args()
    fixtures=None
    if args.stage=='abstract':report=abstract_tests()
    elif args.stage=='geometry':
        report,fixtures,saved=geometric_tests();report.update(rejection_tests(saved))
    else:report,fixtures=family_tests()
    report['scope']='Written refinement theorem and exact tests; no Lean or Prove2Me verdict'
    report['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'scripts').glob('*.py'))}
    (ROOT/f'research/DEFECT_COMPRESSION_{args.stage.upper()}_TESTS.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    if fixtures is not None:(ROOT/f'fixtures/defect_compression_{args.stage}.json').write_text(json.dumps(D.serial(fixtures),sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
