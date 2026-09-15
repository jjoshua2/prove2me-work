#!/usr/bin/env python3
"""Counted hierarchical flag refinement, with ORIGINAL-edge carrier transport.

The input class is simple bounded full-dimensional original H-polytopes. The
complete original minimal-nonface classification can be exponential and is
explicitly capped. A pair of labels may be compressed only when it has the same
NONEMPTY incidence in all higher minimal nonfaces. The exact stellar update
then creates no higher defect other than the prescribed smaller descendants.
No small number of defects, short refinement or polynomial recognition cost is
assumed for arbitrary inputs. This is research code, not Lean-extracted code.
"""
from __future__ import annotations
from itertools import combinations
from math import comb
from pathlib import Path
import argparse, json
import original_facet_segments as old

require, serial = old.require, old.serial


def ordered(sets):
    return sorted(set(map(frozenset, sets)), key=lambda s: (len(s), tuple(sorted(s))))


def minimal(sets):
    out=[]
    for S in ordered(sets):
        if not any(T<=S for T in out): out.append(S)
    return out


class Complex:
    """A fully specified finite complex by its minimal nonfaces, not a sample."""
    def __init__(self, n, missing):
        require(type(n)is int and n>=0, 'invalid complex vertex count')
        self.n=n; self.missing=ordered(missing)
        require(all(len(S)>=2 and all(type(i)is int and 0<=i<n for i in S)
                    for S in self.missing), 'invalid minimal nonface labels')
        require(self.missing==minimal(self.missing), 'nonfaces are not an antichain')
        self.cache={}
    def ask(self,S):
        S=frozenset(S)
        require(all(type(i)is int and 0<=i<self.n for i in S),'invalid face label')
        return not any(N<=S for N in self.missing)
    def high(self): return [S for S in self.missing if len(S)>=3]
    def support(self): return frozenset().union(*self.high())
    def incidence(self):
        H=self.high()
        return {i:tuple(j for j,N in enumerate(H) if i in N) for i in self.support()}


def stellar(K, edge):
    """Exact minimal-nonface formula for subdivision of a FACE edge.
    For mixed high incidences this can SPLIT defects; callers must not silently
    use the safe-compression theorem for such a step.
    """
    E=frozenset(edge)
    require(len(E)==2 and K.ask(E), 'subdivision edge is not a face')
    z=K.n
    candidates=[E]+[N for N in K.missing if not E<=N]
    candidates += [(N-E)|{z} for N in K.missing if N&E]
    return Complex(z+1,minimal(candidates))


def twin_pair(K):
    groups={}
    for i,sig in K.incidence().items(): groups.setdefault(sig,[]).append(i)
    pairs=[tuple(sorted(v)[:2]) for v in groups.values() if len(v)>=2]
    return min(pairs) if pairs else None


def compress(K, step_cap=10000):
    require(type(step_cap)is int and step_cap>=0, 'invalid compression cap')
    initial_q=len(K.high());initial_k=len(K.support());steps=[];stages=[K]
    while (E:=twin_pair(K)) is not None:
        require(len(steps)<step_cap,'compression cap: no completed schedule')
        sig=K.incidence();u,v=E
        require(sig[u] and sig[u]==sig[v], 'unequal or empty higher-defect incidence')
        J=stellar(K,E)
        expected=ordered([(N-set(E))|{K.n} if set(E)<=N else N for N in K.high()])
        expected=[N for N in expected if len(N)>=3]
        require(J.high()==expected,'higher-defect update disagrees with safe rule')
        require(len(J.support())<len(K.support()),'higher support did not decrease')
        steps.append({'edge':list(E),'new_label':K.n,'higher_before':len(K.high()),
                      'higher_after':len(J.high()),'support_before':len(K.support()),
                      'support_after':len(J.support())})
        K=J;stages.append(K)
    h=len(K.support());q=len(K.high())
    require(len(steps)<=initial_k-h and q<=initial_q,'compression resource bound failed')
    require(h<=2**q-1,'residual incidence-signature bound failed')
    return stages,steps,{'initial_higher_defects':initial_q,'initial_exceptional_labels':initial_k,
       'stellar_steps':len(steps),'residual_higher_defects':q,'residual_exceptional_labels':h,
       'residual_signature_cap':2**q-1}


def classify(n,d,O,cap):
    """Complete original face classification, same cutoff as #260, not efficient recognition."""
    require(type(cap)is int and cap>0,'invalid classification cap')
    work=sum(comb(n,j) for j in range(1,min(n,d+1)+1))
    require(work<=cap,'complete classification cap: no global flagness claim')
    missing=[];questions=0
    for j in range(1,min(n,d+1)+1):
        for labels in combinations(range(n),j):
            S=frozenset(labels)
            if any(N<=S for N in missing):continue
            questions+=1
            if not O.ask(S):missing.append(S)
    return Complex(n,missing),{'classification_subsets':work,'classification_questions':questions}


class ResidualRefinement:
    """The single residual-block barycentric construction from #260.
    Safe edge compression is the new part; this finishing operation is reused.
    """
    def __init__(self,K,d,subset_cap=100000,vertex_cap=2000):
        self.K=K;self.d=d;self.core=K.support();h=len(self.core)
        require(2**h<=subset_cap,'residual face enumeration cap')
        self.vertices=[frozenset([i]) for i in range(K.n) if i not in self.core]
        self.core_start=len(self.vertices)
        for size in range(1,min(d,h)+1):
            for T in combinations(sorted(self.core),size):
                if K.ask(T):self.vertices.append(frozenset(T))
        require(len(self.vertices)<=vertex_cap,'refined vertex cap')
        self.index={S:i for i,S in enumerate(self.vertices)};self.cache={}
    def ask(self,S):
        S=frozenset(S)
        require(all(type(i)is int and 0<=i<len(self.vertices) for i in S),'bad refined vertex')
        if S in self.cache:return self.cache[S]
        parts=[self.vertices[i] for i in S if i>=self.core_start]
        good=all(A<=B or B<=A for A,B in combinations(parts,2))
        ans=good and self.K.ask(frozenset().union(*(self.vertices[i] for i in S)))
        self.cache[S]=ans;return ans
    def lift(self,F,common):
        ans={self.index[frozenset([i])] for i in F-self.core};P=frozenset()
        for i in sorted(F&self.core&common)+sorted((F&self.core)-common):
            P=P|{i};ans.add(self.index[P])
        require(len(ans)==self.d and self.ask(ans),'invalid residual endpoint lift')
        return frozenset(ans)
    def carrier(self,F):
        require(len(F)==self.d and self.ask(F),'not a refined maximal face')
        C=frozenset().union(*(self.vertices[i] for i in F))
        require(len(C)==self.d and self.K.ask(C),'residual carrier has wrong rank')
        return C


def lift_pair(F,H,steps):
    """Compatible endpoint lifts preserve a refined face covering original common labels."""
    for s in steps:
        E=frozenset(s['edge']);z=s['new_label'];oldF,oldH=F,H
        if E<=oldF:
            drop=max(E-oldH) if E-oldH else max(E)
            F=(oldF-{drop})|{z}
        if E<=oldH:
            drop=max(E-oldF) if E-oldF else max(E)
            H=(oldH-{drop})|{z}
    return F,H


def collapse(F,steps,stages,d):
    require(len(F)==d and stages[-1].ask(F),'invalid terminal facet')
    for j in reversed(range(len(steps))):
        E=frozenset(steps[j]['edge']);z=steps[j]['new_label']
        if z in F: F=(F-{z})|E
        require(len(F)==d and stages[j].ask(F),'stellar carrier is not a full old face')
    return F


def route(K,F,H,d,subset_cap=100000,vertex_cap=2000):
    require(len(F)==len(H)==d and K.ask(F) and K.ask(H),'invalid original endpoint faces')
    stages,steps,summary=compress(K)
    R=ResidualRefinement(stages[-1],d,subset_cap,vertex_cap)
    U,V=lift_pair(F,H,steps);X,Y=R.lift(U,U&V),R.lift(V,U&V)
    M=len(R.vertices);require(M>=d,'invalid refined dimension')
    alg=old.Segment(M,d,R,max(1,M-d),(4*d+4)*(max(1,M-d)+1))
    fine=alg.between(X&Y,X,Y)
    fine_ledger=old.ledger(fine,M,d)
    require(fine_ledger['nonrevisiting'] and len(fine)-1<=M-d,'flag segment count failed')
    path=[];mid=[]
    for X in fine:
        Q=R.carrier(X);mid.append(Q);C=collapse(Q,steps,stages,d)
        if not path or path[-1]!=C:path.append(C)
    require(path[0]==F and path[-1]==H,'carrier endpoints changed')
    require(all(F&H<=Q for Q in path),'lost common ORIGINAL facet')
    # Check adjacency at EVERY intermediate subdivision, not just final output.
    walks=mid[:]
    for j in reversed(range(len(steps))):
        E=frozenset(steps[j]['edge']);z=steps[j]['new_label']
        walks=[(Q-{z})|E if z in Q else Q for Q in walks]
        require(all(len(Q)==d and stages[j].ask(Q) for Q in walks),'bad intermediate carrier')
        require(all(A==B or len(A&B)==d-1 for A,B in zip(walks,walks[1:])),
                'stellar carrier maps an edge to a chord')
    require(all(len(A&B)==d-1 for A,B in zip(path,path[1:])),'original carrier nonedge')
    report={**summary,'refined_vertices':M,'residual_nonempty_faces':len(R.vertices)-R.core_start,
       'refined_edges':len(fine)-1,'original_edges':len(path)-1,
       'stationary_carrier_steps':len(fine)-len(path),'global_original_edge_bound':M-d,
       'coarse_refinement_bound':K.n-d+len(steps)+2**len(R.core)-len(R.core)-1,
       'original_reentries':old.ledger(path,K.n,d)['reentry_debt'],
       'common_original_facets_preserved':sorted(F&H),'visited_refined_links':len(alg.graphs),
       'refined_membership_queries':len(R.cache)}
    packet={'steps':steps,'residual_vertices':[sorted(S) for S in R.vertices],
       'refined_path':[sorted(S) for S in fine],'original_path':[sorted(S) for S in path]}
    return packet,report,path


def audit_original(A,b,packets,path):
    V={}
    for p in packets:
        q={'point':[old.rat(z) for z in p['point']],'active':p['active'],
           'directions':[[old.rat(z) for z in v] for v in p['directions']]}
        x,J,D=old.basis.audit_basis(A,b,q);F=frozenset(J)
        require(F not in V,'duplicate original basis');V[F]=(tuple(x),J,D)
    require(set(V)==set(path),'original bases missing or unrelated')
    for F,H in zip(path,path[1:]):
        require(len(F&H)==len(A[0])-1,'not an original facet exchange')
        x,J,D=V[F];y,_,_=V[H];col=J.index(next(iter(F-H)))
        alpha,_=old.basis.maximal_step(A,b,x,D[col])
        require(alpha>0 and tuple(a+alpha*b for a,b in zip(x,D[col]))==y,'not a maximal ORIGINAL edge')
    return V


def construct(data,classification_cap=500000,residual_cap=100000,vertex_cap=2000):
    A,b,u,v=old.parse(data);m,d=len(A),len(u)
    pu,pv=old.basis.basis_packet(A,b,u),old.basis.basis_packet(A,b,v)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    O=old.Discovery(A,b,u,v,20000,1000000)
    K,work=classify(m,d,O,classification_cap)
    packet,summary,path=route(K,F,H,d,residual_cap,vertex_cap)
    bases={}
    for C in path:
        if C not in bases:
            p=old.basis.basis_packet(A,b,O.point(C))
            require(frozenset(p['active'])==C,'original carrier not simple');bases[C]=p
    cert={'format':'defect-incidence-compression-v1','problem_sha256':old.input_hash(A,b,u,v),
       'limits':{'classification':classification_cap,'residual':residual_cap,'vertices':vertex_cap},
       'boundedness':O.bounds,'minimal_nonfaces':[sorted(S) for S in K.missing],
       'refinement':packet,'vertices':list(bases.values()),'intersections':list(O.cache.values())}
    verified=verify(data,serial(cert))
    return {'certificate':serial(cert),'verified':verified,
        'discovery':{**work,'LP_maximizations':O.lp_calls,'internal_LP_pivots':O.solver.pivots},
        'scope':'Counted same-dimensional flag refinement; classical flag theorem, not new Lean/platform verification.'}


def verify(data,c):
    A,b,u,v=old.parse(data);m,d=len(A),len(u)
    require(c['format']=='defect-incidence-compression-v1' and c['problem_sha256']==old.input_hash(A,b,u,v),
            'changed original input')
    old.audit_bounds(A,b,c['boundedness']);O=old.Certified(A,b,c['intersections'])
    K,work=classify(m,d,O,c['limits']['classification'])
    require(c['minimal_nonfaces']==[sorted(S) for S in K.missing],'incomplete original defect list')
    F=frozenset(old.basis.active_rows(A,b,u));H=frozenset(old.basis.active_rows(A,b,v))
    p,r,path=route(K,F,H,d,c['limits']['residual'],c['limits']['vertices'])
    require(p==c['refinement'],'wrong safe schedule, final registry, or flag path')
    V=audit_original(A,b,c['vertices'],path)
    require(V[F][0]==u and V[H][0]==v,'original endpoints changed')
    return {'status':'PASS','dimension':d,'original_facets':m,**r,
       'original_intersection_certificates':len(O.cache),
       'scope':'Exact complete classification and original-edge audit; discovery can be exponential; Python is not Lean-verified.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',type=Path)
    p.add_argument('--classification-cap',type=int,default=500000)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data,a.classification_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as e:
        p.exit(2,f'No completed incidence-compression route: {e}\n')
if __name__=='__main__':main()
