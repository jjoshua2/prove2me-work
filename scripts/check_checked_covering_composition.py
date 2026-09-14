#!/usr/bin/env python3
"""Exact original-row tests for the checked covering/Minkowski composition.
These computations are NOT Lean compilation or verification of Python itself.
"""
from fractions import Fraction as Q
from itertools import product, combinations
import sympy as sp
from pathlib import Path
from copy import deepcopy
import hashlib,json,random,time
from checked_circuit_catalogue import generate,audit
ROOT=Path(__file__).resolve().parents[1]

def require(ok, message):
    if not ok: raise ValueError(message)

def dot(x,y): return sum((a*b for a,b in zip(x,y)),Q(0))

def transpose(C,k): return [[Q(row[j]) for row in C] for j in range(k)]

def feasible(C,r,k):
    """Independent exact elimination, no rank or dual-catalogue calls."""
    require(len(C)==len(r) and all(len(a)==k for a in C),'bad primal shape')
    rows=[(tuple(Q(v) for v in a),Q(b)) for a,b in zip(C,r)]
    for _ in range(k):
        P=[(a,b) for a,b in rows if a[0]>0]
        N=[(a,b) for a,b in rows if a[0]<0]
        out=[(a[1:],b) for a,b in rows if a[0]==0]
        for a,b in P:
            for c,d in N:
                out.append((tuple(a[j]/a[0]-c[j]/c[0] for j in range(1,len(a))),b/a[0]-d/c[0]))
        # Normalize by a POSITIVE factor only. Identical LHS keeps the strictest RHS.
        best={}
        for a,b in out:
            s=next((abs(v) for v in a if v),Q(1))
            a=tuple(v/s for v in a);b/=s
            if not any(a) and b<0:return False
            if a not in best or b<best[a]:best[a]=b
        rows=list(best.items())
    return all(b>=0 for a,b in rows)

def cover(B,rho,k):
    require(len(B)==len(rho) and all(len(row)==k for row in B),'wrong budget dimensions')
    require(all(x>=0 for x in rho),'negative coverage multiplier')
    d=[sum(rho[q]*B[q][j] for q in range(len(B))) for j in range(k)]
    require(all(x>=1 for x in d),'coverage does not dominate total mass')
    return d

def vertices(A,b):
    d=len(A[0]) if A else 0
    if d==0:return [()] if all(x>=0 for x in b) else []
    out=set()
    for ids in combinations(range(len(A)),d):
        M=sp.Matrix([A[i] for i in ids])
        if M.det()==0:continue
        x=tuple(Q(str(v)) for v in M.inv()*sp.Matrix([b[i] for i in ids]))
        if all(dot(row,x)<=rhs for row,rhs in zip(A,b)):out.add(x)
    return sorted(out)

def support(A,b,c,V):
    val=max(dot(c,x) for x in V);x=next(x for x in V if dot(c,x)==val)
    m=len(A);d=len(c);active=[i for i in range(m) if dot(A[i],x)==b[i]]
    if not any(c):return [Q(0)]*m,x,val
    for l in range(1,d+1):
        for ids in combinations(active,l):
            M=sp.Matrix([A[i] for i in ids]).T
            R,piv=M.row_join(sp.Matrix(c)).rref()
            if l in piv or len(piv)!=l:continue
            alpha=[Q(0)]*m
            for p,i in enumerate(ids):alpha[i]=Q(str(R[p,l]))
            if all(v>=0 for v in alpha) and all(sum(alpha[i]*A[i][j] for i in range(m))==c[j] for j in range(d)):
                require(all(alpha[i]*(b[i]-dot(A[i],x))==0 for i in range(m)),'nonsharp dual')
                require(dot(alpha,b)==val,'support mismatch')
                return alpha,x,val
    raise ValueError('failed exact finite support witness search')

def serialize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serialize(v) for v in x]
    return x

def req(p,msg):
    if not p:raise ValueError(msg)
def bind(A,G,B,M,e):
    m=len(A);k=len(G);r=len(B);N=m+k+r
    req(sorted(e)==list(range(N)), 'row map is not a bijection')
    C=[[-dot(a,g) for g in G] for a in A]+[[-Q(i==j) for j in range(k)]for i in range(k)]+B
    req(len(M)==k and all(len(v)==N for v in M),'wrong matrix dimensions')
    for j in range(k):
        for i in range(N):req(M[j][e[i]]==C[i][j],'original allocation row identity failed')
    return C
def envelope(A,G,B,t,h,eta):
    req(len(eta)==len(A) and all(len(v)==len(B) for v in eta),'envelope dimension mismatch')
    for i,a in enumerate(A):
        req(all(v>=0 for v in eta[i]),'negative envelope multiplier')
        for j,g in enumerate(G):req(dot(a,g)<=sum(eta[i][q]*B[q][j]for q in range(len(B))),'false envelope column domination')
        req(dot(eta[i],t)<=h[i],'insufficient envelope value')
def sharp(A,b,lam,alpha,x):
    req(len(alpha)==len(A) and all(v>=0 for v in alpha),'bad original-row dual')
    req(all(dot(a,x)<=bi for a,bi in zip(A,b)),'support point infeasible')
    for j in range(len(x)):req(sum(lam[i]*A[i][j]for i in range(len(A)))==sum(alpha[i]*A[i][j]for i in range(len(A))),'objective coefficient mismatch')
    req(all(alpha[i]*(b[i]-dot(A[i],x))==0 for i in range(len(A))),'support value is not sharp')
def main():
    start=time.monotonic();rng=random.Random(234233)
    out={'status':'PASS','scope':'Exact rational regression, not Lean compilation','models':[],
         'row_permutations':0,'scalar_region_checks':0,'original_vertex_allocation_checks':0,
         'candidate_support_certificates':0,'sharp_support_certificates':0,'transported_kernel_and_rhs_checks':0}
    models=[]
    for name,A,b,blocks in [
        ('independent_segments_square',[[-1,0],[0,-1],[1,0],[0,1]],[0,0,1,1],[[[1,0]],[[0,1]]]),
        ('competing_triangle_square',[[1,0],[-1,0],[0,1],[0,-1],[1,1],[-1,-1]],[1]*6,[[[1,0],[0,1]],[[1,0],[0,1],[1,1]]]),
        ('empty_block_and_segment',[[-1],[1]],[0,1],[[],[[1]]]),
        ('dependent_generators',[[-1],[1]],[0,1],[[[1],[Q(1,2)]],[[1]]])]:
        G=[g for block in blocks for g in block];owner=[q for q,block in enumerate(blocks)for _ in block]
        B=[[Q(owner[j]==q)for j in range(len(G))]for q in range(len(blocks))]
        eta=[[max([Q(0)]+[dot(a,g)for g in block])for block in blocks]for a in A]
        models.append((name,A,b,G,B,[Q(1)]*len(blocks),eta))
    models += [
      ('overlapping_budgets_square',[[-1,0],[0,-1],[1,0],[0,1]],[0,0,1,1],[[1,0],[1,1],[0,1]],[[1,1,0],[0,1,1]],[1,1],[[0,0],[0,0],[1,0],[0,1]]),
      ('signed_budget_trapezoid',[[-1,0],[0,-1],[1,-1],[0,2]],[0,0,1,2],[[1,0],[0,1]],[[1,-1],[0,2]],[1,1],[[0,0],[0,0],[1,0],[0,1]]),
      ('zero_allocation_coordinates',[[-1],[1]],[0,1],[],[[]],[1],[[0],[0]])]
    for name,A,b,G,B,rho,eta in models:
        A=[[Q(v)for v in row]for row in A];G=[[Q(v)for v in row]for row in G];B=[[Q(v)for v in row]for row in B]
        b=list(map(Q,b));rho=list(map(Q,rho));eta=[[Q(v)for v in row]for row in eta]
        m,k,r=len(A),len(G),len(B);N=m+k+r;cover(B,rho,k);V=vertices(A,b)
        C=[[-dot(a,g)for g in G]for a in A]+[[-Q(i==j)for j in range(k)]for i in range(k)]+B
        baseline=None;lastcase=None
        for perm in range(2):
            e=list(range(N));rng.shuffle(e);Cp=[[Q(0)]*k for _ in range(N)]
            for i in range(N):Cp[e[i]]=C[i]
            M=transpose(Cp,k);req(bind(A,G,B,M,e)==C,'binding changed original system')
            tab=generate(M,N);res=audit(M,N,tab);out['row_permutations']+=1
            cs=[]
            for c in res['catalogue']:
                w=[Q(0)]*N
                for j,v in zip(c['support'],c['positive']):w[j]=Q(v)
                v=[w[e[i]]for i in range(N)];cs.append(v)
                req(all(dot(row,w)==0 for row in M),'emitted kernel not zero')
                req(all(sum(C[i][j]*v[i]for i in range(N))==0 for j in range(k)),'transported kernel failed')
            if baseline is not None:req(set(map(tuple,cs))==baseline,'row permutation changed catalogue')
            baseline=set(map(tuple,cs));witnesses=[]
            for c in cs:
                obj=[sum(c[i]*A[i][j]for i in range(m))for j in range(len(A[0]))]
                alpha,xstar,val=support(A,b,obj,V);sharp(A,b,c[:m],alpha,xstar)
                witnesses.append((c,alpha,xstar));out['sharp_support_certificates']+=1
            for t in product([Q(0),Q(1,2),Q(1),Q(3,2)],repeat=r):
                h=[dot(v,t)for v in eta];envelope(A,G,B,t,h,eta);out['candidate_support_certificates']+=m
                original=True
                for x in V:
                    rhs=[b[i]-dot(A[i],x)-h[i]for i in range(m)]+[Q(0)]*k+list(t)
                    # Entire primal system kept; independent Fourier--Motzkin eliminates variables.
                    original &= feasible(C,rhs,k);out['original_vertex_allocation_checks']+=1
                    rhsp=[Q(0)]*N
                    for i in range(N):rhsp[e[i]]=rhs[i]
                    for c,_,_ in witnesses:
                        wp=[Q(0)]*N
                        for i in range(N):wp[e[i]]=c[i]
                        req(dot(wp,rhsp)==dot(c,rhs),'RHS pairing transport failed')
                        out['transported_kernel_and_rhs_checks']+=1
                scalar=all(dot(c[:m],h)-dot(c[m+k:],t)<=dot(c[:m],b)-dot(alpha,b)for c,alpha,_ in witnesses)
                req(scalar==original,'whole-set/scalar equivalence failed');out['scalar_region_checks']+=1
                if name in ['independent_segments_square','overlapping_budgets_square']:req(scalar==(max(t)<=1),'rectangle mismatch')
                if name in ['competing_triangle_square','dependent_generators']:req(scalar==(sum(t)<=1),'simplex scale region mismatch')
                if name=='signed_budget_trapezoid':req(scalar==(t[0]<=1 and t[1]<=2),'signed trapezoid budget mismatch')
                if name=='empty_block_and_segment':req(scalar==(t[1]<=1),'empty block changed region')
                if name=='zero_allocation_coordinates':req(scalar,'zero allocation should give unchanged set')
            lastcase=(A,b,G,B,rho,eta,e,M,tab,witnesses)
        out['models'].append({'name':name,'dimension':len(A[0]),'allocation_coordinates':k,'budget_rows':r,
                              'original_vertices':len(V),'support_cells':res['support_cells'],'circuits':res['circuits']})
        if name=='signed_budget_trapezoid':signed=lastcase
        if name=='competing_triangle_square':hexcase=lastcase
    # Negative controls independently target the interface, not merely the producer.
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('forgery accepted: '+name)
    A,b,G,B,rho,eta,e,M,tab,wits=hexcase
    bad=deepcopy(tab);bad['catalogue'].pop();reject('omitted_emitted_obstruction',lambda:audit(M,len(e),bad))
    badM=deepcopy(M);badM[0][e[0]]+=1;reject('wrong_original_row',lambda:bind(A,G,B,badM,e))
    ep=e[:];ep[0]=ep[1];reject('nonbijective_row_map',lambda:bind(A,G,B,M,ep))
    ep=e[1:]+e[:1];reject('forgotten_rhs_row_permutation',lambda:bind(A,G,B,M,ep))
    t=[Q(1),Q(1)];h=[dot(v,t)for v in eta]
    badeta=deepcopy(eta);badeta[0][0]=-1;reject('negative_envelope_multiplier',lambda:envelope(A,G,B,t,h,badeta))
    badeta=[[Q(0)]*2 for _ in A];reject('missing_support_domination',lambda:envelope(A,G,B,t,h,badeta))
    badh=h[:];badh[0]-=1;reject('false_candidate_support_value',lambda:envelope(A,G,B,t,badh,eta))
    c,alpha,x=wits[0];bada=alpha[:];bada[0]=-1;reject('negative_original_support_multiplier',lambda:sharp(A,b,c[:len(A)],bada,x))
    reject('infeasible_support_point',lambda:sharp(A,b,c[:len(A)],alpha,[Q(99)]*len(x)))
    # A dual upper bound with wrong coefficients is not an exact maximum.
    bada=alpha[:];bada[0]+=1;reject('wrong_support_objective',lambda:sharp(A,b,c[:len(A)],bada,x))
    (ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True)
    fixture={'A':A,'b':b,'G':G,'B':B,'rho':rho,'eta':eta,'row_bijection':e,'matrix':M,'table':tab,
             'support_witnesses':[{'c':c,'alpha':aa,'xstar':xx}for c,aa,xx in wits]}
    (ROOT/'fixtures/checked_covering_hexagon.json').write_text(json.dumps(serialize(fixture),indent=2)+'\n')
    out['rejected']=rejected;out['rejected_count']=len(rejected);out['elapsed_seconds']=round(time.monotonic()-start,3)
    out['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [Path(__file__), ROOT/'scripts/checked_circuit_catalogue.py']}
    (ROOT/'research/CHECKED_COVERING_COMPOSITION_TESTS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
