#!/usr/bin/env python3
"""Exact finite affine-normalizer synthesis.

Uses rational equality elimination and strict Fourier--Motzkin feasibility.
No floating point solver, approximation tolerance, or unlabelled timeout is used.
The independent consumer checks witnesses and linear infeasibility certificates.
This implementation is not Lean-extracted and JSON decoding is not verified.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from typing import Sequence


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def dot(a, b):
    need(len(a) == len(b), 'dot dimension')
    return sum((Q(x)*Q(y) for x,y in zip(a,b)), Q(0))


def data(points, values, anchor=0):
    C=[tuple(map(Q,x)) for x in points]; s=list(map(Q,values))
    need(bool(C) and len(C)==len(s) and len(set(C))==len(C), 'nonempty distinct points required')
    d=len(C[0]); need(all(len(x)==d for x in C), 'mixed point dimensions')
    need(isinstance(anchor,int) and 0<=anchor<len(C), 'invalid anchor')
    u=C[anchor]; P=[tuple(xj-uj for xj,uj in zip(x,u)) for x in C]
    # Positive denominators preserve signs. Cross-sign pairs can never tie;
    # zero/zero equations are tautologies; reverse pairs are scalar duplicates.
    pairs=[(i,j) for i,j in combinations(range(len(C)),2) if s[i]*s[j]>0]
    eq=[(tuple(s[i]*P[j][k]-s[j]*P[i][k] for k in range(d)),s[j]-s[i]) for i,j in pairs]
    return C,s,P,pairs,eq


def eliminate_equalities(equations, d):
    """Return a particular solution + full kernel, or an exact left contradiction."""
    n=len(equations); M=[list(a)+[b] for a,b in equations]
    U=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
    piv=[]; row=0
    for col in range(d):
        k=next((i for i in range(row,n) if M[i][col]),None)
        if k is None: continue
        M[row],M[k]=M[k],M[row]; U[row],U[k]=U[k],U[row]
        v=M[row][col]; M[row]=[z/v for z in M[row]]; U[row]=[z/v for z in U[row]]
        for i in range(n):
            if i==row or not M[i][col]: continue
            v=M[i][col]; M[i]=[x-v*y for x,y in zip(M[i],M[row])]
            U[i]=[x-v*y for x,y in zip(U[i],U[row])]
        piv.append(col); row+=1
    for i in range(n):
        if not any(M[i][:d]) and M[i][d]:
            return {'kind':'inconsistent_equalities','dual':U[i]}
    x=[Q(0)]*d
    for i,j in enumerate(piv):x[j]=M[i][d]
    kernel=[]
    for j in range(d):
        if j in piv:continue
        v=[Q(0)]*d; v[j]=Q(1)
        for i,col in enumerate(piv):v[col]=-M[i][j]
        kernel.append(v)
    return {'particular':x,'kernel':kernel}


def strict_feasible(A, b, variable_count, row_cap=20000):
    """Solve A*z < b, or return λ>=0, λ!=0, λ*A=0, λ*b<=0."""
    n=len(b); rows=[(list(map(Q,a)),Q(rhs),[Q(int(i==j)) for j in range(n)])
                  for i,(a,rhs) in enumerate(zip(A,b))]
    stages=[]
    for k in range(variable_count,-1,-1):
        keep={}
        for a,rhs,weights in rows:
            nz=next((abs(t) for t in a if t),None)
            if nz is None:
                if rhs<=0:return {'dual':weights}
                continue
            a=tuple(t/nz for t in a); rhs/=nz; weights=[t/nz for t in weights]
            if a not in keep or rhs<keep[a][0]:keep[a]=(rhs,weights)
        rows=[(list(a),rhs,w) for a,(rhs,w) in sorted(keep.items())]
        if k==0:break
        need(len(rows)<=row_cap, 'Fourier--Motzkin row cap reached; NOT an exclusion')
        stages.append(rows)
        pos=[r for r in rows if r[0][-1]>0]; neg=[r for r in rows if r[0][-1]<0]
        new=[(a[:-1],rhs,w) for a,rhs,w in rows if a[-1]==0]
        need(len(pos)*len(neg)+len(new)<=row_cap,
             'Fourier--Motzkin cross-product cap reached; NOT an exclusion')
        for ap,bp,wp in pos:
            for an,bn,wn in neg:
                p=ap[-1];ncoef=-an[-1]
                new.append(([ap[j]/p+an[j]/ncoef for j in range(k-1)],bp/p+bn/ncoef,
                            [x/p+y/ncoef for x,y in zip(wp,wn)]))
        rows=new
    solution=[]
    for rows in reversed(stages):
        lows=[]; highs=[]
        for a,rhs,w in rows:
            if not a[-1]:continue
            endpoint=(rhs-dot(a[:-1],solution))/a[-1]
            (highs if a[-1]>0 else lows).append(endpoint)
        lo=max(lows) if lows else None; hi=min(highs) if highs else None
        if lo is not None and hi is not None:
            need(lo<hi,'strict interval collapse');value=(lo+hi)/2
        elif lo is not None:value=lo+1
        elif hi is not None:value=hi-1
        else:value=Q(0)
        solution.append(value)
    need(len(solution)==variable_count and all(dot(a,solution)<rhs for a,rhs in zip(A,b)),
         'producer returned invalid strict solution')
    return {'solution':solution}


def solve_system(P, equations, d):
    result=eliminate_equalities(equations,d)
    if result.get('kind')=='inconsistent_equalities':return result
    x=result['particular'];K=result['kernel'];r=len(K)
    constants=[Q(1)+dot(p,x) for p in P]
    # q=constant + sum(z_l * p.K_l)>0 iff -sum(...)<constant.
    A=[[-dot(p,v) for v in K] for p in P]
    sol=strict_feasible(A,constants,r)
    if 'dual' in sol:
        return {'kind':'infeasible_positive',**result,'dual':sol['dual']}
    D=[x[j]+sum((sol['solution'][l]*K[l][j] for l in range(r)),Q(0)) for j in range(d)]
    return {'kind':'positive','slope':D}


def optimize(points, values, anchor=0, system_cap=200000):
    C,s,P,pairs,eq=data(points,values,anchor);d=len(C[0]);records=[];best=None
    lower=len({(x>0)-(x<0) for x in s})
    candidate_count=sum(comb(len(pairs),k) for k in range(min(d,len(pairs))+1))
    for k in range(min(d,len(pairs))+1):
        for B in combinations(range(len(pairs)),k):
            need(len(records)<system_cap,'normalizer system cap reached; NOT an optimum/exclusion')
            cert=solve_system(P,[eq[i] for i in B],d)
            record={'basis':list(B),**cert}; records.append(record)
            if cert['kind']=='positive':
                D=cert['slope'];q=[1+dot(D,p) for p in P];ratios=[sx/qx for sx,qx in zip(s,q)]
                need(min(q)>0,'invalid producer denominator')
                record['values']=sorted(set(ratios));record['denominators']=q
                score=len(record['values'])
                if best is None or score<best[0]:best=(score,len(records)-1)
                if score==lower:
                    return {'mode':'sign_lower_bound','anchor':anchor,'pairs':pairs,
                            'candidate_systems':candidate_count,'sign_lower_bound':lower,
                            'best':best[1],'minimum':score,'records':records}
    need(best is not None,'empty base should be feasible')
    return {'mode':'exhaustive','anchor':anchor,'pairs':pairs,'candidate_systems':candidate_count,
            'sign_lower_bound':lower,'best':best[1],'minimum':best[0],'records':records}


def rank_independent(rows, d):
    """A separate SymPy rank computation for checking full nullspace certificates."""
    import sympy as sp
    return int(sp.Matrix(rows).rank()) if rows else 0


def verify_system(P, equations, d, c):
    kind=c['kind'];n=len(equations)
    if kind=='inconsistent_equalities':
        w=list(map(Q,c['dual']));need(len(w)==n,'equality dual length')
        need(all(sum((w[i]*equations[i][0][j] for i in range(n)),Q(0))==0 for j in range(d)),
             'false equality annihilator')
        need(sum((w[i]*equations[i][1] for i in range(n)),Q(0))!=0,'no equality contradiction')
        return None
    if kind=='positive':
        D=list(map(Q,c['slope']));need(len(D)==d,'slope dimension')
        need(all(dot(a,D)==b for a,b in equations),'equation not satisfied')
        need(all(1+dot(p,D)>0 for p in P),'nonpositive denominator')
        return D
    need(kind=='infeasible_positive','unknown certificate kind')
    x=list(map(Q,c['particular']));K=[list(map(Q,v)) for v in c['kernel']]
    need(len(x)==d and all(len(v)==d for v in K),'kernel dimension')
    need(all(dot(a,x)==b for a,b in equations),'wrong affine solution space')
    need(all(dot(a,v)==0 for a,b in equations for v in K),'kernel leaves equations')
    r=rank_independent([a for a,b in equations],d)
    need(len(K)==d-r and rank_independent(K,d)==len(K),'incomplete/dependent nullspace')
    w=list(map(Q,c['dual']));need(len(w)==len(P) and all(z>=0 for z in w) and any(w),'invalid positive dual')
    need(all(sum((lam*dot(p,v) for p,lam in zip(P,w)),Q(0))==0 for v in K),'dual does not annihilate motions')
    need(sum((lam*(1+dot(p,x)) for p,lam in zip(P,w)),Q(0))<=0,'dual does not exclude positivity')
    return None


def audit(points, values, output):
    C,s,P,pairs,eq=data(points,values,output['anchor']);d=len(C[0]);m=len(pairs)
    need([tuple(p) for p in output['pairs']]==pairs,'changed pair inventory')
    lower=len({(x>0)-(x<0) for x in s})
    need(output['sign_lower_bound']==lower,'false universal sign lower bound')
    expected_count=sum(comb(m,k) for k in range(min(d,m)+1))
    need(output['candidate_systems']==expected_count,'wrong candidate count')
    scores=[];seen=set();positive=exclusions=0
    for index,c in enumerate(output['records']):
        B=tuple(c['basis']);need(tuple(sorted(set(B)))==B and len(B)<=d and all(0<=i<m for i in B),'invalid basis')
        need(B not in seen,'repeated basis');seen.add(B)
        D=verify_system(P,[eq[i] for i in B],d,c)
        if D is None:scores.append(None);exclusions+=1;continue
        q=[1+dot(p,D) for p in P];vals=sorted({sv/qv for sv,qv in zip(s,q)})
        need(list(map(Q,c['denominators']))==q and list(map(Q,c['values']))==vals,'incorrect computed spectrum')
        scores.append(len(vals));positive+=1
    best=output['best'];need(isinstance(best,int) and 0<=best<len(scores) and scores[best] is not None,'bad best witness')
    need(output['minimum']==scores[best] and all(v is None or v>=scores[best] for v in scores),'nonminimum returned witness')
    if output['mode']=='sign_lower_bound':
        need(output['minimum']==lower,'early stop without universal lower bound')
    else:
        need(output['mode']=='exhaustive','unknown termination mode')
        # Re-enumerate the entire reduced finite catalogue independently.
        expected={B for k in range(min(d,m)+1) for B in combinations(range(m),k)}
        need(seen==expected,'incomplete catalogue claimed exhaustive')
    return {'systems':len(seen),'positive_systems':positive,'excluded_systems':exclusions,
            'mode':output['mode'],'minimum_values':output['minimum'],'raw_values':len(set(s))}


def encoded(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:encoded(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [encoded(v) for v in x]
    return x
