#!/usr/bin/env python3
"""Exact maximal removal of a supplied k-simplex from original H-inequalities.

Only the k translation variables are eliminated. All positive circuits of the
auxiliary matrix have support <=k+1. A complete finite circuit list and original
row Farkas multipliers prove GLOBAL Minkowski equality; a primal sharpness point
proves maximality. This is not a circuit-walk algorithm: output edges elsewhere
are ordinary polytope edges. Enumeration is polynomial only for fixed k.
"""
from __future__ import annotations
import argparse, hashlib, json
from itertools import combinations
from math import comb
from pathlib import Path
from fractions import Fraction as Q
from exact_farkas_lp import ExactLP, parse, rat, serial, dot, require, verify_dual, feasible_point, problem_hash

def rref(rows, columns):
    a=[list(map(rat,r)) for r in rows];piv=[];i=0
    for j in range(columns):
        p=next((s for s in range(i,len(a)) if a[s][j]),None)
        if p is None:continue
        a[i],a[p]=a[p],a[i];q=a[i][j];a[i]=[x/q for x in a[i]]
        for s in range(len(a)):
            if s!=i and a[s][j]:
                q=a[s][j];a[s]=[x-q*y for x,y in zip(a[s],a[i])]
        piv.append(j);i+=1
        if i==len(a):break
    return a,piv

def nullspace(rows,n):
    a,piv=rref(rows,n);out=[]
    for j in range(n):
        if j in piv:continue
        v=[Q(0)]*n;v[j]=1
        for row,i in zip(a,piv):v[i]=-row[j]
        out.append(tuple(v))
    return out

def rank(rows,n): return len(rref(rows,n)[1])

def positive_circuits(C,k,cap=2000000):
    """Exhaust supports. No claimed completeness after a combinatorial cap."""
    n=len(C);active=[i for i,r in enumerate(C) if any(r)]
    zero=[i for i,r in enumerate(C) if not any(r)]
    bound=len(zero)+sum(comb(len(active),r) for r in range(1,min(k+1,len(active))+1))
    require(type(cap)is int and cap>0 and bound<=cap,'positive-circuit enumeration cap; no completeness claim')
    out=[((i,),(Q(1),)) for i in zero]
    for size in range(1,min(k+1,len(active))+1):
        for I in combinations(active,size):
            ker=nullspace([[C[i][j] for i in I] for j in range(k)],size)
            if len(ker)!=1:continue
            v=ker[0]
            if all(x>0 for x in v):pass
            elif all(x<0 for x in v):v=tuple(-x for x in v)
            else:continue
            v=tuple(x/v[0] for x in v)
            require(all(sum((v[a]*C[i][j] for a,i in enumerate(I)),Q(0))==0 for j in range(k)),'bad annihilation')
            out.append((I,v))
    return sorted(out),bound

class SimplexModel:
    def __init__(self,A,b,generators):
        self.A,self.b=parse(A,b);self.d=len(self.A[0]);self.m=len(self.A)
        self.G=tuple(tuple(map(rat,g)) for g in generators);self.k=len(self.G)
        require(1<=self.k<=self.d and all(len(g)==self.d for g in self.G),'invalid simplex rank/shape')
        require(rank(self.G,self.d)==self.k,'simplex generators are not independent')
        self.proj=tuple(tuple(dot(a,g) for g in self.G) for a in self.A)
        self.support=tuple(max((Q(0),)+r) for r in self.proj)
        self.C=tuple(tuple(-v for v in row) for row in self.proj)+tuple(
            tuple(-Q(i==j) for j in range(self.k)) for i in range(self.k))+((Q(1),)*self.k,)
        self.hash=hashlib.sha256(json.dumps(serial({'A':self.A,'b':self.b,'simplex_generators':self.G}),
            sort_keys=True,separators=(',',':')).encode()).hexdigest()
    def ray(self,I,w):
        lam=[Q(0)]*self.m;gamma=Q(0)
        for i,x in zip(I,w):
            if i<self.m:lam[i]=x
            elif i==self.m+self.k:gamma=x
        c=tuple(sum((v*a[j] for v,a in zip(lam,self.A)),Q(0)) for j in range(self.d))
        C=dot(lam,self.b);demand=dot(lam,self.support)-gamma
        return c,C,demand,lam

def extract(A,b,generators,seed=None,pivot_cap=20000,circuit_cap=2000000):
    P=SimplexModel(A,b,generators);x=feasible_point(P.A,P.b,seed,pivot_cap)
    rays,examined=positive_circuits(P.C,P.k,circuit_cap)
    needed=[(I,w,P.ray(I,w)) for I,w in rays if P.ray(I,w)[2]>0]
    require(needed,'no finite simplex capacity constraint; unsupported infinite-capacity case')
    lp=ExactLP(P.A,P.b,x,pivot_cap);proofs=[];cache={};best=None
    for I,w,(c,C,den,lam) in needed:
        if best is not None and best[0]==0:
            dual=[[i,str(v)] for i,v in enumerate(lam) if v]
            value=C
        else:
            norm=max(map(abs,c),default=Q(0)) or Q(1);key=tuple(v/norm for v in c)
            if key not in cache:cache[key]=lp.maximize(key)
            sol=cache[key];value=rat(sol['value'])*norm
            dual=[[i,str(rat(v)*norm)] for i,v in sol['dual']]
            t=(C-value)/den
            require(t>=0,'negative capacity from feasible input')
            if best is None or t<best[0]:best=(t,I,w,sol['point'])
        proofs.append({'support':list(I),'ray':serial(w),'dual':dual})
    t,I,w,sharp=best
    cert=serial({'problem_sha256':P.hash,'simplex_generators':P.G,'capacity':t,'removed':t,
        'positive_circuit_count':len(rays),'supports_examined':examined,
        'demanding_circuit_proofs':proofs,'sharp_support':I,'sharp_ray':w,'sharp_point':sharp})
    out=verify(A,b,generators,cert,circuit_cap)
    return {'certificate':cert,'verified':out,'lp_calls':lp.calls,'lp_pivots':lp.pivots}

def verify(A,b,generators,cert,circuit_cap=2000000):
    """No LP or decomposition search. Re-enumerates ALL small circuit supports."""
    P=SimplexModel(A,b,generators)
    require(cert['problem_sha256']==P.hash and cert['simplex_generators']==serial(P.G),'changed input or simplex')
    t,s=rat(cert['capacity']),rat(cert['removed']);require(0<=s<=t,'invalid capacity/removal')
    rays,examined=positive_circuits(P.C,P.k,circuit_cap)
    require(type(cert['positive_circuit_count'])is int and cert['positive_circuit_count']==len(rays),'wrong ray count')
    require(type(cert['supports_examined'])is int and cert['supports_examined']==examined,'wrong completeness count')
    demanding={I:w for I,w in rays if P.ray(I,w)[2]>0};seen=set()
    for proof in cert['demanding_circuit_proofs']:
        I=tuple(proof['support']);w=tuple(map(rat,proof['ray']))
        require(all(type(i)is int for i in I) and I in demanding and I not in seen and w==demanding[I],'missing/forged/repeated circuit')
        seen.add(I);c,C,den,_=P.ray(I,w)
        upper=verify_dual(P.A,P.b,c,proof['dual'])
        require(upper<=C-t*den,'global equality certificate too weak')
    require(seen==set(demanding),'uncertified positive-demand obstruction')
    I=tuple(cert['sharp_support']);w=tuple(map(rat,cert['sharp_ray']))
    require(I in demanding and w==demanding[I],'invalid sharp ray')
    x=tuple(map(rat,cert['sharp_point']))
    require(len(x)==P.d and all(dot(a,x)<=b for a,b in zip(P.A,P.b)),'infeasible sharp point')
    c,C,den,_=P.ray(I,w)
    require(C-dot(c,x)==t*den,'maximality not sharp')
    return serial({'status':'PASS','ambient_dimension':P.d,'simplex_dimension':P.k,'original_rows':P.m,
        'auxiliary_rows':len(P.C),'circuit_supports_examined':examined,'positive_circuits':len(rays),
        'positive_demand_circuits':len(demanding),'capacity':t,'removed':s,
        'eroded_rhs':[b-s*h for b,h in zip(P.b,P.support)],
        'scope':'Exact global simplex-summand equality and maximality; finite verification, not Lean/platform acceptance.'})

def decompose_point(A,b,generators,amount,x):
    """Construct a point's split; its finite inequalities are easy to recheck."""
    P=SimplexModel(A,b,generators);t=rat(amount);x=tuple(map(rat,x))
    require(len(x)==P.d and t>=0 and all(dot(a,x)<=z for a,z in zip(P.A,P.b)),'invalid point/removal')
    rhs=tuple(z-dot(a,x)-t*h for a,z,h in zip(P.A,P.b,P.support))+(Q(0),)*P.k+(t,)
    lam=feasible_point(P.C,rhs)
    p=tuple(x[j]-sum((v*g[j] for v,g in zip(lam,P.G)),Q(0)) for j in range(P.d))
    require(all(v>=0 for v in lam) and sum(lam)<=t and all(dot(a,p)<=z-t*h for a,z,h in zip(P.A,P.b,P.support)),
            'invalid decomposition')
    return serial({'core_point':p,'simplex_coefficients':lam})

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    try:
        data=json.loads(args.input.read_text())
        out=verify(data['A'],data['b'],data['simplex_generators'],json.loads(args.certificate.read_text())) if args.certificate else extract(
            data['A'],data['b'],data['simplex_generators'],data.get('start'))
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:
        ap.exit(2,f'No simplex certificate: {e}\n')
if __name__=='__main__':main()
