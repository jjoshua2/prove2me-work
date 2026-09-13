#!/usr/bin/env python3
"""Maximally remove a supplied finite-vertex Minkowski summand from original H-data.

A candidate with k+1 distinct listed points is parameterized by k barycentric
variables (affine independence is not required). Enumerate the positive circuits
of the m+k+1 feasibility normals, with supports of size <=k+1. Each restrictive
circuit gives one original-H LP and an exact nonnegative row-combination proof.
All circuits, including nonrestrictive ones, are independently reconstructed by
verification. No original vertex enumeration or proposed residual is supplied.

The candidate SHAPE is an input, not discovered universally. Enumeration is
polynomial in m for fixed k, exponential when k grows. Exact Bland simplex has
no asserted polynomial pivot bound. An enumeration/pivot cap never produces a
partial equality certificate. Candidate points are translated by the first point;
reported residuals use this explicitly documented origin convention.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from itertools import combinations
from functools import lru_cache
from math import comb
from pathlib import Path
from exact_farkas_lp import (ExactLP, parse, rat, serial, dot, require,
    feasible_point, verify_dual, problem_hash)


def candidate(raw, d):
    require(isinstance(raw,(list,tuple)) and raw, 'nonempty candidate point list required')
    pts=[]
    for v in raw:
        p=tuple(map(rat,v)); require(len(p)==d,'candidate point dimension')
        if p not in pts: pts.append(p)
    origin=pts[0]
    G=tuple(tuple(x-y for x,y in zip(p,origin)) for p in pts[1:])
    require(G,'candidate must have at least two distinct points')
    return origin,G


def positive_circuit(rows):
    """Unique positive dependence of this minimal support, normalized to sum one."""
    s=len(rows); k=len(rows[0]); a=[[row[j] for row in rows] for j in range(k)]
    piv=[]; r=0
    for j in range(s):
        p=next((i for i in range(r,k) if a[i][j]),None)
        if p is None: continue
        a[r],a[p]=a[p],a[r]; t=a[r][j]; a[r]=[x/t for x in a[r]]
        for i in range(k):
            if i!=r and a[i][j]:
                t=a[i][j]; a[i]=[x-t*y for x,y in zip(a[i],a[r])]
        piv.append(j); r+=1
        if r==k: break
    if s-r!=1: return None
    free=next(j for j in range(s) if j not in piv); w=[Q(0)]*s; w[free]=Q(1)
    for row,j in zip(a,piv): w[j]=-row[free]
    if any(x<=0 for x in w): return None  # free coordinate fixes the orientation
    total=sum(w); w=tuple(x/total for x in w)
    require(all(sum(x*row[j] for x,row in zip(w,rows))==0 for j in range(k)),
            'internal positive-kernel identity failed')
    return w


@lru_cache(maxsize=128)
def enumerate_circuits(C, cap=300000):
    n=len(C); k=len(C[0]); active=[i for i,row in enumerate(C) if any(row)]
    zero=[i for i,row in enumerate(C) if not any(row)]
    # A zero normal is a singleton circuit. No larger minimal support can
    # contain it, so excluding those supersets is exact, not a heuristic.
    work=len(zero)+sum(comb(len(active),s) for s in range(1,min(k+1,len(active))+1))
    require(type(cap)is int and cap>=work,'circuit enumeration cap; no complete certificate')
    out=[((i,),(Q(1),)) for i in zero]
    for s in range(1,min(k+1,len(active))+1):
        for I in combinations(active,s):
            w=positive_circuit([C[i] for i in I])
            if w is not None: out.append((I,w))
    out.sort(key=lambda x:(len(x[0]),x[0]))
    return tuple(out),work


class Data:
    def __init__(self,A,b,points,cap=300000):
        self.A,self.b=parse(A,b);self.d=len(self.A[0]);self.m=len(self.A)
        self.origin,self.G=candidate(points,self.d);self.k=len(self.G)
        self.H=tuple(max([Q(0)]+[dot(a,g) for g in self.G]) for a in self.A)
        self.C=tuple(tuple(-dot(a,g) for g in self.G) for a in self.A)+\
            tuple(tuple(-Q(i==j) for j in range(self.k)) for i in range(self.k))+\
            ((Q(1),)*self.k,)
        self.circuits,self.subsets=enumerate_circuits(self.C,cap)
        canonical={'A':self.A,'b':self.b,'candidate_origin':self.origin,'candidate_offsets':self.G}
        self.digest=hashlib.sha256(json.dumps(serial(canonical),sort_keys=True,separators=(',',':')).encode()).hexdigest()
        self.constraints=[]
        for I,w in self.circuits:
            v=tuple(sum((t*self.A[i][j] for i,t in zip(I,w) if i<self.m),Q(0)) for j in range(self.d))
            b0=sum((t*self.b[i] for i,t in zip(I,w) if i<self.m),Q(0))
            gamma=sum((t*self.H[i] if i<self.m else -t if i==self.m+self.k else Q(0)
                       for i,t in zip(I,w)),Q(0))
            if gamma>0:self.constraints.append((I,w,v,b0,gamma))

    def rhs(self,tau): return tuple(b-tau*h for b,h in zip(self.b,self.H))

    def allocation_rhs(self,x,tau):
        return tuple(b-dot(a,x)-tau*h for a,b,h in zip(self.A,self.b,self.H))+\
            (Q(0),)*self.k+(tau,)


def discover(A,b,points,seed=None,amount=None,subset_cap=300000,pivot_cap=20000):
    P=Data(A,b,points,subset_cap);x=feasible_point(P.A,P.b,seed,pivot_cap)
    require(P.constraints,'candidate has unbounded removable scale; finite-capacity mode only')
    lp=ExactLP(P.A,P.b,x,pivot_cap);cache={};proofs=[];sharp=None
    for I,w,v,b0,gamma in P.constraints:
        scale=max(map(abs,v),default=Q(0)) or Q(1);key=tuple(z/scale for z in v)
        if key not in cache:cache[key]=lp.maximize(key)
        opt=cache[key];upper=rat(opt['value'])*scale;mu=(b0-upper)/gamma
        require(mu>=0,'negative capacity from a feasible original point')
        dual=[[i,serial(rat(z)*scale)] for i,z in opt['dual']]
        proofs.append({'support':list(I),'circuit_weights':serial(w),'dual':dual})
        if sharp is None or mu<sharp[0]: sharp=(mu,I,opt['point'])
    capacity,I,point=sharp;tau=capacity if amount is None else rat(amount)
    require(0<=tau<=capacity,'removal outside maximal certified range')
    rhs=P.rhs(tau);core=feasible_point(P.A,rhs,pivot_cap=pivot_cap)
    cert=serial({'problem_sha256':P.digest,'capacity':capacity,'removed':tau,
        'proofs':proofs,'sharp_support':list(I),'sharp_point':point,'core_seed':core,
        'enumerated_supports':P.subsets,'positive_circuits':len(P.circuits)})
    report=verify(A,b,points,cert,subset_cap)
    return {'certificate':cert,'verified':report,'core_b':serial(rhs),
        'scaled_candidate':serial([(Q(0),)*P.d]+[tuple(tau*z for z in g) for g in P.G]),
        'discovery':{'lp_calls':lp.calls,'lp_pivots':lp.pivots,'supports_tested':P.subsets}}


def verify(A,b,points,cert,subset_cap=300000):
    """No LP or path search. Complete support enumeration and rational identities only."""
    P=Data(A,b,points,subset_cap)
    require(cert['problem_sha256']==P.digest,'changed original H-data or candidate shape')
    mu,tau=rat(cert['capacity']),rat(cert['removed']);require(0<=tau<=mu,'invalid removal/capacity')
    require(type(cert['enumerated_supports'])is int and cert['enumerated_supports']==P.subsets,'false enumeration count')
    require(type(cert['positive_circuits'])is int and cert['positive_circuits']==len(P.circuits),'false circuit count')
    wanted={I:(w,v,b0,gamma) for I,w,v,b0,gamma in P.constraints};seen=set()
    for proof in cert['proofs']:
        require(isinstance(proof['support'],list) and all(type(i)is int for i in proof['support']),'bad circuit indices')
        I=tuple(proof['support']);require(I in wanted and I not in seen,'unneeded/duplicate/invalid circuit support')
        seen.add(I);w,v,b0,gamma=wanted[I]
        require(tuple(map(rat,proof['circuit_weights']))==w,'incorrect positive dependence')
        upper=verify_dual(P.A,P.b,v,proof['dual'])
        require(upper<=b0-mu*gamma,'global circuit inequality is insufficient')
    require(seen==set(wanted),'missing a restrictive positive circuit')
    require(isinstance(cert['sharp_support'],list) and all(type(i)is int for i in cert['sharp_support']),'bad sharpness indices')
    I=tuple(cert['sharp_support']);require(I in wanted,'sharpness must use a restrictive circuit')
    w,v,b0,gamma=wanted[I];x=tuple(map(rat,cert['sharp_point']))
    require(len(x)==P.d and all(dot(a,x)<=z for a,z in zip(P.A,P.b)),'infeasible sharpness point')
    require(b0-dot(v,x)==mu*gamma,'upper capacity witness is not sharp')
    core=tuple(map(rat,cert['core_seed']))
    require(len(core)==P.d and all(dot(a,core)<=z for a,z in zip(P.A,P.rhs(tau))),'empty or false residual witness')
    # A small positive scale above mu makes this circuit's total feasibility
    # RHS strictly negative at x. That proves failure for every possible core.
    return {'status':'PASS','ambient_dimension':P.d,'original_rows':P.m,'candidate_points':P.k+1,
        'barycentric_variables':P.k,'support_subsets_checked':P.subsets,'positive_circuits':len(P.circuits),
        'restrictive_circuit_proofs':len(wanted),'capacity':str(mu),'removed':str(tau),
        'sharp_circuit_size':len(I),'global_minkowski_equality':True,'maximality_against_any_residual':True,
        'scope':'Exact original-H finite-summand certificate using complete positive circuits. Candidate shape is supplied; no Lean or platform acceptance.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--subset-cap',type=int,default=300000);a=p.parse_args()
    try:
        d=json.loads(a.input.read_text())
        out=verify(d['A'],d['b'],d['candidate_vertices'],json.loads(a.certificate.read_text()),a.subset_cap) if a.certificate else \
            discover(d['A'],d['b'],d['candidate_vertices'],d.get('start'),subset_cap=a.subset_cap)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,ZeroDivisionError,OSError) as e:p.exit(2,f'No finite summand certificate: {e}\n')
if __name__=='__main__':main()
