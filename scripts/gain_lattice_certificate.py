#!/usr/bin/env python3
"""Exact gain-lattice certificates and sparse basis inverses.

The matrix may have arbitrary signs and rational gains with <=2 nonzero entries
per row. A given rational base q>1 certifies cycle magnitudes that are integer
powers of q, AFTER removing arbitrary tree/coordinate scales. Integer potential
balancing is exact; a negative-cycle witness proves the returned integer radius
optimal. No cycle, basis, or vertex enumeration is used for this certificate.
The global inverse bound is a structural theorem, not an observed-basis maximum.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from math import gcd
import hashlib, json
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok: raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int, str) or isinstance(x, Q), 'exact rational data required; floats/bools rejected')
    return Q(x)


def dot(a, b):
    require(len(a) == len(b), 'vector shape mismatch')
    return sum((x*y for x, y in zip(a,b) if x and y), Q(0))


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x


def parse_rows(raw):
    require(isinstance(raw,(list,tuple)) and raw and raw[0], 'positive matrix shape required')
    A=[tuple(map(rat,row)) for row in raw]; d=len(A[0])
    require(all(len(row)==d and sum(bool(x) for x in row)<=2 for row in A), 'ragged or more-than-two-variable row')
    return A


def gain_kernel(rows,d):
    """Exact homogeneous kernel: one weighted component per unpinned gain tree.
    A unary equation OR any inconsistent signed gain cycle pins its component.
    Inconsistency here means a zero homogeneous parameter, not infeasibility.
    """
    rows=[tuple(map(rat,a)) for a in rows]
    G=[[] for _ in range(d)]; pins=set()
    for r,a in enumerate(rows):
        require(len(a)==d, 'kernel row shape')
        nz=[i for i,x in enumerate(a) if x]; require(len(nz)<=2, 'dense kernel row')
        if len(nz)==1: pins.add(nz[0])
        if len(nz)==2:
            i,j=nz; t=-a[i]/a[j]
            G[i].append((j,t,r)); G[j].append((i,1/t,r))
    weights={}; components=[]; kernel=[]
    for root in range(d):
        if root in weights: continue
        weights[root]=Q(1); todo=[root]; nodes=[]; pinned=False; conflicts=[]
        while todo:
            i=todo.pop();nodes.append(i);pinned |= i in pins
            for j,t,r in G[i]:
                wanted=t*weights[i]
                if j not in weights: weights[j]=wanted;todo.append(j)
                elif weights[j]!=wanted: pinned=True;conflicts.append(r)
        nodes.sort()
        components.append({'nodes':nodes,'weights':[weights[i] for i in nodes],
                           'pinned':bool(pinned),'conflicting_rows':sorted(set(conflicts))})
        if not pinned:
            ns=set(nodes); g=tuple(weights[i] if i in ns else Q(0) for i in range(d))
            require(all(dot(a,g)==0 for a in rows), 'invalid kernel witness')
            kernel.append(g)
    return {'rank':d-len(kernel),'kernel':kernel,'components':components}


def gain_inverse(rows):
    """Each inverse column is the normalized kernel after deleting one row.
    This works for arbitrary rational gains; no good-conditioning claim is
    inferred merely from successful inversion.
    """
    rows=[tuple(map(rat,a)) for a in rows]
    d=len(rows); require(all(len(a)==d for a in rows), 'inverse needs square rows')
    cols=[];witnesses=[]
    for j in range(d):
        ker=gain_kernel(rows[:j]+rows[j+1:],d)['kernel']
        require(len(ker)==1, 'singular basis')
        g=ker[0]; den=dot(rows[j],g); require(den!=0, 'singular basis')
        col=tuple(x/den for x in g)
        require(all(dot(a,col)==int(i==j) for i,a in enumerate(rows)), 'inverse equation failed')
        cols.append(col); witnesses.append({'row':j,'generator':g,'denominator':den})
    return tuple(tuple(cols[j][i] for j in range(d)) for i in range(d)),witnesses


def exact_power(x,q):
    """Find k with x=q^k without integer factorization or floating logarithms."""
    require(x>0 and q>1, 'positive power/base required')
    if x==1: return 0
    negative=x<1; y=1/x if negative else x
    # If y=q^k in lowest terms, numerator(y)=numerator(q)^k >= 2^k.
    lo,hi=0,y.numerator.bit_length()
    while lo<=hi:
        k=(lo+hi)//2; z=q**k
        if z==y: return -k if negative else k
        if z<y: lo=k+1
        else: hi=k-1
    raise ValueError('cycle holonomy is not an integer power of the supplied base')


def support_edges(A):
    out=[]
    for r,a in enumerate(A):
        nz=[i for i,v in enumerate(a) if v]
        if len(nz)==2:
            i,j=nz;out.append((r,i,j,abs(a[i]/a[j])))
    return out


def tree_normalize(A,q):
    d=len(A[0]);G=[[]for _ in range(d)]
    for r,i,j,g in support_edges(A):G[i].append((j,g));G[j].append((i,1/g))
    s=[None]*d
    for root in range(d):
        if s[root] is not None:continue
        s[root]=Q(1);todo=[root]
        while todo:
            i=todo.pop()
            for j,g in G[i]:
                if s[j] is None:s[j]=s[i]*g;todo.append(j)
    E=[(r,i,j,exact_power(g*s[i]/s[j],q))for r,i,j,g in support_edges(A)]
    return s,E


def feasible_radius(d,E,R):
    """Difference constraints p_j-p_i in [ell-R,ell+R], Bellman--Ford."""
    arcs=[]
    for r,i,j,k in E:arcs.extend([(i,j,k+R,r),(j,i,-k+R,r)])
    p=[0]*d;pred=[None]*d;changed=None
    for _ in range(d):
        changed=None
        for k,(i,j,w,r) in enumerate(arcs):
            if p[j]>p[i]+w:p[j]=p[i]+w;pred[j]=k;changed=j
        if changed is None:return p,None
    v=changed
    for _ in range(d):v=arcs[pred[v]][0]
    start=v;cycle=[]
    while True:
        a=arcs[pred[v]];cycle.append({'row':a[3],'from':a[0],'to':a[1]});v=a[0]
        if v==start:break
        require(len(cycle)<=d, 'negative-cycle extraction failed')
    cycle.reverse();return None,cycle


def cycle_gcd(d,E):
    G=[[]for _ in range(d)]
    for _,i,j,k in E:G[i].append((j,k));G[j].append((i,-k))
    p=[None]*d
    for root in range(d):
        if p[root] is not None:continue
        p[root]=0;todo=[root]
        while todo:
            i=todo.pop()
            for j,k in G[i]:
                if p[j] is None:p[j]=p[i]+k;todo.append(j)
    g=0
    for _,i,j,k in E:g=gcd(g,abs(k+p[i]-p[j]))
    return g


def input_hash(A):
    return hashlib.sha256(json.dumps(serial(A),separators=(',',':')).encode()).hexdigest()


def certify(Araw,qraw):
    A=parse_rows(Araw);q=rat(qraw);require(q>1,'gain base must exceed one');d=len(A[0])
    s,E=tree_normalize(A,q);lo=0;hi=max((abs(k)for *_,k in E),default=0)
    while lo<hi:
        mid=(lo+hi)//2;p,_=feasible_radius(d,E,mid)
        if p is None:lo=mid+1
        else:hi=mid
    R=lo;p,_=feasible_radius(d,E,R)
    _,cycle=feasible_radius(d,E,R-1) if R else (None,None)
    diagonal=[x*q**k for x,k in zip(s,p)]
    exponents=[None]*len(A)
    for r,i,j,k in E:exponents[r]=k+p[i]-p[j]
    g=cycle_gcd(d,[(r,i,j,exponents[r])for r,i,j,_ in E])
    T=sum(sorted((abs(k)for k in exponents if k is not None),reverse=True)[:d-1])
    Gamma=q**T;eta=1-q**(-g) if g else Q(1);U=Gamma/eta
    cert={'matrix_sha256':input_hash(A),'base':q,'diagonal':diagonal,'exponents':exponents,
          'integer_radius':R,'cycle_gcd':g,'smaller_radius_negative_cycle':cycle or [],
          'path_exponent_budget':T,'path_product_bound':Gamma,'cycle_gap_bound':eta,'inverse_entry_bound':U}
    cert=serial(cert);return {'certificate':cert,'verified':verify(Araw,cert)}


def verify(Araw,cert):
    """Validate a finite certificate, not the radius-search algorithm's answer."""
    A=parse_rows(Araw);d=len(A[0]);q=rat(cert['base']);s=list(map(rat,cert['diagonal']))
    require(cert['matrix_sha256']==input_hash(A),'matrix identity changed')
    require(q>1 and len(s)==d and all(t>0 for t in s),'invalid positive base/scaling')
    R=cert['integer_radius'];require(type(R)is int and R>=0,'invalid radius')
    ex=cert['exponents'];require(len(ex)==len(A),'row occurrence count changed')
    E=[];normalized=[]
    for r,a in enumerate(A):
        b=tuple(x*t for x,t in zip(a,s));M=max(map(abs,b),default=Q(0)) or Q(1)
        normalized.append(tuple(x/M for x in b));nz=[i for i,x in enumerate(b)if x]
        if len(nz)<2:require(ex[r]is None,'spurious unary/zero exponent')
        else:
            i,j=nz;k=ex[r];require(type(k)is int and abs(k)<=R,'invalid bounded exponent')
            require(abs(b[i]/b[j])==q**k,'incorrect original-row gain identity')
            E.append((r,i,j,k))
    g=cycle_gcd(d,E);require(type(cert['cycle_gcd'])is int and cert['cycle_gcd']==g,'false cycle lattice gcd')
    cycle=cert['smaller_radius_negative_cycle']
    if R:
        require(isinstance(cycle,list)and cycle,'missing lower-radius obstruction')
        lookup={r:(i,j,k)for r,i,j,k in E};total=0
        for t,arc in enumerate(cycle):
            r=arc['row'];i=arc['from'];j=arc['to']
            require(all(type(x)is int for x in (r,i,j))and r in lookup,'invalid cycle row')
            a,b,k=lookup[r];require((i,j)in ((a,b),(b,a)),'cycle endpoints not row support')
            require(j==cycle[(t+1)%len(cycle)]['from'],'broken lower-bound cycle')
            total+=(k if i==a else -k)+R-1
        require(total<0,'cycle does not refute radius R-1')
    else:require(not cycle,'unneeded radius-zero negative cycle')
    T=sum(sorted((abs(k)for *_,k in E),reverse=True)[:d-1])
    require(type(cert['path_exponent_budget'])is int and cert['path_exponent_budget']==T,'false path exponent budget')
    Gamma=q**T;eta=1-q**(-g)if g else Q(1);U=Gamma/eta
    for key,val in [('path_product_bound',Gamma),('cycle_gap_bound',eta),('inverse_entry_bound',U)]:
        require(rat(cert[key])==val,'false '+key)
    safe=R>0 and U<=6*d*R
    return {'status':'PASS','dimension':d,'rows':len(A),'full_row_rank':gain_kernel(normalized,d)['rank'],
            'integer_gauge_radius':R,'path_exponent_budget':T,'absolute_cycle_gcd':g,'genuinely_magnitude_unbalanced':g>0,
            'inverse_entry_bound':str(U),'relative_separation_squared_lower':str(1/(2*d*U**2)),
            'quartic_regime_certified':safe,'quartic_safe_bound':360*R**2*d**4 if safe else None,
            'calibrated_base':bool(R and q==1+Q(1,d*R)),
            'scope':'Exact global gain-lattice certificate. Analytic diameter consequence uses the stated external normal-cone theorem, not a Lean verdict.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());result=certify(data['A'],data['gain_base'])
        text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError)as e:p.exit(2,f'No gain certificate: {e}\n')
if __name__=='__main__':main()
