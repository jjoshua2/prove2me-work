#!/usr/bin/env python3
"""Exact original-row witnesses for genuine edges of a linear image.

The producer uses rational elimination; audit() uses only arithmetic identities.
The exposed preimage need not be one-dimensional, bounded, or have vertex lifts.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int, str, Q), 'exact rational data required; floats/bools are refused')
    return Q(x)


def vector(x, n):
    require(type(x) in (list, tuple) and len(x) == n, 'wrong vector dimension')
    return [rat(y) for y in x]


def matrix(A, n):
    require(type(A) in (list, tuple), 'matrix must be a row list')
    return [vector(row, n) for row in A]


def dot(x, y):
    require(len(x) == len(y), 'dot dimension mismatch')
    return sum((a*b for a,b in zip(x,y)), Q(0))


def apply(A,x):
    return [dot(row,x) for row in A]


def audit(A,b,G,cert):
    """No rank calculation, vertex enumeration, LP or inverse in this auditor."""
    require(type(cert) is dict, 'certificate is not an object')
    require(set(cert) == {'x','y','rows','weights','normal','coordinate','residual',
                         'lower','upper','lower_eq','upper_eq'}, 'unexpected certificate fields')
    n=len(cert['x']); A=matrix(A,n); b=vector(b,len(A)); G=matrix(G,n)
    p=len(G); m=len(A)
    require(n>0 and p>0, 'nondegenerate edge needs positive dimensions')
    x=vector(cert['x'],n); y=vector(cert['y'],n)
    J=cert['rows']; require(type(J) in (list,tuple), 'bad selected rows')
    require(all(type(j) is int and 0<=j<m for j in J) and len(set(J))==len(J),'invalid/repeated selected rows')
    r=len(J); lam=vector(cert['weights'],r); f=vector(cert['normal'],p)
    phi=vector(cert['coordinate'],n); W=matrix(cert['residual'],p)
    require(len(W)==r,'wrong residual identity dimension')
    lo=vector(cert['lower'],m); up=vector(cert['upper'],m)
    gl=vector(cert['lower_eq'],r); gu=vector(cert['upper_eq'],r)
    ax=apply(A,x); ay=apply(A,y); u=apply(G,x); v=apply(G,y)
    delta=[vi-ui for ui,vi in zip(u,v)]
    require(any(delta),'image endpoints collapse')
    require(all(a<=bb for a,bb in zip(ax,b)) and all(a<=bb for a,bb in zip(ay,b)), 'infeasible source endpoint')
    require(all(ax[j]==b[j] and ay[j]==b[j] for j in J),'selected row not tight at both endpoints')
    require(all(t>0 for t in lam),'exposure weights must be strictly positive')
    require(all(t>=0 for t in lo+up),'negative inequality multiplier')
    require(dot(phi,y)-dot(phi,x)==1,'image coordinate is not normalized')
    checks=0
    for i in range(n):
        require(sum(f[l]*G[l][i] for l in range(p)) == sum(lam[j]*A[J[j]][i] for j in range(r)), 'false exposing-row identity')
        require(-phi[i] == sum(lo[j]*A[j][i] for j in range(m))+sum(gl[j]*A[J[j]][i] for j in range(r)), 'false lower endpoint identity')
        require(phi[i] == sum(up[j]*A[j][i] for j in range(m))+sum(gu[j]*A[J[j]][i] for j in range(r)), 'false upper endpoint identity')
        for l in range(p):
            require(G[l][i] == phi[i]*delta[l]+sum(A[J[j]][i]*W[j][l] for j in range(r)), 'image is not rank one modulo selected rows')
        checks+=3+p
    require(-dot(phi,x)==dot(lo,b)+sum(gl[j]*b[J[j]] for j in range(r)), 'lower witness is not sharp')
    require(dot(phi,y)==dot(up,b)+sum(gu[j]*b[J[j]] for j in range(r)), 'upper witness is not sharp')
    beta=sum(lam[j]*b[J[j]] for j in range(r))
    require(dot(f,u)==beta and dot(f,v)==beta,'inconsistent image support values')
    return {'status':'PASS','source_dimension':n,'image_ambient_dimension':p,
            'original_rows':m,'selected_rows':r,'column_identity_checks':checks,
            'image_start':u,'image_end':v,'support_value':beta}


def row_coefficients(rows,target):
    """Untrusted exact producer helper. All outputs are audited independently."""
    import sympy as sp
    if not rows:
        return [] if all(x==0 for x in target) else None
    M=sp.Matrix(rows).T
    R,pivots=M.row_join(sp.Matrix(target)).rref()
    s=len(rows)
    if s in pivots: return None
    c=[Q(0)]*s
    for i,pivot in enumerate(pivots): c[pivot]=Q(str(R[i,s]))
    require([sum(c[i]*rows[i][j] for i in range(s)) for j in range(len(target))]==list(target),'producer solve failed')
    return c


def independent_rows(rows):
    import sympy as sp
    return list(sp.Matrix(rows).T.rref()[1]) if rows else []


def strict_support_weights(A,J,target):
    if not J:
        require(all(x==0 for x in target),'no nonzero objective on empty selected rows')
        return []
    rank=len(independent_rows([A[j] for j in J]))
    for power in range(32):
        eps=Q(1,2**power)
        q=[target[i]-eps*sum(A[j][i] for j in J) for i in range(len(target))]
        for subset in combinations(range(len(J)),rank):
            rows=[A[J[j]] for j in subset]
            if len(independent_rows(rows))!=rank: continue
            c=row_coefficients(rows,q)
            if c is not None and all(x>=0 for x in c):
                weights=[eps]*len(J)
                for j,x in zip(subset,c): weights[j]+=x
                return weights
    raise ValueError('no strict exposure found within explicit producer cap')


def endpoint_certificate(A,b,J,point,target):
    jbasis=independent_rows([A[j] for j in J])
    base=[A[J[j]] for j in jbasis]
    active=[i for i in range(len(A)) if i not in J and dot(A[i],point)==b[i]]
    for size in range(min(len(target)-len(base),len(active))+1):
        for extra in combinations(active,size):
            c=row_coefficients(base+[A[i] for i in extra],target)
            if c is not None and all(x>=0 for x in c[len(base):]):
                mu=[Q(0)]*len(A); gamma=[Q(0)]*len(J)
                for j,x in zip(jbasis,c[:len(base)]):gamma[j]=x
                for i,x in zip(extra,c[len(base):]):mu[i]=x
                return mu,gamma
    raise ValueError('no endpoint certificate found')


def produce(A,b,G,J,x,y,f):
    n=len(x);A=matrix(A,n);b=vector(b,len(A));G=matrix(G,n)
    x=vector(x,n);y=vector(y,n);f=vector(f,len(G))
    u=apply(G,x);v=apply(G,y);delta=[q-p for p,q in zip(u,v)]
    require(any(delta),'collapsed projected endpoints')
    pivot=next(i for i,a in enumerate(delta) if a)
    phi=[a/delta[pivot] for a in G[pivot]]
    target=[sum(f[j]*G[j][i] for j in range(len(G))) for i in range(n)]
    lam=strict_support_weights(A,J,target)
    baseidx=independent_rows([A[j] for j in J]);base=[A[J[j]] for j in baseidx]
    W=[[Q(0)]*len(G) for _ in J]
    for l in range(len(G)):
        c=row_coefficients(base,[G[l][i]-delta[l]*phi[i] for i in range(n)])
        require(c is not None,'projected equality face has dimension greater than one')
        for j,a in zip(baseidx,c):W[j][l]=a
    lo,gl=endpoint_certificate(A,b,J,x,[-a for a in phi])
    up,gu=endpoint_certificate(A,b,J,y,phi)
    cert=dict(x=x,y=y,rows=list(J),weights=lam,normal=f,coordinate=phi,residual=W,
              lower=lo,upper=up,lower_eq=gl,upper_eq=gu)
    audit(A,b,G,cert)
    return cert


def jsonable(obj):
    if isinstance(obj,Q):return str(obj)
    if isinstance(obj,dict):return {k:jsonable(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)):return [jsonable(x) for x in obj]
    return obj
