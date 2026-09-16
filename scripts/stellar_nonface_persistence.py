#!/usr/bin/env python3
"""Minimal-nonface ancestry under forward stellar subdivisions.

Research/certificate code, not Lean verification. All faces of size >=2 may be
subdivided. A sequence with inverse moves is deliberately outside this theorem.
The original #261 complex representation and edge operation are reused.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import comb, prod
from pathlib import Path
import argparse, json
import defect_incidence_compression as base

require=base.require


def label_set(raw,n):
    require(isinstance(raw,(list,tuple,set,frozenset)) and
            all(type(i)is int and 0<=i<n for i in raw),'invalid labels')
    require(len(raw)==len(set(raw)), 'duplicate labels')
    return frozenset(raw)


def stellar_face(K,face):
    E=label_set(face,K.n)
    require(len(E)>=2 and K.ask(E),'subdivision requires a face of size >=2')
    z=K.n
    J=base.Complex(z+1,base.minimal([E]+[N for N in K.missing if not E<=N]+
                                  [(N-E)|{z} for N in K.missing if N&E]))
    if len(E)==2:
        require(J.missing==base.stellar(K,E).missing,'old edge formula changed')
    return J


def descendant(N,E,z):
    return (N-E)|{z} if E<=N else N


def audit_step(K,E,J):
    E=label_set(E,K.n)
    require(len(E)>=2 and K.ask(E) and J.n==K.n+1,'invalid stellar step')
    expected=stellar_face(K,E)
    require(J.missing==expected.missing,'wrong full minimal-nonface update')
    images=[descendant(N,E,K.n) for N in K.missing]
    require(len(images)==len(set(images)),'old nonface descendants collided')
    require(all(N in J.missing for N in images),'descendant is not minimal')
    require(E in J.missing and E not in images,'fresh missing face lost')
    require(len(J.missing)>=len(K.missing)+1,'total nonface count decreased')
    return images


def lower_bound_vertices(m,q):
    """Integer lower bound from q+(M-m)<=C(M,2), with M>=m.
    q may be a CERTIFIED SUBFAMILY size; completeness is unnecessary.
    """
    require(type(m)is int and type(q)is int and m>=2 and q>=0,'invalid size')
    good=lambda M:comb(M,2)>=q+M-m
    lo=m;hi=m
    while not good(hi):hi*=2
    while lo<hi:
        mid=(lo+hi)//2
        if good(mid):hi=mid
        else:lo=mid+1
    return lo


def ancestry(K,faces):
    """Track every original nonface and every mandatory born face.
    Original roots additionally preserve their union of original carriers.
    """
    m=K.n;initial=list(K.missing);roots=list(initial)
    carriers=[frozenset([i]) for i in range(m)];trace=[]
    for face in faces:
        E=label_set(face,K.n);J=stellar_face(K,E);audit_step(K,E,J)
        z=K.n;carriers.append(frozenset().union(*(carriers[i] for i in E)))
        roots=[descendant(N,E,z) for N in roots]+[E]
        require(len(roots)==len(set(roots)) and all(N in J.missing for N in roots),
                'ancestry injection failed')
        for N,T in zip(initial,roots):
            require(frozenset().union(*(carriers[i] for i in T))==N,
                    'original carrier union changed')
        trace.append({'face':sorted(E),'new_vertex':z,'minimal_before':len(K.missing),
                      'minimal_after':len(J.missing),'tracked_roots':len(roots)})
        K=J
    flag=not K.high()
    require(not flag or all(len(N)==2 for N in roots),'flag root did not become pair')
    if flag:require(K.n>=lower_bound_vertices(m,len(initial)),'flag lower bound failed')
    return {'initial_vertices':m,'initial_minimal_nonfaces':len(initial),'steps':trace,
            'final_vertices':K.n,'final_minimal_nonfaces':len(K.missing),'flag':flag,
            'final_tracked_descendants':[sorted(N) for N in roots],
            'original_carriers':[sorted(N) for N in carriers],
            'universal_completion_vertex_lower_bound':lower_bound_vertices(m,len(initial))}


def verify_ancestry(packet):
    require(packet['format']=='stellar-nonface-ancestry-v1','wrong format')
    K=base.Complex(packet['n'],packet['minimal_nonfaces'])
    r=ancestry(K,packet['subdivide_faces'])
    require(r==packet['report'],'ancestry report mismatch')
    return r


def polynomial(roots,squared=False):
    c=[1]
    for r in roots:
        for _ in range(2 if squared else 1):
            out=[0]*(len(c)+1)
            for i,x in enumerate(c):out[i]-=r*x;out[i+1]+=x
            c=out
    return c


def evaluate(c,t):
    y=0
    for a in reversed(c):y=y*t+a
    return y


def moment_rows(k):
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;d=2*k
    mean=[Q(sum(t**j for t in range(m)),m) for j in range(1,d+1)]
    return [[Q(t**j)-mean[j-1] for j in range(1,d+1)] for t in range(m)]


def support_certificate(k,S):
    """For every |S|<=k, product (t-s)^2 exposes exactly those moment labels."""
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;S=label_set(S,m)
    require(0<len(S)<=k,'support set too large')
    c=polynomial(sorted(S),True);values=[evaluate(c,t) for t in range(m)]
    h=Q(sum(values),m);require(h>0,'zero normalizing value')
    x=[-Q(c[j] if j<len(c) else 0)/h for j in range(1,2*k+1)]
    return {'k':k,'labels':sorted(S),'coefficients':c,'point':[str(t) for t in x]}


def verify_support(c,A=None):
    k=c['k'];require(type(k)is int and k>=2,'invalid dimension parameter')
    m=4*k+1;S=label_set(c['labels'],m)
    require(0<len(S)<=k,'invalid support size')
    p=c['coefficients'];require(all(type(z)is int for z in p) and len(p)<=2*k+1,'inexact polynomial')
    values=[evaluate(p,t) for t in range(m)]
    require(all(v>=0 and (v==0)==(t in S) for t,v in enumerate(values)),
            'polynomial does not expose exactly supplied labels')
    h=Q(sum(values),m);require(h>0,'zero support normalization')
    x=list(map(Q,c['point']));require(len(x)==2*k,'bad H point')
    require(x==[-Q(p[j] if j<len(p) else 0)/h for j in range(1,2*k+1)],'H point not bound')
    if A is not None:
        require(len(A)==m,'wrong row table')
        for i,a in enumerate(A):
            v=sum(u*w for u,w in zip(a,x))
            require(v<=1 and (v==1)==(i in S),'original-H support check failed')
    return True


def nonface_certificate(k,N):
    """Alternating affine circuit plus an exact Vandermonde rank witness.
    Every immediate proper subset is <=k and has the support proof above.
    """
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;N=label_set(N,m)
    require(len(N)==k+1 and all(i%2==1 for i in N),'not a parity nonface')
    odd=sorted(N);even=[odd[0]-1]+[x+1 for x in odd]
    z=sorted(odd+even)
    w=[Q(1,prod(t-s for s in z if s!=t)) for t in z]
    scale=sum(x for x in w if x>0)
    return {'k':k,'nonface':odd,'separators':even,
            'parameters':z,'weights':[str(x/scale) for x in w]}


def verify_nonface(c,A=None):
    k=c['k'];require(type(k)is int and k>=2,'invalid dimension parameter')
    m=4*k+1;N=label_set(c['nonface'],m);Y=label_set(c['separators'],m)
    z=c['parameters'];w=list(map(Q,c['weights']))
    require(len(N)==k+1 and all(i%2 for i in N),'wrong parity nonface')
    require(len(Y)==k+2 and not N&Y and z==sorted(N|Y) and len(w)==len(z),'wrong alternating circuit')
    require(all((t in Y and a>0) or (t in N and a<0) for t,a in zip(z,w)), 'wrong circuit signs')
    require(sum(a for a in w if a>0)==1 and sum(a for a in w if a<0)==-1,'unnormalized Radon weights')
    for j in range(2*k+1):
        require(sum(a*t**j for a,t in zip(w,z))==0,'false affine moment identity')
    # Any first d+1 points are affinely independent: determinant of their
    # augmented moment matrix is exactly this nonzero Vandermonde product.
    require(prod(b-a for a,b in combinations(z[:2*k+1],2))!=0,'zero Vandermonde determinant')
    if A is not None:
        for j in range(2*k):require(sum(a*A[t][j] for a,t in zip(w,z))==0,'unbound H-row relation')
    # If N were simultaneously tight, positive Radon weights force Y tight.
    # A nonconstant support hyperplane cannot contain these d+1 independent
    # points. Minimality follows from the universal squared-polynomial proof.
    return True


def family_bound(k):
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;d=2*k;q=comb(2*k,k+1);M=lower_bound_vertices(m,q)
    return {'k':k,'original_dimension':d,'original_facets':m,
            'certified_minimal_nonface_subfamily':q,'required_final_flag_vertices':M,
            'required_forward_subdivisions':M-m,
            'minimum_global_M_minus_d_certificate':M-d,
            'published_exact_original_diameter':d,
            'diameter_source':'Maksimenko 2009, DOI 10.4213/dm1054; not proved by this lower-bound code',
            'full_high_dimensional_graph_enumerated':False}



def facet_certificate(k,F):
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;F=label_set(F,m);require(len(F)==2*k,'wrong facet cardinality')
    c=polynomial(sorted(F));vals=[evaluate(c,t) for t in range(m)]
    if all(v<=0 for v in vals):c=[-v for v in c];vals=[-v for v in vals]
    require(all(v>=0 and (v==0)==(i in F) for i,v in enumerate(vals)),
            'not an original moment-polytope facet')
    h=Q(sum(vals),m);require(h>0,'zero facet normalization')
    return {'k':k,'labels':sorted(F),'coefficients':c,
            'point':[str(-Q(c[j])/h) for j in range(1,2*k+1)]}


def verify_facet(c):
    k=c['k'];require(type(k)is int and k>=2,'invalid dimension parameter')
    m=4*k+1;F=label_set(c['labels'],m);p=c['coefficients']
    require(len(F)==2*k and len(p)==2*k+1 and all(type(a)is int for a in p),
            'invalid facet polynomial')
    vals=[evaluate(p,t) for t in range(m)]
    require(all(v>=0 and (v==0)==(i in F) for i,v in enumerate(vals)),
            'false supporting facet polynomial')
    h=Q(sum(vals),m);require(h>0,'support hyperplane contains interior mean')
    require(list(map(Q,c['point']))==[-Q(p[j])/h for j in range(1,2*k+1)],
            'wrong original-H vertex')
    # Distinct roots give affine independence. The supporting polynomial is
    # nonzero at the interior mean, so the d centered row normals are linearly
    # independent. Consequently this is a SIMPLE original vertex, not a chord.
    require(prod(b-a for a,b in combinations(sorted(F),2))!=0,'rank failure')
    return True


def domino_route(k,F,H):
    """Classical cyclic-facet combinatorics, used as a direct polynomial control.
    A common absent label cuts the cycle. Shift packed domino blocks LEFT from the first unfinished position, then
    RIGHT from the last unfinished position. No refined complex.
    """
    require(type(k)is int and k>=2,'k>=2 required')
    m=4*k+1;F=label_set(F,m);H=label_set(H,m)
    verify_facet(facet_certificate(k,F));verify_facet(facet_certificate(k,H))
    cut=min(set(range(m))-(F|H));order=[(cut+1+j)%m for j in range(m-1)]
    pos={x:j for j,x in enumerate(order)}
    def starts(S):
        a=sorted(pos[x] for x in S)
        require(len(a)==2*k and all(a[2*j+1]==a[2*j]+1 for j in range(k)),
                'Gale-even facet did not split into path dominoes')
        return [a[2*j] for j in range(k)]
    a,b=starts(F),starts(H);path=[sorted(F)];block_moves=[]
    initial_work=sum(abs(x-y) for x,y in zip(a,b))
    for direction in (-1,1):
        while True:
            need=[i for i in range(k) if (a[i]>b[i] if direction<0 else a[i]<b[i])]
            if not need:break
            if direction<0:
                left=min(need);right=left
                while right+1<k and a[right+1]==a[right]+2 and a[right+1]>b[right+1]:right+=1
            else:
                right=max(need);left=right
                while left>0 and a[left-1]+2==a[left] and a[left-1]<b[left-1]:left-=1
            before=sum(abs(x-y) for x,y in zip(a,b))
            for i in range(left,right+1):a[i]+=direction
            require(a[0]>=0 and a[-1]+1<m-1 and
                    all(a[j]+2<=a[j+1] for j in range(k-1)), 'overlapping dominoes')
            require(sum(abs(x-y) for x,y in zip(a,b))==before-(right-left+1),
                    'block shift did not reduce coordinate distance')
            T={order[x] for t in a for x in (t,t+1)}
            require(len(T)==2*k and len(T&set(path[-1]))==2*k-1,'not one original-edge exchange')
            path.append(sorted(T));block_moves.append({'direction':direction,'first':left,'last':right})
    require(set(path[-1])==H,'wrong final endpoint')
    L=len(path)-1;require(L<=initial_work<=2*k*k,'direct quadratic route count failed')
    return {'format':'moment-domino-route-v1','k':k,'start':sorted(F),'target':sorted(H),
            'cut':cut,'active_path':path,'edges':L,'proved_route_bound':2*k*k,
            'initial_domino_distance':initial_work,'block_moves':block_moves}


def verify_domino_route(c):
    """Replay supplied block moves; no choice of route or complete graph search."""
    require(c['format']=='moment-domino-route-v1','wrong route format')
    k=c['k'];require(type(k)is int and k>=2,'invalid dimension parameter')
    m=4*k+1;path=c['active_path']
    require(type(c['edges'])is int and path and len(path)-1==c['edges'],'edge count mismatch')
    require(path[0]==c['start'] and path[-1]==c['target'],'endpoints changed')
    require(c['proved_route_bound']==2*k*k and c['edges']<=2*k*k,'false route bound')
    cut=c['cut']
    require(type(cut)is int and 0<=cut<m and all(cut not in F for F in path),'false common absent label')
    order=[(cut+1+j)%m for j in range(m-1)];pos={x:j for j,x in enumerate(order)}
    def starts(F):
        verify_facet(facet_certificate(k,F))
        x=sorted(pos[i] for i in F)
        require(all(x[2*j+1]==x[2*j]+1 for j in range(k)),'invalid domino decomposition')
        return x[::2]
    a,b=starts(path[0]),starts(path[-1]);initial=sum(abs(x-y) for x,y in zip(a,b))
    require(c['initial_domino_distance']==initial<=2*k*k,'false initial progress measure')
    require(len(c['block_moves'])==c['edges'],'missing or extra block moves')
    for next_face,move in zip(path[1:],c['block_moves']):
        sign,left,right=move['direction'],move['first'],move['last']
        require(all(type(v)is int for v in (sign,left,right)) and sign in(-1,1)
                and 0<=left<=right<k,'invalid block-move labels')
        require(all(a[i+1]==a[i]+2 for i in range(left,right)),'selected block not packed')
        require(all(a[i]>b[i] if sign<0 else a[i]<b[i] for i in range(left,right+1)),
                'block move points away from target')
        before=sum(abs(x-y) for x,y in zip(a,b))
        for i in range(left,right+1):a[i]+=sign
        require(a==starts(next_face),'supplied block move differs from next vertex')
        require(sum(abs(x-y) for x,y in zip(a,b))==before-(right-left+1),'progress identity failed')
    require(a==b and c['edges']<=initial,'block sequence did not finish within its progress budget')
    require(all(len(set(F)&set(H))==2*k-1 for F,H in zip(path,path[1:])),
            'consecutive original vertices are not adjacent')
    return {'status':'PASS','edges':c['edges'],'original_vertices_checked':len(path),
            'scope':'exact original facet polynomials, supplied block progress and adjacency, not full graph enumeration'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--k',type=int,default=8)
    p.add_argument('--verify',type=Path);a=p.parse_args()
    result=verify_ancestry(json.loads(a.verify.read_text())) if a.verify else family_bound(a.k)
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
