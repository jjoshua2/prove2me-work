#!/usr/bin/env python3
"""Exact original-H simple-vertex pivots, with a search-free certificate auditor.

The two policies maximize normalized derivative or COMPLETED-edge gain. No
polynomial guarantee is claimed. Non-simple vertices and unbounded improving
rays are explicitly unsupported. The auditor uses no inverse/rank/LP routine.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse, hashlib, json


def require(ok, text):
    if not ok: raise ValueError(text)


def rat(v):
    require(type(v) in (int, str, Q), 'exact rational data required')
    return Q(v)


def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: serial(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)): return [serial(v) for v in x]
    return x


def dot(a,b):
    require(len(a)==len(b), 'dot shape')
    return sum((x*y for x,y in zip(a,b) if x and y), 0)


def invert(M):
    """Untrusted producer; every result is checked against the ORIGINAL rows."""
    n=len(M); R=[[Q(a) for a in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(M)]
    for j in range(n):
        p=next((i for i in range(j,n) if R[i][j]),None)
        require(p is not None, 'singular active matrix')
        R[j],R[p]=R[p],R[j]; q=R[j][j]; R[j]=[a/q for a in R[j]]
        for i in range(n):
            if i!=j and R[i][j]:
                q=R[i][j]; R[i]=[a-q*b for a,b in zip(R[i],R[j])]
    return [row[n:] for row in R]


def active_rows(A,b,x): return [i for i,a in enumerate(A) if dot(a,x)==b[i]]
def feasible(A,b,x): return all(dot(a,x)<=v for a,v in zip(A,b))


def basis_packet(A,b,x):
    J=active_rows(A,b,x); n=len(x)
    require(len(J)==n and feasible(A,b,x), 'requires a simple feasible vertex')
    R=invert([A[j] for j in J])
    return {'point':list(x), 'active':J, 'directions':[[-R[i][j] for i in range(n)] for j in range(n)]}


def audit_basis(A,b,c):
    n=len(A[0]); x=c['point']; J=c['active']; D=c['directions']
    require(len(x)==n and all(type(v) in (int,Q) for v in x), 'bad point')
    require(feasible(A,b,x), 'infeasible point')
    require(type(J)is list and len(J)==n and J==sorted(set(J)) and all(type(j)is int and 0<=j<len(A) for j in J), 'bad active list')
    require(J==active_rows(A,b,x), 'not exact simple active set')
    require(len(D)==n and all(len(v)==n and all(type(z) in (int,Q) for z in v) for v in D), 'bad inverse columns')
    for i,di in enumerate(D):
        for j,row in enumerate(J): require(dot(A[row],di)==-int(i==j), 'false original-row inverse identity')
    # T*D=-I proves all rays and the original vertex rank without search.
    return x,J,D


def maximal_step(A,b,x,r):
    ratios=[(Q(bi-dot(a,x),dot(a,r)),i) for i,(a,bi) in enumerate(zip(A,b)) if dot(a,r)>0]
    require(ratios, 'unbounded improving ray: no finite edge certificate')
    return min(ratios)


def completed_key(A,b,f,x,r):
    length,_=maximal_step(A,b,x,r)
    end=tuple(xx+length*rr for xx,rr in zip(x,r))
    # Endpoint-based tie breaking is unaffected by positive row rescaling.
    return (length*dot(f,r), end)


def make_step(A,b,f,basis,policy):
    x,J,D=audit_basis(A,b,basis); scores=[dot(f,r) for r in D]
    improving=[i for i,s in enumerate(scores) if s>0]
    require(improving,'no improving incident ray')
    if policy=='normalized': best=max(improving,key=lambda i:(scores[i],-i))
    elif policy=='full_gain':
        best=max(improving,key=lambda i:completed_key(A,b,f,x,D[i]))
    else: raise ValueError('unknown policy')
    length,blocker=maximal_step(A,b,x,D[best]); y=[xx+length*rr for xx,rr in zip(x,D[best])]
    return {'basis':basis,'selected':best,'length':length,'blocker':blocker,'to':y}


def audit_step(A,b,f,c,policy):
    x,J,D=audit_basis(A,b,c['basis']); n=len(x); i=c['selected']
    require(type(c['length']) in (int,Q) and type(c['blocker']) is int, 'inexact step data')
    require(len(c['to'])==n and all(type(v) in (int,Q) for v in c['to']), 'inexact endpoint')
    require(type(i)is int and 0<=i<n,'invalid selected ray')
    gains=[dot(f,r) for r in D]; require(gains[i]>0,'no strict objective progress')
    ell,k=maximal_step(A,b,x,D[i]); require(ell>0 and c['length']==ell and c['blocker']==k,'not maximal original step')
    require(c['to']==[xx+ell*rr for xx,rr in zip(x,D[i])] and feasible(A,b,c['to']),'incorrect endpoint')
    require(sum(dot(A[j],D[i]) for j in J)==-1,'height not one')
    eligible=[j for j,g in enumerate(gains) if g>0]
    if policy=='normalized':
        require(i==max(eligible,key=lambda j:(gains[j],-j)), 'not greatest normalized derivative')
        # These n nonnegative multipliers certify optimality over the WHOLE
        # normalized tangent slice: f = gain_i*h + sum(lambda_j*T_j).
        lam=[gains[i]-g for g in gains]
        require(all(w>=0 for w in lam),'negative tangent dual coefficient')
        h=[-sum(A[j][k] for j in J) for k in range(n)]
        for k in range(n): require(f[k]==gains[i]*h[k]+sum(lam[j]*A[J[j]][k] for j in range(n)),'false normalized optimum identity')
    elif policy=='full_gain':
        require(i==max(eligible,key=lambda j:completed_key(A,b,f,x,D[j])), 'not greatest completed-edge gain')
    else: raise ValueError('unknown policy')
    # All other original active rows stay tight. Their independent rank is n-1;
    # maximality and feasibility identify the entire edge, not an interior step.
    require(all(dot(A[j],c['to'])==b[j] for j in J if j!=J[i]), 'lost common facet')
    return c['to']


def audit_target(A,b,f,target):
    x,J,D=audit_basis(A,b,target); w=target['weights']
    require(len(w)==len(J) and all(type(v) in (int,Q) and v>0 for v in w),'strict target weights required')
    require(all(f[k]==sum(w[i]*A[j][k] for i,j in enumerate(J)) for k in range(len(x))),'target exposer not bound to original rows')
    # Positive exposing combination plus invertibility proves unique global max.
    return x


def construct(A,b,f,start,target,policy='full_gain',edge_cap=10000):
    audit_target(A,b,f,target); x=list(start); steps=[]
    while x!=target['point']:
        require(len(steps)<edge_cap,'route cap; no completed route')
        s=make_step(A,b,f,basis_packet(A,b,x),policy); steps.append(s);x=s['to']
    return {'policy':policy,'steps':steps}


def audit_route(A,b,f,start,target,c):
    end=audit_target(A,b,f,target); x=list(start); seen={tuple(x)}; least_gain=None
    for s in c['steps']:
        require(s['basis']['point']==x,'path discontinuity')
        y=audit_step(A,b,f,s,c['policy']); gain=dot(f,y)-dot(f,x)
        require(gain>0 and tuple(y) not in seen,'repeated/unimproving vertex')
        least_gain=gain if least_gain is None else min(least_gain,gain)
        x=y;seen.add(tuple(x))
    require(x==end,'wrong final endpoint')
    return {'status':'PASS','edges':len(c['steps']),'least_objective_gain':serial(least_gain),
            'original_rows':len(A),'dimension':len(start),'graph_supplied':False}


def decode_input(data):
    A=[[rat(x) for x in row] for row in data['A']];b=[rat(x) for x in data['b']]
    require(A and A[0] and len(A)==len(b) and all(len(a)==len(A[0]) for a in A),'matrix shape')
    f=[rat(x) for x in data['objective']];start=[rat(x) for x in data['start']]
    require(len(f)==len(start)==len(A[0]),'endpoint/objective shape')
    t=data['target'];target={'point':[rat(x) for x in t['point']], 'active':t['active'],
      'directions':[[rat(x) for x in r] for r in t['directions']], 'weights':[rat(x) for x in t['weights']]}
    return A,b,f,start,target


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--policy',choices=['normalized','full_gain'],default='full_gain');p.add_argument('--edge-cap',type=int,default=10000)
    a=p.parse_args()
    try:
        A,b,f,start,target=decode_input(json.loads(a.input.read_text()))
        route=construct(A,b,f,start,target,a.policy,a.edge_cap);report=audit_route(A,b,f,start,target,route)
        a.output.write_text(json.dumps(serial({'route':route,'verified':report}),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:p.exit(2,f'No certified completed route: {e}\n')

if __name__=='__main__':main()
