#!/usr/bin/env python3
"""Choose genuine improving IMAGE edges via a normalized tangent slice.

Input: original H-system A,b, image matrix G, and image endpoint vertices u,v.
No neighbor, ray, face, source vertex, or graph is supplied. Source lineality is
allowed. A bounded image is independently certified. The first-order slice is
optimized, with image-coordinate lexicographic tie breaking; the selected ray
is maximized over ALL lifts, not just one source line. Exact LP has explicit
caps, and neither the number of pivots nor route length is claimed polynomial.
The verifier checks finite primal/dual and column identities without an LP,
rank computation, kernel computation, or graph search.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from pathlib import Path
import sympy as sp
from exact_farkas_lp import (ExactLP, Unbounded, parse, rat, serial, dot,
    require, feasible_point, verify_dual, verify_optimum, dense_dual)


def vec(x,n):
    require(isinstance(x,(list,tuple)) and len(x)==n,'wrong vector dimension')
    return tuple(map(rat,x))
def im(G,x): return tuple(dot(g,x) for g in G)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def mul(t,x): return tuple(t*a for a in x)
def pull(G,c): return tuple(sum((c[j]*G[j][i] for j in range(len(G))),Q(0)) for i in range(len(G[0])))
def feasible(A,b,x): return all(dot(a,x)<=t for a,t in zip(A,b))
def fibre(A,b,G,u): return A+G+tuple(mul(-1,g) for g in G), b+u+mul(-1,u)
def hash_input(A,b,G,u,v):
    return hashlib.sha256(json.dumps(serial([A,b,G,u,v]),separators=(',',':')).encode()).hexdigest()
def read(data):
    A,b=parse(data['A'],data['b']);n=len(A[0]);G=tuple(vec(g,n) for g in data['G'])
    require(G,'empty image ambient space')
    return A,b,G,vec(data['u'],len(G)),vec(data['v'],len(G))


def row_repr(rows,target):
    """Untrusted exact producer. Returned identities are recomputed in audit."""
    if not rows:
        require(not any(target),'image point is not a vertex')
        return []
    M=sp.Matrix(rows).T;R,piv=M.row_join(sp.Matrix(target)).rref();s=len(rows)
    require(s not in piv,'image point is not a vertex')
    w=[Q(0)]*s
    for i,j in enumerate(piv):w[j]=Q(str(R[i,s]))
    return w


def discover_vertex(A,b,G,u,seed=None,cap=20000):
    """#247 fibre-dual construction at one image point, then a finite singleton
    test G=W A_J. Zero-slack LPs may be unbounded in the source fibre."""
    n=len(A[0]);m=len(A);p=len(G);C,d=fibre(A,b,G,u)
    x=feasible_point(C,d,seed,cap);lp=ExactLP(C,d,x,cap);points=[x];J=[];duals=[]
    for j,a in enumerate(A):
        try:
            out=lp.maximize(mul(-1,a));slack=b[j]+rat(out['value'])
            require(slack>=0,'negative feasible slack')
            if slack==0:J.append(j);duals.append({'row':j,'dual':out['dual']})
            else:points.append(vec(out['point'],n))
        except Unbounded as exc:
            points.append(add(exc.point,exc.direction))
    x=tuple(sum(y[i] for y in points)/len(points) for i in range(n))
    weights=[Q(1)]*len(J);normal=[Q(0)]*p
    for item in duals:
        z=dense_dual(item['dual'],len(C))
        for i,j in enumerate(J):weights[i]+=z[j]
        for l in range(p):normal[l]-=z[m+l]-z[m+p+l]
    W=[row_repr([A[j] for j in J],g) for g in G]
    cert=serial({'anchor':x,'rows':J,'zero_duals':duals,'normal':normal,'weights':weights,'image_rows':W})
    verify_vertex(A,b,G,u,cert)
    return cert


def verify_vertex(A,b,G,u,c):
    """Finite original-row certificate: no optimizer or elimination used."""
    n=len(A[0]);m=len(A);p=len(G);x=vec(c['anchor'],n);J=c['rows']
    require(type(J)is list and all(type(j)is int and 0<=j<m for j in J) and J==sorted(set(J)),'bad selected rows')
    require(im(G,x)==u and feasible(A,b,x),'invalid image anchor')
    require(all((dot(a,x)==t)==(i in J) for i,(a,t) in enumerate(zip(A,b))),'anchor not strict off the selected face')
    C,d=fibre(A,b,G,u);normal=[Q(0)]*p;weights=[Q(1)]*len(J);seen=set()
    for q in c['zero_duals']:
        j=q['row'];require(type(j)is int and j in J and j not in seen,'bad repeated dual row');seen.add(j)
        require(verify_dual(C,d,mul(-1,A[j]),q['dual'])==-b[j],'nonzero maximal fibre slack')
        z=dense_dual(q['dual'],len(C));require(all(not z[i] or i in J for i in range(m)),'noncomplementary fibre witness')
        for i,k in enumerate(J):weights[i]+=z[k]
        for l in range(p):normal[l]-=z[m+l]-z[m+p+l]
    require(seen==set(J),'missing fibre certificate')
    require(vec(c['normal'],p)==tuple(normal) and vec(c['weights'],len(J))==tuple(weights),'incorrect derived exposer')
    W=tuple(vec(w,len(J)) for w in c['image_rows']);require(len(W)==p,'wrong image factorization')
    for i in range(n):
        require(sum(normal[l]*G[l][i] for l in range(p))==sum(weights[j]*A[k][i] for j,k in enumerate(J)),'false exposing identity')
        for l in range(p):require(G[l][i]==sum(W[l][j]*A[k][i] for j,k in enumerate(J)),'not a singleton image face')
    return x,J,tuple(normal)


def compact_image(A,b,G,x,cap):
    lp=ExactLP(A,b,x,cap);out=[]
    for j,g in enumerate(G):
        for s in (-1,1):
            o=lp.maximize(mul(s,g));out.append({'coordinate':j,'sign':s,'dual':o['dual'],'bound':o['value']})
    return out

def verify_compact(A,b,G,c):
    seen=set()
    for x in c:
        i,s=x['coordinate'],x['sign']
        require(type(i)is int and type(s)is int and 0<=i<len(G) and s in (-1,1) and (i,s) not in seen,'bad compactness label')
        seen.add((i,s));require(verify_dual(A,b,mul(s,G[i]),x['dual'])==rat(x['bound']),'incorrect image bound')
    require(len(seen)==2*len(G),'missing bounded IMAGE coordinate')


def tangent_system(A,J,G,h):
    hg=pull(G,h)
    return tuple(A[j] for j in J)+(hg,mul(-1,hg)), (Q(0),)*len(J)+(Q(1),-Q(1))

def ray_system(A,b,G,u,r):
    n=len(A[0]);M=tuple(a+(Q(0),) for a in A);d=b
    for g,z,ri in zip(G,u,r):
        row=g+(-ri,);M+=(row,mul(-1,row));d+=(z,-z)
    M+=((Q(0),)*n+(-Q(1),),);d+=(Q(0),)
    return M,d


def select_step(A,b,G,u,v,target,cap=20000):
    vx=discover_vertex(A,b,G,u,cap=cap);x,J,normal=verify_vertex(A,b,G,u,vx)
    c=vec(target['normal'],len(G));y=vec(target['anchor'],len(A[0]));h=mul(-1,normal)
    gap=dot(c,sub(v,u));height=dot(h,sub(v,u));require(gap>0 and height>0,'no improving normalized direction')
    seed=mul(1/height,sub(y,x));M,rhs=tangent_system(A,J,G,h);C,d=M,rhs;records=[]
    # Refine the first optimum face by image coordinates. One maximizing source
    # point can still project into the interior; all p coordinates are required.
    for obj in [pull(G,c)]+list(G):
        lp=ExactLP(C,d,seed,cap);o=lp.maximize(obj);records.append(o);seed=vec(o['point'],len(x));z=rat(o['value'])
        C+=(tuple(obj),mul(-1,obj));d+=(z,-z)
    r=im(G,seed);require(dot(h,r)==1 and dot(c,r)>0,'invalid improving ray')
    ray_vertex=discover_vertex(M,rhs,G,r,seed,cap)
    R,rb=ray_system(A,b,G,u,r);opt=ExactLP(R,rb,x+(Q(0),),cap).maximize((Q(0),)*len(x)+(Q(1),))
    yr=vec(opt['point'],len(x)+1);tau=yr[-1];require(tau>0,'selected ray has no positive original step')
    new=im(G,yr[:-1])
    certificate=serial({'from':u,'to':new,'start_vertex':vx,'lex_optima':records,
        'ray_vertex':ray_vertex,'ray_optimum':opt})
    verify_step(A,b,G,v,target,certificate)
    return certificate


def verify_step(A,b,G,v,target,s):
    n=len(A[0]);p=len(G);u=vec(s['from'],p);w=vec(s['to'],p)
    x,J,normal=verify_vertex(A,b,G,u,s['start_vertex']);h=mul(-1,normal);c=vec(target['normal'],p)
    require(dot(c,sub(v,u))>0,'step not before the target optimum')
    M,rhs=tangent_system(A,J,G,h);C,d=M,rhs
    require(len(s['lex_optima'])==p+1,'incomplete image-coordinate tie breaking')
    seed=None
    for obj,o in zip([pull(G,c)]+list(G),s['lex_optima']):
        seed,val=verify_optimum(C,d,tuple(obj),o);C+=(tuple(obj),mul(-1,obj));d+=(val,-val)
    r=im(G,seed);require(dot(h,r)==1 and dot(c,r)>0,'unimproving or unnormalized ray')
    _,_,raynormal=verify_vertex(M,rhs,G,r,s['ray_vertex'])
    R,rb=ray_system(A,b,G,u,r);y,tau=verify_optimum(R,rb,(Q(0),)*n+(Q(1),),s['ray_optimum'])
    require(tau>0 and y[-1]==tau and im(G,y[:-1])==w==add(u,mul(tau,r)),'invalid maximal image endpoint')
    f=sub(raynormal,mul(dot(raynormal,r),h))
    require(dot(f,sub(w,u))==0 and dot(c,w)>dot(c,u),'support/improvement mismatch')
    # The formal tangent-to-edge lemma proves whole-slice equality from these
    # exact witness interfaces. No alleged source adjacency is used here.
    return {'image_start':serial(u),'image_end':serial(w),'image_edge_normal':serial(f),
        'normalized_direction':serial(r),'maximal_parameter':str(tau),
        'objective_gain':str(dot(c,sub(w,u))),
        'normalized_gain':str(dot(c,r)),
        'scope':'Original image edge via normalized tangent slice and maximality over ALL lifts; not a source-edge projection.'}


def construct(data,edge_cap=200,pivot_cap=20000):
    A,b,G,u,v=read(data);target=discover_vertex(A,b,G,v,cap=pivot_cap)
    bounds=compact_image(A,b,G,vec(target['anchor'],len(A[0])),pivot_cap)
    steps=[];current=u
    if current==v:verify_vertex(A,b,G,u,target)
    while current!=v:
        require(len(steps)<edge_cap,'route cap: no completion or polynomial bound claimed')
        s=select_step(A,b,G,current,v,target,pivot_cap);steps.append(s);current=vec(s['to'],len(G))
    out=serial({'problem_sha256':hash_input(A,b,G,u,v),'target_vertex':target,
        'image_boundedness':bounds,'steps':steps})
    return {'certificate':out,'verified':verify(data,out)}


def verify(data,c):
    A,b,G,u,v=read(data);require(c['problem_sha256']==hash_input(A,b,G,u,v),'changed original input')
    verify_vertex(A,b,G,v,c['target_vertex']);verify_compact(A,b,G,c['image_boundedness'])
    current=u;seen={u};reports=[]
    for step in c['steps']:
        require(vec(step['from'],len(G))==current,'broken path')
        reports.append(verify_step(A,b,G,v,c['target_vertex'],step));current=vec(step['to'],len(G))
        require(current not in seen,'repeated original image vertex');seen.add(current)
    require(current==v,'path does not reach the prescribed target')
    return {'status':'PASS','source_dimension':len(A[0]),'image_ambient_dimension':len(G),'source_rows':len(A),
        'original_image_edges':len(reports),'strictly_monotone':True,'all_lift_ray_maximality':True,
        'source_vertex_or_graph_supplied':False,'image_neighbor_supplied':False,'edge_reports':reports,
        'scope':'Finite exact edge-selection/route certificates. No polynomial route-length or simplex-pivot theorem, and no Lean-extracted JSON claim.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--edge-cap',type=int,default=200);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());o=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data,a.edge_cap)
        text=json.dumps(serial(o),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:p.exit(2,f'No completed original-image route: {e}\n')
if __name__=='__main__':main()
