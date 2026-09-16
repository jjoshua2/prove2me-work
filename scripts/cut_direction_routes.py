#!/usr/bin/env python3
"""Original-edge paths after arbitrary halfspace cuts of a direction-controlled base.

The recognized base is a box or a supplied positive building-set simplex sum.
Its full original H rows are bound to the input; a claimed arbitrary direction
list is NOT accepted as evidence of coverage. Each cut edge lies in a base
face of dimension at most k+1. Enumerate the resulting spans/kernel lines,
then trace a generic straight objective segment with exact original-H LPs.

The final auditor checks whole support witnesses and original vertex/edge
right-inverse identities. It runs NO LP. It does recompute the finite rational
candidate-direction catalogue. The bound is polynomial for fixed k, not for
unrestricted k; the old Bland LP has an explicit cap, no polynomial pivot claim.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import argparse, hashlib, json
import exact_farkas_lp as lp
import endpoint_transfer_routes as base

require, rat, serial, dot = lp.require, lp.rat, lp.serial, lp.dot


def rref(rows, columns):
    a=[list(map(rat,r)) for r in rows]; require(all(len(r)==columns for r in a),'matrix shape')
    piv=[];i=0
    for j in range(columns):
        p=next((k for k in range(i,len(a)) if a[k][j]),None)
        if p is None: continue
        a[i],a[p]=a[p],a[i];v=a[i][j];a[i]=[z/v for z in a[i]]
        for k in range(len(a)):
            if k!=i and a[k][j]:
                v=a[k][j];a[k]=[x-v*y for x,y in zip(a[k],a[i])]
        piv.append(j);i+=1
        if i==len(a): break
    return a,piv


def line(v):
    first=next((z for z in v if z),None)
    return None if first is None else tuple(z/first for z in v)


def inverse(A):
    n=len(A); require(all(len(r)==n for r in A),'square inverse shape')
    a,p=rref([list(r)+[Q(i==j) for j in range(n)] for i,r in enumerate(A)],2*n)
    require(p[:n]==list(range(n)),'singular inverse')
    return tuple(tuple(r[n:]) for r in a[:n])


def right_inverse(rows,d):
    r=len(rows)
    if not r:return tuple(() for _ in range(d))
    _,p=rref(rows,d); require(len(p)==r,'row rank is insufficient')
    inv=inverse([[a[j] for j in p] for a in rows]);R=[[Q(0)]*r for _ in range(d)]
    for j,row in zip(p,inv):R[j]=list(row)
    return tuple(map(tuple,R))


def independent_ids(A,ids,count):
    chosen=[];rank=0;d=len(A[0])
    for i in ids:
        r=len(rref([A[j] for j in chosen+[i]],d)[1])
        if r>rank:chosen.append(i);rank=r
        if rank==count:break
    require(rank==count,'insufficient independent original tight rows')
    return chosen


def rank_certificate(A,ids,count):
    chosen=[] if count==0 else independent_ids(A,ids,count)
    return serial({'rows':chosen,'right_inverse':right_inverse([A[i] for i in chosen],len(A[0]))})


def check_rank(A,proof,count):
    I=proof['rows'];R=tuple(tuple(map(rat,r)) for r in proof['right_inverse']);d=len(A[0])
    require(type(I)is list and len(I)==count and len(set(I))==count and
            all(type(i)is int and 0<=i<len(A) for i in I),'bad rank row labels')
    require(len(R)==d and all(len(r)==count for r in R),'right inverse shape')
    require(all(sum(A[i][k]*R[k][j] for k in range(d))==Q(l==j)
                for l,i in enumerate(I) for j in range(count)),'false original right-inverse identity')
    return I


def active(A,b,x):return [i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t]


def model(data):
    B=data['base'];kind=B['kind']
    if kind=='box':
        low=tuple(map(rat,B['lower']));high=tuple(map(rat,B['upper']));d=len(low)
        require(d>0 and len(high)==d and all(l<h for l,h in zip(low,high)),'nondegenerate box required')
        D=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
        A=[tuple(-z for z in a) for a in D]+D;b=[-z for z in low]+list(high)
    elif kind=='building_set':
        n=B['n'];A,b,_,_=base.building_H(n,B['subsets'],B.get('weights'));d=n-1
        D=[tuple(Q(l==i)-Q(l==j) for l in range(d)) for i,j in combinations(range(n),2)]
    else:raise ValueError('unsupported base; an arbitrary asserted direction cover is not verified')
    A=tuple(map(tuple,A));b=tuple(b)
    chart=data.get('affine_chart')
    if chart is not None:
        T=tuple(tuple(map(rat,r)) for r in chart['matrix']);shift=tuple(map(rat,chart['offset']))
        require(len(T)==d and all(len(r)==d for r in T) and len(shift)==d,'affine chart shape')
        inv=inverse(T)
        A=tuple(tuple(sum(a[i]*inv[i][j] for i in range(d)) for j in range(d)) for a in A)
        b=tuple(z+dot(a,shift) for a,z in zip(A,b));D=[tuple(dot(row,g) for row in T) for g in D]
    C=tuple(tuple(map(rat,r)) for r in data.get('cuts_A',[]));h=tuple(map(rat,data.get('cuts_b',[])))
    require(len(C)==len(h) and all(len(r)==d for r in C),'cut shape')
    finalA,finalb=A+C,b+h
    if 'A' in data or 'b' in data:
        suppliedA,suppliedb=lp.parse(data['A'],data['b'])
        require(finalA==suppliedA and finalb==suppliedb,'final ORIGINAL H rows not bound to base and cuts')
    return finalA,finalb,tuple(sorted({line(g) for g in D})),C


def catalogue(D,C,cap=200000,overlap_bound=None):
    raw_count=len(C);d=len(D[0]);D=tuple(sorted({line(g) for g in D}));C=tuple(sorted({v for a in C if (v:=line(a)) is not None}))
    N,k=len(D),len(C)
    q=k if overlap_bound is None else overlap_bound
    require(type(q)is int and q>=0,'invalid cut-overlap bound')
    upper=min(d,N,k+1,q+1)
    work=sum(comb(N,r)*comb(k,r-1) for r in range(1,upper+1))
    require(type(cap)is int and cap>=work,'direction enumeration cap: no partial cover returned')
    out={}
    for r in range(1,upper+1):
        for J in combinations(range(N),r):
            G=[D[j] for j in J]
            if len(rref(G,d)[1])!=r:continue
            for I in combinations(range(k),r-1):
                M=[[dot(C[i],g) for g in G] for i in I];R,p=rref(M,r)
                if len(p)!=r-1:continue
                free=next(i for i in range(r) if i not in p);beta=[Q(0)]*r;beta[free]=1
                for row,j in zip(R,p):beta[j]=-row[free]
                g=line(tuple(sum(beta[j]*G[j][l] for j in range(r)) for l in range(d)))
                require(g is not None,'zero vector from independent span')
                out.setdefault(g,{'base_directions':list(J),'cut_normal_lines':list(I),'coefficients':serial(beta)})
    lines=tuple(sorted(out))
    return lines,{'base_lines':N,'distinct_cut_normal_lines':k,'raw_cut_rows':raw_count,
                  'supports_tested':work,'direction_bound':work,'overlap_bound':overlap_bound,
                  'unrestricted_vandermonde_bound':comb(N+k,k+1),
                  'catalogue_lines':len(lines)},[out[g] for g in lines]


def overlap_certificate(data,A,b,C,seed,cap,pivot_cap):
    q=data.get('max_cut_overlap');proofs=[];calls=pivots=0
    if q is None:return {'bound':None,'proofs':[]},{'overlap_LP_calls':0,'overlap_LP_pivots':0}
    require(type(q)is int and 0<=q<=len(C),'overlap bound outside cut count')
    require(comb(len(C),q+1)<=cap,'overlap separation enumeration cap')
    offset=len(A)-len(C);solver=None
    for I in combinations(range(len(C)),q+1):
        obj=tuple(sum((C[i][j] for i in I),Q(0)) for j in range(len(A[0])))
        rhs=sum((b[offset+i] for i in I),Q(0));dual=None
        # Cheap exact original-box support bound. If inconclusive, solve on
        # the ACTUAL cut polytope. Every output uses the same dual verifier.
        if data['base']['kind']=='box' and not data.get('affine_chart'):
            d=len(obj);raw=[[j if v<0 else d+j,str(abs(v))] for j,v in enumerate(obj) if v]
            if lp.verify_dual(A,b,obj,raw)<rhs:dual=raw
        if dual is None:
            if solver is None:solver=lp.ExactLP(A,b,seed,pivot_cap)
            opt=solver.maximize(obj)
            require(rat(opt['value'])<rhs,'the proposed cut-overlap bound is false')
            dual=opt['dual']
        proofs.append({'cut_rows':list(I),'dual':dual})
    if solver is not None:calls,pivots=solver.calls,solver.pivots
    return {'bound':q,'proofs':proofs},{'overlap_LP_calls':calls,'overlap_LP_pivots':pivots}


def check_overlap(data,A,b,C,proof,cap):
    q=data.get('max_cut_overlap')
    require(proof['bound']==q,'cut-overlap parameter changed')
    if q is None:
        require(proof['proofs']==[],'unrequested overlap evidence');return None
    require(type(q)is int and 0<=q<=len(C),'bad overlap bound')
    require(comb(len(C),q+1)<=cap,'overlap verification cap')
    expected=list(combinations(range(len(C)),q+1))
    require(len(proof['proofs'])==len(expected),'missing cut-intersection exclusion')
    offset=len(A)-len(C)
    for I,p in zip(expected,proof['proofs']):
        require(type(p['cut_rows'])is list and all(type(i)is int for i in p['cut_rows']) and tuple(p['cut_rows'])==I,'wrong excluded cut set')
        obj=tuple(sum((C[i][j] for i in I),Q(0)) for j in range(len(A[0])))
        bound=lp.verify_dual(A,b,obj,p['dual'])
        require(bound<sum((b[offset+i] for i in I),Q(0)),'cut faces may meet: overlap not established')
    return q


def objective_pair(A,b,u,v,D,tries=256):
    d=len(u);I=independent_ids(A,active(A,b,u),d);J=independent_ids(A,active(A,b,v),d)
    def candidate(rows,t):return tuple(sum(Q(t)**i*A[j][l] for i,j in enumerate(rows)) for l in range(d))
    for s in range(1,tries+1):
        f=candidate(I,s);values=[dot(f,g) for g in D]
        if all(values):break
    else:raise ValueError('source generic-objective cap')
    for t in range(1,tries+1):
        h=candidate(J,t);last=[dot(h,g) for g in D]
        if not all(last):continue
        roots=[-a/(z-a) for a,z in zip(values,last) if a*z<0]
        if len(set(roots))==len(roots):break
    else:raise ValueError('target generic-objective cap')
    return f,h,{'source_rows':I,'source_parameter':s,'target_rows':J,'target_parameter':t}


def parameters(f,h,D):
    first=[dot(f,g) for g in D];last=[dot(h,g) for g in D]
    require(all(first) and all(last),'endpoint objective orthogonal to a catalogue line')
    roots=sorted((-a/(b-a),i) for i,(a,b) in enumerate(zip(first,last)) if a*b<0)
    require(len({r for r,i in roots})==len(roots),'independent simultaneous direction crossings')
    return roots


def digest(data):
    return hashlib.sha256(json.dumps(serial(data),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def construct(data,subset_cap=200000,pivot_cap=20000):
    A,b,D,C=model(data);u=tuple(map(rat,data['start']));v=tuple(map(rat,data['target']));d=len(A[0])
    require(len(u)==len(v)==d and all(dot(a,x)<=z for x in (u,v) for a,z in zip(A,b)),'infeasible endpoint')
    overlap,overlap_stats=overlap_certificate(data,A,b,C,u,subset_cap,pivot_cap)
    q=check_overlap(data,A,b,C,overlap,subset_cap)
    D,summary,witnesses=catalogue(D,C,subset_cap,q)
    locked=sorted(set(active(A,b,u))&set(active(A,b,v)))
    H=A+tuple(tuple(-x for x in A[i]) for i in locked);rhs=b+tuple(-b[i] for i in locked)
    f,h,generic=objective_pair(H,rhs,u,v,D)
    roots=parameters(f,h,D);cuts=[Q(0)]+[r for r,i in roots]+[Q(1)]
    samples=[(a+b)/2 for a,b in zip(cuts,cuts[1:])]
    solver=lp.ExactLP(H,rhs,u,pivot_cap);cache={}
    obj=lambda t:tuple((1-t)*a+t*z for a,z in zip(f,h))
    def at(i):
        if i not in cache:cache[i]=solver.maximize(obj(samples[i]))
        return tuple(map(rat,cache[i]['point']))
    # A vertex's objective-optimality set on a line is an interval. Skip
    # stationary chamber ranges by certified optimization and binary search.
    require(at(0)==u and at(len(samples)-1)==v,'wrong endpoint chamber')
    vertices=[u];wall_records=[];i=0
    while i<len(samples)-1:
        current=vertices[-1]
        if at(len(samples)-1)==current:break
        lo,hi=i,len(samples)-1
        while hi-lo>1:
            mid=(lo+hi)//2
            if at(mid)==current:lo=mid
            else:hi=mid
        nxt=at(hi);root,idx=roots[hi-1]
        optimum=solver.maximize(obj(root))
        require(dot(obj(root),current)==dot(obj(root),nxt)==rat(optimum['value']),'wrong crossing support')
        wall_records.append({'parameter':str(root),'catalogue_line':idx,'dual':optimum['dual']})
        vertices.append(nxt);i=hi
    require(vertices[-1]==v,'route failed to reach target')
    vc=[rank_certificate(A,active(A,b,x),d) for x in vertices]
    ec=[rank_certificate(A,sorted(set(active(A,b,x))&set(active(A,b,y))),d-1)
        for x,y in zip(vertices,vertices[1:])]
    cert=serial({'format':'cut-direction-shadow-v1','input_sha256':digest(data),'subset_cap':subset_cap,
       'catalogue':D,'summary':summary,'witnesses':witnesses,'overlap':overlap,'locked_rows':locked,
       'source_objective':f,'target_objective':h,'generic':generic,
       'path':vertices,'vertex_rank':vc,'edge_rank':ec,'walls':wall_records})
    return {'certificate':cert,'verified':verify(data,cert),
            'discovery':{**overlap_stats,'LP_calls':solver.calls,'LP_pivots':solver.pivots,
             'sample_queries':len(cache),'full_direction_chambers':len(samples),
             'global_original_graph_enumerated':False}}


def verify(data,c):
    require(c['format']=='cut-direction-shadow-v1' and c['input_sha256']==digest(data),'changed input binding')
    A,b,D,C=model(data);q=check_overlap(data,A,b,C,c['overlap'],c['subset_cap'])
    D,summary,witnesses=catalogue(D,C,c['subset_cap'],q);d=len(A[0])
    require(c['catalogue']==serial(D) and c['summary']==summary and c['witnesses']==witnesses,'incomplete or changed direction cover')
    path=[tuple(map(rat,x)) for x in c['path']]
    require(path and path[0]==tuple(map(rat,data['start'])) and path[-1]==tuple(map(rat,data['target'])),'wrong requested endpoints')
    require(len(path)==len(c['vertex_rank'])==len(c['edge_rank'])+1==len(c['walls'])+1,'certificate lengths')
    require(all(len(x)==d and all(dot(a,x)<=z for a,z in zip(A,b)) for x in path),'infeasible original vertex')
    for x,p in zip(path,c['vertex_rank']):
        I=check_rank(A,p,d);require(all(dot(A[i],x)==b[i] for i in I),'vertex rank rows not tight')
    locked=sorted(set(active(A,b,path[0]))&set(active(A,b,path[-1])))
    require(c['locked_rows']==locked and all(all(dot(A[i],x)==b[i] for i in locked) for x in path),'common original face lost')
    H=A+tuple(tuple(-x for x in A[i]) for i in locked);rhs=b+tuple(-b[i] for i in locked)
    f=tuple(map(rat,c['source_objective']));h=tuple(map(rat,c['target_objective']));g=c['generic']
    require(len(f)==len(h)==d,'objective dimension')
    # Positive weights on d independent tight rows strictly expose endpoints
    # of the restricted original face. Independence is checked algebraically
    # for original path vertices above; full endpoint duals suffice below.
    for name,cost,x in [('source',f,path[0]),('target',h,path[-1])]:
        I=g[name+'_rows'];t=g[name+'_parameter']
        require(type(t)is int and t>0 and type(I)is list and len(I)==d and len(set(I))==d and
                all(type(j)is int and 0<=j<len(H) and dot(H[j],x)==rhs[j] for j in I),'bad exposing rows')
        require(cost==tuple(sum(Q(t)**i*H[j][l] for i,j in enumerate(I)) for l in range(d)),'false exposing objective')
        # This narrow d-row independence check uses exact rational elimination;
        # original-edge certificates themselves are equation-only.
        require(len(rref([H[j] for j in I],d)[1])==d,'endpoint objective rows not independent')
    rootmap={idx:r for r,idx in parameters(f,h,D)};last=Q(0);used=set()
    for x,y,p,w in zip(path,path[1:],c['edge_rank'],c['walls']):
        I=check_rank(A,p,d-1);require(x!=y and all(dot(A[i],x)==dot(A[i],y)==b[i] for i in I),'not an original one-dimensional face')
        idx=w['catalogue_line'];r=rat(w['parameter'])
        require(type(idx)is int and idx in rootmap and rootmap[idx]==r and idx not in used and last<r<1,'repeated/out-of-order crossing')
        require(line(tuple(b-a for a,b in zip(x,y)))==D[idx],'edge direction not bound to crossing')
        cost=tuple((1-r)*a+r*b for a,b in zip(f,h))
        bound=lp.verify_dual(H,rhs,cost,w['dual'])
        require(dot(cost,x)==dot(cost,y)==bound,'whole crossing support not certified')
        require(dot(h,tuple(b-a for a,b in zip(x,y)))>0,'target-objective progress fails')
        used.add(idx);last=r
    require(len(path)-1<=len(rootmap)<=len(D)<=summary['direction_bound'],'direction/edge budget failure')
    return {'status':'PASS','dimension':d,'original_H_rows':len(A),'added_halfspace_rows':len(C),**summary,
        'original_edges':len(path)-1,'separating_catalogue_lines':len(rootmap),
        'common_original_rows_retained':len(locked),'nonsimple_or_lower_dimensional_allowed':True,
        'shortest_claimed':False,'global_original_graph_enumerated':False,
        'scope':'Recognized base plus explicit arbitrary cuts; classical direction theorem and written cut-closure proof, not Lean verification.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--certificate',type=Path);p.add_argument('--subset-cap',type=int,default=200000);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data,a.subset_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError,OSError) as e:p.exit(2,f'No certified cut-polytope route: {e}\n')
if __name__=='__main__':main()
