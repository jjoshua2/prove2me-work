#!/usr/bin/env python3
"""Original-edge routes for box cuts with signed pair rows and few RHS values.

The complete coordinate alphabet follows from ALL normalized input rows, not a
sampled vertex inventory. Overlap is unrestricted. Classical coordinate-extreme
routing is adapted to ordered levels, not geometric coordinate rounding. LPs
select edges; a consumer checks certificates without LP/elimination/search.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import argparse, json, hashlib
import exact_farkas_lp as lp
import original_route_exclusion as edge

require=lp.require


def model(data):
    d=data['dimension'];require(type(d)is int and d>=1,'positive dimension required')
    I=[tuple(Q(j==i) for j in range(d)) for i in range(d)]
    A=[tuple(-x for x in a) for a in I]+I;b=[Q(0)]*d+[Q(1)]*d
    C,h= data.get('cuts_A',[]), data.get('cuts_b',[])
    require(len(C)==len(h),'cut RHS mismatch')
    normalized=list(A);nb=list(b)
    for row,rhs in zip(C,h):
        a=tuple(map(lp.rat,row));rhs=lp.rat(rhs)
        nz=[x for x in a if x]
        require(len(a)==d and len(nz)==2 and abs(nz[0])==abs(nz[1]),
                'cut needs exactly two coefficients of equal absolute value')
        z=abs(nz[0]);A.append(a);b.append(rhs)
        normalized.append(tuple(x/z for x in a));nb.append(rhs/z)
    if 'A' in data or 'b' in data:
        givenA,givenb=lp.parse(data['A'],data['b'])
        require(tuple(A)==givenA and tuple(b)==givenb,'not the same ORIGINAL H rows')
    values=tuple(sorted({abs(t) for t in nb[2*d:] if t}))
    return tuple(A),tuple(b),tuple(normalized),tuple(nb),values


def l1_size(q,r):
    return sum(2**j*comb(q,j)*comb(r,j) for j in range(min(q,r)+1))


def vectors(q,r,prefix=()):
    if q==0:
        yield prefix;return
    for n in range(-r,r+1):yield from vectors(q-1,r-abs(n),prefix+(n,))


def alphabet(d,values,cap=200000):
    require(type(cap)is int and cap>0,'bad alphabet cap')
    q=len(values);work=l1_size(q,d-1)+l1_size(q,2*d)
    require(work<=cap,'alphabet enumeration cap: no coverage certificate')
    out=set()
    for n in vectors(q,d-1):
        s=sum((a*c for a,c in zip(n,values)),Q(0))
        for z in (-1,0,1):
            if 0<=z+s<=1:out.add(z+s)
    for n in vectors(q,2*d):
        x=sum((a*c for a,c in zip(n,values)),Q(0))/2
        if 0<=x<=1:out.add(x)
    require(0 in out and 1 in out,'missing box levels')
    return tuple(sorted(out)),work


def tangent(A,b,x,common,locks):
    d=len(x);active=[i for i,(a,t) in enumerate(zip(A,b)) if lp.dot(a,x)==t]
    rows=[A[i] for i in active]+[tuple(-z for z in A[i]) for i in common]
    for j,value in locks:
        require(x[j]==value,'current vertex violates a locked coordinate')
        e=tuple(Q(k==j) for k in range(d));rows.extend([e,tuple(-z for z in e)])
    h=tuple(-sum((A[i][j] for i in active),Q(0)) for j in range(d))
    rows.append(h);rhs=(Q(0),)*(len(rows)-1)+(Q(1),)
    return tuple(rows),rhs


def lex_objective(d,i,sign,m):
    # Every normalized tangent-slice vertex has coordinates 0 or +/-1/H,
    # 1<=H<=2m. B makes a primary-coordinate improvement dominate the tail.
    D=2*m;B=4*D*D+4;order=[i]+[j for j in range(d) if j!=i]
    c=[Q(0)]*d
    for p,j in enumerate(order):c[j]=Q(sign if p==0 else 1,B**p)
    return tuple(c)


def path_packet(A,b,points):
    packet={'format':'original-route-witness-v1',
        'input_sha256':edge.binding(A,b,points[0],points[-1]),
        'vertices':[edge.vertex_packet(A,b,x) for x in points], 'length':len(points)-1}
    edge.add_path_inverses(A,packet)
    return lp.serial(packet)


def raw_input(A,b,u,v):return lp.serial({'A':A,'b':b,'start':u,'target':v})


def construct(data,alphabet_cap=200000,pivot_cap=20000,edge_cap=100000):
    A,b,N,rhs,values=model(data);d=len(A[0]);u=tuple(map(lp.rat,data['start']));v=tuple(map(lp.rat,data['target']))
    edge.vertex_packet(A,b,u);edge.vertex_packet(A,b,v)
    levels,work=alphabet(d,values,alphabet_cap);ranks={x:i for i,x in enumerate(levels)};K=len(levels)
    require(all(x in ranks for x in (*u,*v)),'endpoint not covered by proved alphabet')
    common=[i for i,(a,t) in enumerate(zip(A,b)) if lp.dot(a,u)==t==lp.dot(a,v)]
    left=[u];right=[v];locks=[];phases=[];calls=pivots=committed=0
    def move(points,i,sign):
        nonlocal calls,pivots,committed
        while True:
            x=points[-1];T,h=tangent(N,rhs,x,common,locks)
            solver=lp.ExactLP(T,h,(Q(0),)*d,pivot_cap)
            out=solver.maximize(lex_objective(d,i,sign,len(A)))
            r=tuple(map(lp.rat,out['point']));calls+=1;pivots+=solver.pivots
            if sign*r[i]<=0:
                old=solver.pivots;c=tuple(Q(sign if j==i else 0) for j in range(d))
                opt=solver.maximize(c);calls+=1;pivots+=solver.pivots-old
                require(lp.rat(opt['value'])==0,'lexicographic tangent priority failed')
                return opt['dual']
            require(lp.dot(T[-1],r)==1,'nonzero tangent optimizer not normalized')
            ratios=[(t-lp.dot(a,x))/lp.dot(a,r) for a,t in zip(N,rhs) if lp.dot(a,r)>0]
            require(ratios and min(ratios)>0,'invalid bounded edge step')
            alpha=min(ratios);y=tuple(a+alpha*z for a,z in zip(x,r))
            edge.vertex_packet(A,b,y) # independent actual-original-vertex check
            require(all(z in ranks for z in y),'new vertex outside proved alphabet')
            require(sign*(ranks[y[i]]-ranks[x[i]])>0,'coordinate rank did not strictly progress')
            pair={'vertices':[edge.vertex_packet(A,b,x),edge.vertex_packet(A,b,y)]}
            edge.add_path_inverses(A,pair) # reject a direction that is not an edge
            points.append(y);committed+=1
            require(committed<=edge_cap,'route cap: no complete path claimed')
    for i in range(d):
        if left[-1]==right[-1]:break
        a,z=left[-1],right[-1];S=ranks[a[i]]+ranks[z[i]]
        sign=-1 if S<=K-1 else 1
        startL,startR=len(left)-1,len(right)-1
        dualL=move(left,i,sign);dualR=move(right,i,sign)
        require(left[-1][i]==right[-1][i],'different minima on the same face')
        phases.append({'coordinate':i,'sign':sign,'left_range':[startL,len(left)-1],
            'right_range':[startR,len(right)-1],'left_dual':dualL,'right_dual':dualR,
            'value':lp.serial(left[-1][i])})
        locks.append((i,left[-1][i]))
    require(left[-1]==right[-1],'coordinate-face assembly did not meet')
    cert={'format':'signed-coordinate-level-route-v1','input_sha256':edge.binding(A,b,u,v),
        'levels':lp.serial(levels),'RHS_values':lp.serial(values),'common_rows':common,
        'left':path_packet(A,b,left),'right':path_packet(A,b,right),'phases':phases,
        'bound':d*(K-1)}
    report=verify(data,cert,alphabet_cap)
    return {'certificate':cert,'verified':report,
        'discovery':{'LP_calls':calls,'LP_pivots':pivots,'alphabet_integer_vectors':work,
                     'complete_stars_enumerated':0,'vertex_graph_enumerated':False,
                     'global_direction_catalogue':False}}


def verify(data,c,alphabet_cap=200000):
    A,b,N,rhs,values=model(data);d=len(A[0]);u=tuple(map(lp.rat,data['start']));v=tuple(map(lp.rat,data['target']))
    require(c['format']=='signed-coordinate-level-route-v1' and c['input_sha256']==edge.binding(A,b,u,v),'input binding changed')
    levels,_=alphabet(d,values,alphabet_cap);ranks={x:i for i,x in enumerate(levels)};K=len(levels)
    require(c['levels']==lp.serial(levels) and c['RHS_values']==lp.serial(values),'false alphabet coverage')
    common=[i for i,(a,t) in enumerate(zip(A,b)) if lp.dot(a,u)==t==lp.dot(a,v)]
    require(c['common_rows']==common and c['bound']==d*(K-1),'false face or bound')
    paths=[]
    for name,source in [('left',u),('right',v)]:
        p=c[name];require(p['vertices'],'empty route leg')
        end=tuple(map(lp.rat,p['vertices'][-1]['point']))
        edge.verify_path(raw_input(A,b,source,end),p)
        points=[tuple(map(lp.rat,z['point'])) for z in p['vertices']]
        require(all(z in ranks for x in points for z in x),'vertex outside proved coordinate set')
        require(all(lp.dot(A[j],x)==b[j] for x in points for j in common),'lost common original face')
        paths.append(points)
    left,right=paths;require(left[-1]==right[-1],'legs do not meet')
    cursor=[0,0];locks=[];phasebudget=0
    require(len(c['phases'])<=d,'too many coordinate phases')
    for i,p in enumerate(c['phases']):
        require(p['coordinate']==i and type(p['sign'])is int and p['sign'] in (-1,1),'invalid coordinate/sign')
        sign=p['sign'];S=ranks[left[cursor[0]][i]]+ranks[right[cursor[1]][i]]
        require(sign==(-1 if S<=K-1 else 1),'wrong smaller rank budget')
        allowed=S if sign<0 else 2*(K-1)-S
        require(allowed<=K-1,'phase budget exceeds level span')
        steps=0;ends=[]
        for j,(name,points) in enumerate(zip(('left','right'),paths)):
            span=p[name+'_range'];require(type(span)is list and len(span)==2 and all(type(n)is int for n in span),'invalid phase span')
            first,last=span
            require(first==cursor[j] and first<=last<len(points),'phase gap or out of range')
            for x in points[first:last+1]:
                require(all(x[k]==t for k,t in locks),'departed earlier extreme face')
            require(all(sign*(y[i]-x[i])>0 for x,y in zip(points[first:last],points[first+1:last+1])),
                    'phase contains stationary or backward coordinate move')
            x=points[last];T,h=tangent(N,rhs,x,common,locks)
            objective=tuple(Q(sign if k==i else 0) for k in range(d))
            bound=lp.verify_dual(T,h,objective,p[name+'_dual'])
            require(bound==0,'coordinate extremality is not certified')
            ends.append(x[i]);cursor[j]=last;steps+=last-first
        require(ends[0]==ends[1]==lp.rat(p['value']),'new face values disagree')
        require(steps<=allowed,'actual phase exceeds proved rank charge')
        locks.append((i,ends[0]));phasebudget+=allowed
    require(cursor==[len(left)-1,len(right)-1],'unaccounted edges')
    L=len(left)+len(right)-2
    require(L<=phasebudget<=d*(K-1),'global route bound violated')
    route=left+list(reversed(right[:-1]));debt=0;departed=set()
    acts=[set(edge.active(A,b,x)) for x in route]
    for I,J in zip(acts,acts[1:]):debt+=len((J-I)&departed);departed|=I-J
    return {'status':'PASS','dimension':d,'original_rows':len(A),'distinct_RHS_magnitudes':len(values),
        'coordinate_levels':K,'all_pairs_bound':d*(K-1),'endpoint_phase_bound':phasebudget,
        'original_edges':L,'coordinate_phases':len(c['phases']),'common_rows_preserved':len(common),
        'original_row_reentries':debt,
        'scope':'Signed-pair/few-RHS class, not arbitrary polytopes. Exact code, no Lean or polynomial LP-pivot claim.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--certificate',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();data=json.loads(a.input.read_text())
    if a.certificate:r=verify(data,json.loads(a.certificate.read_text()))
    else:r=construct(data)
    a.output.write_text(json.dumps(lp.serial(r),sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
