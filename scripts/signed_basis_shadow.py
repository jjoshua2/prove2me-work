#!/usr/bin/env python3
"""Exact signed two-coordinate conditioning and original-H shadow routes.

Recognizes positive diagonal/row rescalings of rows with <=2 entries in {+1,-1}.
The signed graph may have unbalanced sign cycles. Every basis inverse is checked
against the original normalized rows. Symbolic RHS perturbation is used ONLY for
basis selection; reported routes and all edge checks are on the unchanged input.
The deterministic test objectives are NOT the random distribution in the cited
Dadush--Haehnle diameter proof. Computational caps report failure, not nonexistence.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from itertools import combinations
import hashlib, json, random
from pathlib import Path


def need(ok, msg):
    if not ok: raise ValueError(msg)


def rat(x):
    need(type(x) in (int,str) or isinstance(x,F), 'exact integers/rational strings required')
    return F(x)


def dot(a,b): return sum((x*y for x,y in zip(a,b) if x and y),F(0))
def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x


def signed_kernel(rows,d):
    """Homogeneous kernel = signed constants on unpinned balanced components."""
    graph=[[] for _ in range(d)]; unary=set()
    for row in rows:
        nz=[(i,v) for i,v in enumerate(row) if v]
        need(len(row)==d and len(nz)<=2 and all(v in (-1,1) for _,v in nz),'not a signed unit row')
        if len(nz)==1:unary.add(nz[0][0])
        if len(nz)==2:
            (i,a),(j,b)=nz;sg=-a*b
            graph[i].append((j,sg));graph[j].append((i,sg))
    signs={};components=[];free=[]
    for root in range(d):
        if root in signs:continue
        signs[root]=1;todo=[root];nodes=[];pinned=False;conflicts=[]
        while todo:
            i=todo.pop();nodes.append(i);pinned |= i in unary
            for j,s in graph[i]:
                if j not in signs:signs[j]=s*signs[i];todo.append(j)
                elif signs[j]!=s*signs[i]:pinned=True;conflicts.append([i,j,s])
        nodes.sort();part={'nodes':nodes,'signs':[signs[i] for i in nodes],
                           'pinned':bool(pinned),'unary_nodes':sorted(set(nodes)&unary),
                           'sign_conflicts':conflicts}
        components.append(part)
        if not pinned:free.append(tuple(signs.get(i,0) if i in nodes else 0 for i in range(d)))
    for g in free:need(all(dot(a,g)==0 for a in rows),'kernel witness failed')
    return {'components':components,'kernel':free,'rank':d-len(free)}


def basis_inverse(rows):
    """Delete each row; the remaining kernel is one signed-constant component."""
    d=len(rows);need(all(len(a)==d for a in rows),'basis must be square')
    columns=[];witnesses=[]
    for j in range(d):
        k=signed_kernel(rows[:j]+rows[j+1:],d)
        if len(k['kernel'])!=1:raise ValueError('singular basis')
        g=k['kernel'][0];den=dot(rows[j],g)
        if not den:raise ValueError('singular basis')
        need(den in (-2,-1,1,2),'impossible signed pivot denominator')
        col=tuple(F(t,den) for t in g)
        need(all(dot(row,col)==int(i==j) for i,row in enumerate(rows)),'basis inverse identity failed')
        columns.append(col);witnesses.append({'row':j,'kernel':g,'denominator':den})
    inv=tuple(tuple(columns[j][i] for j in range(d)) for i in range(d))
    need(all(x in (0,1,-1,F(1,2),F(-1,2)) for r in inv for x in r),'inverse alphabet failed')
    return inv,witnesses


def recognize(A):
    d=len(A[0]);G=[[] for _ in range(d)]
    for a in A:
        need(len(a)==d,'ragged input')
        nz=[i for i,v in enumerate(a) if v];need(len(nz)<=2,'more than two nonzero coefficients')
        if len(nz)==2:
            i,j=nz;ratio=abs(a[i]/a[j]);G[i].append((j,ratio));G[j].append((i,1/ratio))
    scale=[None]*d
    for root in range(d):
        if scale[root] is not None:continue
        scale[root]=F(1);todo=[root]
        while todo:
            i=todo.pop()
            for j,g in G[i]:
                v=scale[i]*g
                if scale[j] is None:scale[j]=v;todo.append(j)
                else:need(scale[j]==v,'inconsistent absolute-gain cycle; unsupported, not high diameter')
    rows=[];mult=[]
    for a in A:
        transformed=[x*s for x,s in zip(a,scale)]
        m=next((abs(x) for x in transformed if x),F(1));row=tuple(x/m for x in transformed)
        need(all(x in (-1,0,1) for x in row),'normalization failed')
        rows.append(row);mult.append(m)
    return scale,mult,rows


class SignedModel:
    def __init__(self,data):
        self.originalA=[tuple(map(rat,a)) for a in data['A']];self.originalb=tuple(map(rat,data['b']))
        need(self.originalA and self.originalA[0],'nonempty positive-dimensional ambient input required')
        self.d=len(self.originalA[0]);self.m=len(self.originalA)
        need(len(self.originalb)==self.m,'row/right-hand-side mismatch')
        self.start=tuple(map(rat,data['start']));self.end=tuple(map(rat,data['end']))
        need(len(self.start)==self.d==len(self.end),'endpoint dimension mismatch')
        for x in (self.start,self.end):need(all(dot(a,x)<=b for a,b in zip(self.originalA,self.originalb)),'infeasible endpoint')
        self.scale,self.row_scale,self.fullA=recognize(self.originalA)
        self.fullb=tuple(b/s for b,s in zip(self.originalb,self.row_scale))
        xs=tuple(x/s for x,s in zip(self.start,self.scale));ys=tuple(x/s for x,s in zip(self.end,self.scale))
        acts=[[i for i,(a,b) in enumerate(zip(self.fullA,self.fullb)) if dot(a,x)==b] for x in (xs,ys)]
        for act in acts:need(signed_kernel([self.fullA[i] for i in act],self.d)['rank']==self.d,'endpoint is not a vertex')
        self.common=sorted(set(acts[0])&set(acts[1]));ker=signed_kernel([self.fullA[i] for i in self.common],self.d)
        self.lift_columns=ker['kernel'];self.h=len(self.lift_columns);self.offset=xs
        self.quotient_scale=[];self.A=[];self.b=[]
        for a,b in zip(self.fullA,self.fullb):
            projected=[dot(a,g) for g in self.lift_columns]
            s=next((abs(v) for v in projected if v),F(1))
            row=tuple(v/s for v in projected)
            need(all(v in (-1,0,1) for v in row),'signed face closure failed')
            self.A.append(row);self.b.append((b-dot(a,xs))/s);self.quotient_scale.append(s)
        self.b=tuple(self.b);self.s=(F(0),)*self.h
        self.t=tuple((ys[next(i for i,v in enumerate(g) if v)]-xs[next(i for i,v in enumerate(g) if v)]) /
                     next(v for v in g if v) for g in self.lift_columns)
        need(self.lift(self.t)==self.end,'quotient endpoint lift failed')
        mid=tuple(v/2 for v in self.t)
        need(all(not any(a) or dot(a,mid)<b for a,b in zip(self.A,self.b)),'quotient is not strict at endpoint midpoint')
        self.inv_cache={};self.basis_searches=0
        self.digest=hashlib.sha256(json.dumps(serial({'A':self.originalA,'b':self.originalb,'start':self.start,'end':self.end}),sort_keys=True).encode()).hexdigest()

    def lift(self,x):
        return tuple((self.offset[j]+sum((x[k]*g[j] for k,g in enumerate(self.lift_columns)),F(0)))*self.scale[j] for j in range(self.d))

    def inverse(self,B):
        B=tuple(B)
        if B not in self.inv_cache:self.inv_cache[B]=basis_inverse([self.A[i] for i in B])[0]
        return self.inv_cache[B]

    def point(self,B):
        inv=self.inverse(B)
        return tuple(dot(row,[self.b[i] for i in B]) for row in inv)

    def coefficients(self,a,inv):
        return tuple(sum((a[i]*inv[i][j] for i in range(self.h) if a[i]),F(0)) for j in range(self.h))

    def ratio_series(self,B,r,inv,den=F(1)):
        alpha=self.coefficients(self.A[r],inv)
        terms={0:(self.b[r]-dot(alpha,[self.b[i] for i in B]))/den,r+1:F(1)/den}
        for i,v in zip(B,alpha):terms[i+1]=terms.get(i+1,F(0))-v/den
        return {k:v for k,v in terms.items() if v}

    def series_cmp(self,s,t):
        for k in sorted(s.keys()|t.keys()):
            z=s.get(k,F(0))-t.get(k,F(0))
            if z:return 1 if z>0 else -1
        return 0

    def feasible_basis(self,B):
        try:inv=self.inverse(B)
        except ValueError:return False
        return all(self.series_cmp(self.ratio_series(B,i,inv),{})>=0 for i in range(self.m))

    def endpoint_basis(self,x,cap=100000):
        active=[i for i,(a,b) in enumerate(zip(self.A,self.b)) if any(a) and dot(a,x)==b]
        for tried,B in enumerate(combinations(active,self.h),1):
            self.basis_searches+=1
            need(tried<=cap,'endpoint basis enumeration cap; no partial success claimed')
            if self.feasible_basis(B):return tuple(B)
        raise ValueError('no feasible symbolic endpoint basis')

    def one_attempt(self,seed,limit=20000):
        if self.h==0:return {'input_sha256':self.digest,'basis_steps':[],'route':[serial(self.start)],'dimension':0,'seed':seed}
        Bs=self.endpoint_basis(self.s);Bt=self.endpoint_basis(self.t);rng=random.Random(seed)
        ws=[F(rng.randrange(1,1000000)) for _ in range(self.h)];wt=[F(rng.randrange(1,1000000)) for _ in range(self.h)]
        c0=tuple(sum((ws[k]*self.A[r][j] for k,r in enumerate(Bs)),F(0)) for j in range(self.h))
        c1=tuple(sum((wt[k]*self.A[r][j] for k,r in enumerate(Bt)),F(0)) for j in range(self.h))
        diff=tuple(v-u for u,v in zip(c0,c1));B=Bs;time=F(0);steps=[];seen=set();route=[self.start]
        for _ in range(limit):
            need(B not in seen,'basis revisit on parametric path');seen.add(B)
            inv=self.inverse(B);l0=self.coefficients(c0,inv);ld=self.coefficients(diff,inv)
            need(all(a+time*b>=0 for a,b in zip(l0,ld)),'dual feasibility failed')
            exits=[(-a/b,j) for j,(a,b) in enumerate(zip(l0,ld)) if b<0 and time<=-a/b<1]
            if not exits:
                need(self.lift(self.point(B))==self.end,'terminal basis does not map to requested target')
                return {'input_sha256':self.digest,'dimension':self.h,'seed':seed,'source_basis':Bs,'target_basis':Bt,
                        'source_weights':ws,'target_weights':wt,'source_objective':c0,'target_objective':c1,
                        'basis_steps':steps,'final_basis':B,'route':route}
            t=min(z[0] for z in exits);leaves=[j for v,j in exits if v==t]
            need(len(leaves)==1,'nongeneric objective tie; retry with another recorded seed')
            j=leaves[0];direction=tuple(-row[j] for row in inv)
            best=None;winner=None
            for r,a in enumerate(self.A):
                den=dot(a,direction)
                if den<=0:continue
                series=self.ratio_series(B,r,inv,den)
                if best is None or self.series_cmp(series,best)<0:best=series;winner=r
                elif self.series_cmp(series,best)==0:raise ValueError('symbolic primal tie')
            need(winner is not None,'unbounded pivot despite bounded target objective')
            need(self.series_cmp(best,{})>0,'nonpositive formal pivot')
            newB=tuple(winner if k==j else r for k,r in enumerate(B));x=self.point(B);y=self.point(newB)
            need(all(dot(a,y)<=b for a,b in zip(self.A,self.b)),'perturbation collapse infeasible')
            steps.append({'basis':B,'leave_position':j,'enter':winner,'time':t,
                          'alpha_constant':best.get(0,F(0)),'next_basis':newB})
            if x!=y:route.append(self.lift(y))
            B=newB;time=t
        raise ValueError('pivot cap reached; no diameter or algorithmic runtime conclusion')


def construct(data,attempts=12,limit=20000):
    P=SignedModel(data);failures=[]
    for seed in range(attempts):
        try:cert=serial(P.one_attempt(seed,limit));return {'certificate':cert,'verified':verify(data,cert),'retry_failures':failures}
        except ValueError as e:
            if 'objective tie' not in str(e):raise
            failures.append(str(e))
    raise ValueError('generic objective attempt cap; no route certificate returned')


def verify(data,cert):
    """No route discovery. Rechecks all bases, exact shadow events and original edges."""
    P=SignedModel(data);need(cert['input_sha256']==P.digest,'changed input or endpoints')
    need(type(cert['dimension'])is int and cert['dimension']==P.h,'false intrinsic dimension')
    if P.h==0:
        need(not cert['basis_steps'] and cert['route']==[serial(P.start)] and P.start==P.end,'invalid stationary certificate')
        return {'status':'PASS','intrinsic_dimension':0,'edges':0,'basis_pivots':0,'stationary_pivots':0,'row_checks':P.m}
    Bs=tuple(cert['source_basis']);Bt=tuple(cert['target_basis'])
    def valid_basis(B):
        need(len(B)==P.h and len(set(B))==P.h and all(type(i)is int and 0<=i<P.m for i in B),'invalid basis labels')
        need(P.feasible_basis(B),'basis not symbolically feasible')
    valid_basis(Bs);valid_basis(Bt)
    need(P.point(Bs)==P.s and P.point(Bt)==P.t,'basis endpoints mismatch')
    ws=tuple(map(rat,cert['source_weights']));wt=tuple(map(rat,cert['target_weights']))
    need(len(ws)==P.h==len(wt) and all(w>0 for w in ws+wt),'nonpositive exposing weights')
    c0=tuple(map(rat,cert['source_objective']));c1=tuple(map(rat,cert['target_objective']))
    for c,w,B in [(c0,ws,Bs),(c1,wt,Bt)]:
        need(len(c)==P.h and c==tuple(sum((w[k]*P.A[r][j] for k,r in enumerate(B)),F(0)) for j in range(P.h)), 'false exposing objective')
    B=Bs;t0=F(0);route=[P.start];stationary=0;half=0;rowchecks=0
    for step in cert['basis_steps']:
        need(tuple(step['basis'])==B,'broken basis chain')
        inv=P.inverse(B);half+=int(any(abs(v)==F(1,2) for r in inv for v in r))
        t=rat(step['time']);j=step['leave_position'];enter=step['enter']
        need(type(j)is int and 0<=j<P.h and type(enter)is int and 0<=enter<P.m,'invalid pivot labels')
        need(t0<=t<1,'invalid objective time')
        l0=P.coefficients(c0,inv);ld=P.coefficients(tuple(v-u for u,v in zip(c0,c1)),inv)
        need(all(a+t0*b>=0 and a+t*b>=0 for a,b in zip(l0,ld)), 'invalid dual segment')
        need(l0[j]+t*ld[j]==0 and ld[j]<0,'false leaving wall')
        direction=tuple(-r[j] for r in inv);den=dot(P.A[enter],direction)
        need(den>0,'entering row does not block')
        chosen=P.ratio_series(B,enter,inv,den)
        need(P.series_cmp(chosen,{})>0,'nonpositive symbolic step')
        for r,a in enumerate(P.A):
            denominator=dot(a,direction)
            if denominator>0:need(P.series_cmp(chosen,P.ratio_series(B,r,inv,denominator))<=0,'wrong lexicographic ratio')
        need(rat(step['alpha_constant'])==chosen.get(0,F(0)),'forged real step length')
        newB=tuple(enter if k==j else r for k,r in enumerate(B))
        need(tuple(step['next_basis'])==newB,'false basis update');valid_basis(newB)
        x=P.lift(P.point(B));y=P.lift(P.point(newB))
        for p in (x,y):
            need(all(dot(a,p)<=b for a,b in zip(P.originalA,P.originalb)),'infeasible original point');rowchecks+=P.m
        if x==y:stationary+=1
        else:
            common=[i for i,(a,b) in enumerate(zip(P.fullA,P.fullb)) if dot(a,tuple(v/s for v,s in zip(x,P.scale)))==b==dot(a,tuple(v/s for v,s in zip(y,P.scale)))]
            need(signed_kernel([P.fullA[i] for i in common],P.d)['rank']==P.d-1,'original step is not an edge')
            need(dot(P.originalA[B[j]],x)==P.originalb[B[j]] and dot(P.originalA[B[j]],y)<P.originalb[B[j]],'missing original leaving blocker')
            need(dot(P.originalA[enter],y)==P.originalb[enter] and dot(P.originalA[enter],x)<P.originalb[enter],'missing original entering blocker')
            route.append(y)
        B=newB;t0=t
    need(tuple(cert['final_basis'])==B,'false final basis')
    need(all(v>=0 for v in P.coefficients(c1,P.inverse(B))),'final objective not optimal')
    need(P.lift(P.point(B))==P.end,'wrong final endpoint')
    need([tuple(map(rat,p)) for p in cert['route']]==route,'false reported route')
    need(all(all(dot(a,p)==b for a,b in [(P.originalA[i],P.originalb[i]) for i in P.common]) for p in route),'lost common facet')
    return {'status':'PASS','ambient_dimension':P.d,'intrinsic_dimension':P.h,'rows':P.m,'edges':len(route)-1,
            'basis_pivots':len(cert['basis_steps']),'stationary_pivots':stationary,'half_integral_basis_visits':half,
            'row_checks':rowchecks,'classical_safe_diameter_bound':36*P.h**3,
            'within_safe_bound':len(route)-1<=36*P.h**3,
            'scope':'Exact ORIGINAL-polyhedron edge certificate. Sampled objectives do not implement the cited expected-length distribution.'}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path);ap.add_argument('--certificate',type=Path);ap.add_argument('--output',type=Path);ap.add_argument('--limit',type=int,default=20000)
    args=ap.parse_args()
    try:
        data=json.loads(args.input.read_text());out=verify(data,json.loads(args.certificate.read_text())) if args.certificate else construct(data,limit=args.limit)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError)as e:ap.exit(2,f'No certificate: {e}\n')
if __name__=='__main__':main()
