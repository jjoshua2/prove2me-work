#!/usr/bin/env python3
"""Independently checkable original-edge balls and facet-reentry exclusions.

Producer: exact local tangent-slice enumeration; no supplied vertex graph/SMT.
Consumer: rational identities and finite coverage/closure; no elimination,
inversion, graph search, shortest-path calculation or solver. Exponential
certificate/producer size is possible. This is not Lean-extracted software.
"""
from __future__ import annotations
import argparse
from collections import deque
from fractions import Fraction as Q
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json


def require(p, message):
    if not p: raise ValueError(message)


def rat(x):
    require(isinstance(x,(int,str,Q)) and not isinstance(x,bool), 'inexact rational')
    return Q(x)


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x


def dot(x,y):
    require(len(x)==len(y), 'dot dimensions')
    return sum((a*b for a,b in zip(x,y) if a and b),Q(0))


def parse(data):
    A=tuple(tuple(rat(t) for t in r) for r in data['A']); b=tuple(map(rat,data['b']))
    require(A and A[0] and len(A)==len(b) and all(len(r)==len(A[0]) for r in A), 'invalid H dimensions')
    u=tuple(map(rat,data['start']));v=tuple(map(rat,data['target']))
    require(len(u)==len(v)==len(A[0]), 'endpoint dimensions')
    return A,b,u,v


def binding(A,b,u,v):
    return sha256(json.dumps(serial([A,b,u,v]),separators=(',',':')).encode()).hexdigest()


def active(A,b,x):
    return tuple(i for i,(a,rhs) in enumerate(zip(A,b)) if dot(a,x)==rhs)


def matrix(raw,n,m):
    require(isinstance(raw,(list,tuple)) and len(raw)==n and
            all(isinstance(r,(list,tuple)) and len(r)==m for r in raw), 'matrix dimensions')
    return [list(map(rat,r)) for r in raw]


def inverse_or_kernel(M):
    """PRODUCER ONLY: return full inverse or a nonzero right-kernel vector."""
    n=len(M);T=[list(r)+[Q(i==j) for j in range(n)] for i,r in enumerate(M)]
    piv=[];row=0
    for col in range(n):
        pivot=next((i for i in range(row,n) if T[i][col]),None)
        if pivot is None: continue
        T[row],T[pivot]=T[pivot],T[row];z=T[row][col]
        T[row]=[x/z for x in T[row]]
        for i in range(n):
            if i!=row and T[i][col]:
                z=T[i][col];T[i]=[x-z*y for x,y in zip(T[i],T[row])]
        piv.append(col);row+=1
    if row==n: return {'inverse':[r[n:] for r in T]}
    col=next(i for i in range(n) if i not in piv);x=[Q(0)]*n;x[col]=1
    for i,j in enumerate(piv):x[j]=-T[i][col]
    return {'kernel':x}


def independent_rows(M,d):
    """PRODUCER ONLY."""
    basis=[];piv=[];ids=[]
    for i,row in enumerate(M):
        x=list(row)
        for v,j in zip(basis,piv):
            z=x[j];x=[a-z*b for a,b in zip(x,v)]
        j=next((j for j,z in enumerate(x) if z),None)
        if j is None:continue
        z=x[j];basis.append([a/z for a in x]);piv.append(j);ids.append(i)
        if len(ids)==d:return ids
    raise ValueError('point is not a vertex: active rank below ambient dimension')


def vertex_packet(A,b,x):
    d=len(x);I=active(A,b,x);ids=independent_rows([A[i] for i in I],d)
    J=[I[j] for j in ids]
    return {'point':x,'active':list(I),'basis':J,
            'inverse':inverse_or_kernel([A[i] for i in J])['inverse']}


def check_vertex(A,b,packet):
    d=len(A[0]);x=tuple(map(rat,packet['point']));require(len(x)==d,'point dimension')
    require(all(dot(a,x)<=rhs for a,rhs in zip(A,b)), 'infeasible vertex')
    I=active(A,b,x);require(packet['active']==list(I), 'incomplete active rows')
    J=packet['basis'];require(type(J)is list and len(J)==d and len(set(J))==d and
            all(type(i)is int and i in I for i in J), 'invalid vertex basis')
    R=matrix(packet['inverse'],d,d)
    require(all(sum((A[J[i]][k]*R[k][j] for k in range(d)),Q(0))==int(i==j)
                for i in range(d) for j in range(d)), 'false vertex right inverse')
    return x,I


class Limit(Exception): pass


class Producer:
    def __init__(self,A,b,star_cap=100000,vertex_cap=50000):
        self.A,self.b=A,b;self.d=len(A[0]);self.star_cap=star_cap;self.vertex_cap=vertex_cap
        self.vertices=[];self.by_point={};self.stars={};self.subsets=0
    def vertex(self,x):
        if x not in self.by_point:
            if len(self.vertices)>=self.vertex_cap:raise Limit('vertex_cap')
            self.by_point[x]=len(self.vertices);self.vertices.append(vertex_packet(self.A,self.b,x))
        return self.by_point[x]
    def star(self,j):
        if j in self.stars:return self.stars[j]
        A,b,d=self.A,self.b,self.d;p=self.vertices[j];x=tuple(p['point']);I=p['active']
        count=comb(len(I),d-1)
        if count>self.star_cap:raise Limit('star_subset_cap')
        h=tuple(-sum((A[i][k] for i in I),Q(0)) for k in range(d))
        entries=[];rays=[];index={}
        for J in combinations(I,d-1):
            self.subsets+=1;M=[h]+[A[i] for i in J];w=inverse_or_kernel(M)
            if 'kernel' in w:entries.append({'kind':'singular','kernel':w['kernel']});continue
            R=w['inverse'];r=tuple(R[k][0] for k in range(d))
            bad=next((i for i in I if dot(A[i],r)>0),None)
            if bad is not None:
                entries.append({'kind':'blocked','inverse':R,'violated':bad});continue
            if r not in index:
                rates=[(i,dot(a,r)) for i,a in enumerate(A)]
                ratios=[((b[i]-dot(A[i],x))/z,i) for i,z in rates if z>0]
                if ratios:
                    alpha,block=min(ratios);require(alpha>0,'zero ray step')
                    y=tuple(a+alpha*z for a,z in zip(x,r));target=self.vertex(y)
                    row={'direction':r,'kind':'edge','step':alpha,'blocker':block,'target':target}
                else:row={'direction':r,'kind':'unbounded_ray'}
                index[r]=len(rays);rays.append(row)
            entries.append({'kind':'ray','inverse':R,'ray':index[r]})
        s={'vertex':j,'entries':entries,'rays':rays};self.stars[j]=s;return s


def check_star(A,b,V,s):
    """EVERY active (d-1)-subset is covered; no untrusted neighbor omissions."""
    d=len(A[0]);j=s['vertex'];require(type(j)is int and 0<=j<len(V), 'bad star vertex')
    x,I=V[j];h=tuple(-sum((A[i][k] for i in I),Q(0)) for k in range(d))
    entries=s['entries'];rays=s['rays'];require(len(entries)==comb(len(I),d-1), 'incomplete tangent subset cover')
    seen=set();neigh=set();ray_count=0
    for J,e in zip(combinations(I,d-1),entries):
        M=[h]+[A[i] for i in J]
        if e['kind']=='singular':
            r=tuple(map(rat,e['kernel']));require(len(r)==d and any(r) and all(dot(a,r)==0 for a in M),'false singularity witness')
            continue
        require(e['kind'] in ('blocked','ray'),'unknown subset type')
        R=matrix(e['inverse'],d,d)
        require(all(sum((M[i][k]*R[k][q] for k in range(d)),Q(0))==int(i==q)
                    for i in range(d) for q in range(d)), 'false slice inverse')
        r=tuple(R[k][0] for k in range(d))
        if e['kind']=='blocked':
            i=e['violated'];require(type(i)is int and i in I and dot(A[i],r)>0,'false infeasible slice point')
        else:
            require(all(dot(A[i],r)<=0 for i in I),'infeasible tangent ray')
            q=e['ray'];require(type(q)is int and 0<=q<len(rays),'missing ray')
            require(tuple(map(rat,rays[q]['direction']))==r,'wrong normalized ray')
            seen.add(q)
    require(seen==set(range(len(rays))),'unbound outgoing ray')
    require(len({tuple(map(rat,r['direction'])) for r in rays})==len(rays),'duplicate normalized ray')
    for r in rays:
        direction=tuple(map(rat,r['direction']))
        rates=[dot(a,direction) for a in A]
        if r['kind']=='unbounded_ray':
            require(all(z<=0 for z in rates),'ray has an omitted finite blocker');ray_count+=1;continue
        require(r['kind']=='edge','invalid outgoing type')
        alpha=rat(r['step']);i=r['blocker'];q=r['target']
        require(alpha>0 and type(q)is int and 0<=q<len(V),'invalid finite step')
        y,_=V[q];require(y==tuple(a+alpha*z for a,z in zip(x,direction)),'wrong neighbor endpoint')
        require(type(i)is int and 0<=i<len(A) and rates[i]>0 and
                b[i]-dot(A[i],x)==alpha*rates[i], 'false maximal-step blocker')
        require(all(b[k]-dot(A[k],x)>=alpha*z for k,z in enumerate(rates)), 'step crosses an original row')
        neigh.add(q)
    return neigh,ray_count,len(entries)


def solve(data,budget=None,max_reentries=None,state_cap=50000,star_cap=100000,vertex_cap=50000):
    """No graph input. budget=None requires an explicit reentry restriction.
    Restricted EXCLUDED means no walk meeting THAT restriction, not no path.
    """
    A,b,u,v=parse(data)
    require(budget is None or type(budget)is int and budget>=0,'bad length budget')
    require(max_reentries is None or type(max_reentries)is int and max_reentries>=0,'bad reentry budget')
    require(budget is not None or max_reentries is not None,'need a finite-length or finite-state restriction')
    require(all(type(c)is int and c>=0 for c in (state_cap,star_cap,vertex_cap)), 'bad cap')
    target=vertex_packet(A,b,v);P=Producer(A,b,star_cap,vertex_cap)
    try:
        root=P.vertex(u);states=[(root,(),0)];depth=[0];pos={states[0]:0};pred=[None];queue=deque([0]);found=None
        while queue:
            s=queue.popleft();j,left,used=states[s];x=tuple(P.vertices[j]['point'])
            if x==v:found=s;break
            if budget is not None and depth[s]==budget:continue
            star=P.star(j);I=set(P.vertices[j]['active'])
            for r in star['rays']:
                if r['kind']!='edge':continue
                q=r['target'];J=set(P.vertices[q]['active'])
                if max_reentries is None:key=(q,(),0)
                else:
                    new_used=used+len((J-I)&set(left))
                    if new_used>max_reentries:continue
                    key=(q,tuple(sorted(set(left)|(I-J))),new_used)
                if key not in pos:
                    if len(states)>=state_cap:raise Limit('state_cap')
                    pos[key]=len(states);states.append(key);depth.append(depth[s]+1);pred.append(s);queue.append(len(states)-1)
        if found is not None:
            walk=[];s=found
            while s is not None:walk.append(states[s][0]);s=pred[s]
            walk.reverse();cert={'format':'original-route-witness-v1','input_sha256':binding(A,b,u,v),
                'vertices':[P.vertices[j] for j in walk], 'length':len(walk)-1}
            add_path_inverses(A,cert)
            return {'status':'FOUND','certificate':serial(cert),'verified':verify_path(data,serial(cert)),
                    'producer':{'local_stars':len(P.stars),'slice_subsets':P.subsets,'states':len(states)}}
        cert={'format':'original-route-exclusion-v1','input_sha256':binding(A,b,u,v),
              'budget':budget,'max_row_reentries':max_reentries,'target':target,
              'vertices':P.vertices,'stars':[P.stars[j] for j in sorted(P.stars)],
              'states':[{'vertex':j,'left':list(left),'used':used,'depth':z} for (j,left,used),z in zip(states,depth)]}
        cert=serial(cert)
        return {'status':'EXCLUDED','certificate':cert,'verified':verify_exclusion(data,cert),
                'producer':{'local_stars':len(P.stars),'slice_subsets':P.subsets,'states':len(states)}}
    except Limit as e:
        return {'status':'UNKNOWN','reason':str(e),'producer':{'local_stars':len(P.stars),'slice_subsets':P.subsets,'states':len(locals().get('states',[]))}}


def verify_path(data,c):
    A,b,u,v=parse(data);require(c['format']=='original-route-witness-v1' and c['input_sha256']==binding(A,b,u,v),'wrong path binding')
    V=[check_vertex(A,b,p) for p in c['vertices']]
    require(V and V[0][0]==u and V[-1][0]==v and c['length']==len(V)-1,'wrong path endpoints/length')
    # The producer supplies a right inverse for d-1 shared tight rows.
    # Multiplication verifies their independence; the consumer never performs
    # elimination, including at nonsimple or lower-dimensional vertices.
    edges=c.get('edges')
    require(edges is not None and len(edges)==len(V)-1,'missing path edge inverse')
    debt=0;left=set()
    for (x,I),(y,J),e in zip(V,V[1:],edges):
        require(x!=y,'stationary recorded edge');K=e['rows'];d=len(x)
        require(len(K)==d-1 and len(set(K))==d-1 and all(type(i)is int and i in I and i in J for i in K),'wrong common rows')
        S=matrix(e['right_inverse'],d,d-1)
        require(all(sum((A[K[i]][k]*S[k][j] for k in range(d)),Q(0))==int(i==j)
                    for i in range(d-1) for j in range(d-1)), 'false edge rank')
        debt+=len((set(J)-set(I))&left);left|=set(I)-set(J)
    return {'status':'PASS','original_edges':len(V)-1,'original_row_reentries':debt}


def add_path_inverses(A,c):
    """PRODUCER ONLY. Pad common rows to a square invertible matrix."""
    d=len(A[0]);out=[]
    for p,q in zip(c['vertices'],c['vertices'][1:]):
        I=sorted(set(p['active'])&set(q['active']))
        # independent_rows requires d rows; extend by standard coordinate rows.
        M=[A[i] for i in I]+[tuple(Q(i==j) for j in range(d)) for i in range(d)]
        ids=independent_rows(M,d);common=[j for j in ids if j<len(I)]
        require(len(common)==d-1,'generated path has wrong edge dimension')
        order=common+[j for j in ids if j>=len(I)];R=inverse_or_kernel([M[j] for j in order])['inverse']
        out.append({'rows':[I[j] for j in common],'right_inverse':[r[:d-1] for r in R]})
    c['edges']=out


def verify_exclusion(data,c):
    A,b,u,v=parse(data);m=len(A)
    require(c['format']=='original-route-exclusion-v1' and c['input_sha256']==binding(A,b,u,v),'changed exclusion input')
    L=c['budget'];B=c['max_row_reentries']
    require(L is None or type(L)is int and L>=0,'bad length bound')
    require(B is None or type(B)is int and B>=0,'bad reentry bound')
    require(L is not None or B is not None,'unrestricted closure is not supported by this format')
    require(check_vertex(A,b,c['target'])[0]==v,'target is not the input vertex')
    V=[check_vertex(A,b,p) for p in c['vertices']]
    require(len({x for x,I in V})==len(V),'duplicate original vertex')
    states=c['states'];require(states,'empty coverage')
    lookup={};depth=[]
    for n,s in enumerate(states):
        j,left,used,z=s['vertex'],s['left'],s['used'],s['depth']
        require(type(j)is int and 0<=j<len(V) and type(z)is int and z>=0 and (L is None or z<=L),'invalid state/depth')
        require(type(left)is list and left==sorted(set(left)) and all(type(i)is int and 0<=i<m for i in left),'bad left-row memory')
        require(type(used)is int and used>=0 and (B is None and not left and used==0 or B is not None and used<=B),'bad reentry state')
        key=(j,tuple(left),used);require(key not in lookup,'duplicate reachability state');lookup[key]=n;depth.append(z)
        require(V[j][0]!=v,'excluded target appears in coverage')
    require(states[0]=={'vertex':0,'left':[],'used':0,'depth':0} and V[0][0]==u,'wrong root state')
    neighbors={};rays=subsets=0
    for s in c['stars']:
        j=s['vertex'];require(j not in neighbors,'duplicate star')
        neighbors[j],r,count=check_star(A,b,V,s);rays+=r;subsets+=count
    needed={s['vertex'] for s in states if L is None or s['depth']<L}
    require(set(neighbors)==needed,'missing/extra expanded star')
    transitions=0;rejected=0
    for n,s in enumerate(states):
        if L is not None and depth[n]==L:continue
        j=s['vertex'];I=set(V[j][1]);left=set(s['left'])
        for q in neighbors[j]:
            J=set(V[q][1]);used=s['used']+len((J-I)&left)
            if B is not None and used>B:rejected+=1;continue
            key=(q,tuple(sorted(left|(I-J))),used) if B is not None else (q,(),0)
            require(key in lookup,'uncovered permitted successor')
            require(depth[lookup[key]]<=depth[n]+1,'successor assigned too deep')
            transitions+=1
    return {'status':'PASS','conclusion':'no route satisfying the stated bounds',
        'length_budget':L,'max_original_row_reentries':B,'vertices_in_certificate':len(V),
        'covered_states':len(states),'complete_stars':len(neighbors),'slice_subsets':subsets,
        'unbounded_edge_rays':rays,'closure_transitions':transitions,'forbidden_reentry_transitions':rejected,
        'scope':'Rational finite certificate check; not Lean verification. Row reentries are facet reentries only for genuine-facet presentations.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--budget',type=int)
    p.add_argument('--reentries',type=int);p.add_argument('--verify',type=Path);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();data=json.loads(a.input.read_text())
    if a.verify:
        c=json.loads(a.verify.read_text());r=verify_path(data,c) if c['format']=='original-route-witness-v1' else verify_exclusion(data,c)
    else:r=solve(data,a.budget,a.reentries)
    a.output.write_text(json.dumps(serial(r),sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
