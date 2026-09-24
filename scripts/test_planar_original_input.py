#!/usr/bin/env python3
"""Exact original-H tests for chart-free planar half-row routing.

Standard-library Fraction arithmetic; not Lean-extracted code. The mathematical
proof is independent of this generator, parser, enumerator, and checker.
"""
from __future__ import annotations
import argparse, copy, hashlib, json
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path


def need(ok, why):
    if not ok: raise ValueError(why)


def dot(a,b): return sum((x*y for x,y in zip(a,b)), Q(0))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def cross(a,b): return a[0]*b[1]-a[1]*b[0]

def enc(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):enc(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [enc(v) for v in x]
    return x


def hull(points):
    p=sorted(set(tuple(map(Q,z)) for z in points))
    if len(p)<=1: return p
    def chain(seq):
        out=[]
        for x in seq:
            while len(out)>1 and cross(sub(out[-1],out[-2]),sub(x,out[-1]))<=0: out.pop()
            out.append(x)
        return out
    return chain(p)[:-1]+chain(p[::-1])[:-1]


def rows_for(points):
    v=hull(points)
    need(len(v)>=3,'rows_for requires a genuine polygon')
    return [(*((y[1]-x[1],x[0]-y[0])),dot((y[1]-x[1],x[0]-y[0]),x))
            for x,y in zip(v,v[1:]+v[:1])]


def complete_vertices(rows):
    R=[tuple(map(Q,r)) for r in rows]
    # In 2D any nonzero closed polyhedral recession cone contains one of these
    # boundary directions, unless there are no effective normals (basis tests).
    candidates=[(Q(1),Q(0)),(Q(-1),Q(0)),(Q(0),Q(1)),(Q(0),Q(-1))]
    for a,b,c in R:
        if a or b: candidates += [(b,-a),(-b,a)]
    need(not any(any(d) and all(dot(r[:2],d)<=0 for r in R) for d in candidates),
         'unbounded original H-system')
    v=set()
    for r,s in combinations(R,2):
        det=cross(r[:2],s[:2])
        if not det: continue
        z=((r[2]*s[1]-r[1]*s[2])/det,(r[0]*s[2]-r[2]*s[0])/det)
        if all(dot(a[:2],z)<=a[2] for a in R): v.add(z)
    need(v,'empty original H-system')
    return sorted(v)


def graph(rows,v):
    g=[set() for _ in v]
    for i,j in combinations(range(len(v)),2):
        shared=[r for r in rows if any(r[:2]) and dot(r[:2],v[i])==r[2]==dot(r[:2],v[j])]
        if shared: g[i].add(j);g[j].add(i)
    return g


def distances(g,t):
    d={t:0};todo=deque([t])
    while todo:
        i=todo.popleft()
        for j in g[i]:
            if j not in d: d[j]=d[i]+1;todo.append(j)
    return d


def produce(name, rows, generators, targets=None):
    R=[tuple(map(Q,r)) for r in rows];C=[tuple(map(Q,c)) for c in generators]
    V=complete_vertices(R)
    need(set(hull(C))==set(V),'finite-hull identity fails')
    active=[[i for i,r in enumerate(R) if any(r[:2]) and dot(r[:2],x)==r[2]] for x in V]
    slices=[[j for j,x in enumerate(V) if dot(r[:2],x)==r[2]] if any(r[:2]) else [] for r in R]
    need(all(len(a)>=2 for a in active),'active nonzero rank/incidence bound')
    need(all(len(s)<=2 for s in slices),'row-line vertex bound')
    incidence=sum(map(len,active));need(incidence==sum(map(len,slices)) and 2*len(V)<=incidence<=2*len(R),'double counting failed')
    records=[]
    for t in (range(len(V)) if targets is None else targets):
        h=tuple(-sum((Q(k+1)*R[i][j] for k,i in enumerate(active[t])),Q(0)) for j in range(2))
        e=(-h[1],h[0]);P=V[t]
        non=[i for i in range(len(V)) if i!=t]
        if non:
            need(any(h),'zero strict exposure')
            heights={i:dot(h,sub(V[i],P)) for i in non}
            need(all(x>0 for x in heights.values()),'exposure is not strict')
            w={i:dot(e,sub(V[i],P))/heights[i] for i in non}
            order=sorted(non,key=w.get)
            need(len(set(w.values()))==len(non),'radial coordinate collision')
        else: order=[]
        routes=[]
        for u in range(len(V)):
            if u==t: path=[t]
            else:
                k=order.index(u)
                left=list(reversed(order[:k+1]))+[t]
                right=order[k:]+[t]
                path=left if len(left)<=len(right) else right
            need(2*(len(path)-1)<=len(R),'half-row bound')
            routes.append(dict(source=u,path=path,length=len(path)-1))
        records.append(dict(target=t,h=h,e=e,order=order,routes=routes))
    return dict(name=name,rows=R,generators=C,vertices=V,nonzero_active=active,row_slices=slices,records=records)


def audit(c):
    """Independent consumer reconstructs original vertices and edge adjacency.
    It does not call produce, choose an exposure, or generate either boundary arc.
    """
    R=[tuple(map(Q,r)) for r in c['rows']];C=[tuple(map(Q,z)) for z in c['generators']]
    V=[tuple(map(Q,z)) for z in c['vertices']]
    need(V==complete_vertices(R) and set(hull(C))==set(V),'incomplete/false vertex or finite-hull input')
    A=[[i for i,r in enumerate(R) if any(r[:2]) and dot(r[:2],x)==r[2]] for x in V]
    S=[[j for j,x in enumerate(V) if dot(r[:2],x)==r[2]] if any(r[:2]) else [] for r in R]
    need(A==c['nonzero_active'] and S==c['row_slices'],'false original-row incidences')
    need(all(len(a)>=2 for a in A) and all(len(s)<=2 for s in S),'incidence degree bounds')
    need(sum(map(len,A))==sum(map(len,S)) and len(V)<=len(R),'incidence cardinality bound')
    G=graph(R,V);nr=ne=neq=0
    for rec in c['records']:
        t=rec['target'];need(0<=t<len(V),'target missing')
        h=tuple(map(Q,rec['h']));e=tuple(map(Q,rec['e']));order=rec['order']
        need(sorted(order)==[i for i in range(len(V)) if i!=t],'incomplete source ordering')
        if order:
            need(cross(h,e)!=0,'dependent coordinates')
            H=[dot(h,sub(V[i],V[t])) for i in order];need(all(a>0 for a in H),'invalid strict numerator')
            w=[dot(e,sub(V[i],V[t]))/a for i,a in zip(order,H)]
            need(all(a<b for a,b in zip(w,w[1:])),'not strictly sorted')
        need([r['source'] for r in rec['routes']]==list(range(len(V))),'missing source pair')
        d=distances(G,t)
        for r in rec['routes']:
            p=r['path'];L=r['length']
            need(p and p[0]==r['source'] and p[-1]==t,'endpoint mismatch')
            need(L==len(p)-1 and 2*L<=len(R),'incorrect count or bound')
            need(all(0<=i<len(V) for i in p),'nonvertex in route')
            for x,y in zip(p,p[1:]): need(y in G[x] and x!=y,'not a whole original edge')
            # Independent shortest-path comparison is a numerical check only.
            need(L==d[r['source']],'reference distance differs')
            nr+=1;ne+=L;neq+=int(r['source']==t)
    return dict(vertices=len(V),rows=len(R),generators=len(C),targets=len(c['records']),
                routes=nr,edge_occurrences=ne,equal_endpoint_routes=neq,
                nonzero_incidences=sum(map(len,A)),zero_rows=sum(not any(r[:2]) for r in R),
                redundant_generator_count=len(C)-len(V))


def controls(c):
    out=[]
    edits=[('missing generator vertex',lambda z:z['generators'].pop(0)),
           ('false vertex list',lambda z:z['vertices'].pop()),
           ('dependent coordinates',lambda z:z['records'][0].update(e=z['records'][0]['h'])),
           ('zero exposure',lambda z:z['records'][0].update(h=['0','0'])),
           ('missing active incidence',lambda z:z['nonzero_active'][0].pop()),
           ('zero-row false incidences',lambda z:z['row_slices'][-1].extend(range(len(z['vertices'])))),
           ('missing order item',lambda z:z['records'][0]['order'].pop()),
           ('false path length',lambda z:z['records'][0]['routes'][1].update(length=1000)),
           ('wrong endpoint',lambda z:z['records'][0]['routes'][1]['path'].__setitem__(-1,1)),
           ('infeasible generator',lambda z:z['generators'].append(['100000','100000']))]
    for name,fn in edits:
        z=copy.deepcopy(c);fn(z)
        try:audit(z)
        except (ValueError,IndexError,ZeroDivisionError,KeyError):out.append(dict(case=name,rejected=True))
        else: raise AssertionError('accepted corruption: '+name)
    try:complete_vertices([(1,0,1),(-1,0,0),(0,-1,0)])
    except ValueError:out.append(dict(case='unbounded original halfspaces',rejected=True))
    else:raise AssertionError('accepted unbounded carrier')
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--large',action='store_true');args=ap.parse_args()
    fixtures=[];reports=[];bad=[]
    if args.large:
        n=32;P=[(Q(1-t*t,1+t*t),Q(2*t,1+t*t)) for t in range(-15,16)]+[(Q(-1),Q(0))]
        specs=[('circle32_redundant',P,[0,8,16,24])]
    else:
        basics=[('triangle',[(0,0),(3,0),(0,2)]),('square',[(0,0),(2,0),(2,2),(0,2)]),
                ('pentagon',[(-1,2),(0,0),(3,0),(4,2),(2,4)]),
                ('heptagon',[(-3,0),(-2,-2),(1,-3),(4,0),(3,3),(0,5),(-3,3)])]
        specs=[(name,P,None) for name,P in basics]
        for k in range(8):
            name,P=basics[k%4];a=k+1;b=k-2
            specs.append((f'shear_{k}',[(Q(x)+a*Q(y)+Q(1,3),b*Q(x)+(1+a*b)*Q(y)-Q(2,7)) for x,y in P],None))
    for name,P,targets in specs:
        V=hull(P);R=rows_for(P)
        R += [tuple(2*x for x in R[0]),(R[1][0],R[1][1],R[1][2]+7),(0,0,0),(0,0,3)]
        C=list(V)+[tuple((x+y)/2 for x,y in zip(V[i],V[(i+1)%len(V)])) for i in range(len(V))]
        C += [tuple(sum(z[k] for z in V)/len(V) for k in range(2))]
        cert=json.loads(json.dumps(enc(produce(name,R,C,targets))))
        report=audit(cert);report['name']=name;fixtures.append(cert);reports.append(report)
        if name=='square':bad=controls(cert)
    if not args.large:
        for name,R,C in [('segment',[(1,0,2),(-1,0,0),(0,1,0),(0,-1,0),(0,0,0)],[(0,0),(2,0),(1,0)]),
                         ('point',[(1,0,0),(0,1,0),(-1,-1,0),(0,0,0)],[(0,0)])]:
            cert=json.loads(json.dumps(enc(produce(name,R,C))))
            report=audit(cert);report['name']=name;fixtures.append(cert);reports.append(report)
    totals={k:sum(r[k] for r in reports) for k in ['vertices','rows','generators','targets','routes','edge_occurrences','equal_endpoint_routes','nonzero_incidences','zero_rows','redundant_generator_count']}
    result=dict(kind='exact_rational_supporting_tests_not_Lean',models=reports,totals=totals,controls=bad)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.out/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
    print(json.dumps(dict(totals=totals,controls=len(bad))))

if __name__=='__main__':main()
