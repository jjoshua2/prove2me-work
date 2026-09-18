#!/usr/bin/env python3
"""Exact tests for the separate all-endpoint monotone Lean candidate.

Discovery uses only the original inequalities at each visited vertex, not the
reference graph. The latter is used only for independent small-model checks.
"""
from fractions import Fraction as Q
from itertools import combinations
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random
import test_moment_release_pivots as pivot
import test_moment_root_catalogue as roots


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x


def save(path,x):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(serial(x),sort_keys=True,indent=2)+'\n')


def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))


def construct(a,d,u,v,cap=1000):
    A=pivot.rows(a,d)
    J=[i for i,r in enumerate(A) if dot(r,v)==1]
    assert len(J)==d and all(dot(r,v)<=1 for r in A)
    R=pivot.inverse([A[i] for i in J]);assert R is not None
    objective=tuple(sum((A[i][j] for i in J),Q(0)) for j in range(d))
    initial=tuple(u);cur=initial;steps=[];seen=set()
    while cur!=tuple(v):
        assert len(steps)<cap and cur not in seen
        seen.add(cur)
        I=[i for i,r in enumerate(A) if dot(r,cur)==1]
        assert len(I)==d and all(dot(r,cur)<=1 for r in A)
        B=pivot.inverse([A[i] for i in I]);assert B is not None
        directions=[tuple(-r[j] for r in B) for j in range(d)]
        coeff=[1-dot(A[i],v) for i in I]
        assert all(c>=0 for c in coeff)
        assert tuple(sum((c*w[j] for c,w in zip(coeff,directions)),Q(0)) for j in range(d))==tuple(t-s for s,t in zip(cur,v))
        chosen=next(j for j in range(d) if coeff[j]>0 and dot(objective,directions[j])>0)
        record=pivot.make(a,d,cur,I[chosen]);steps.append(record);cur=tuple(record['v'])
    result=dict(a=a,dimension=d,start=initial,target=v,target_active=J,target_inverse=R,steps=steps)
    verify(result)
    return result


def verify(c):
    a=tuple(map(Q,c['a']));d=c['dimension'];u=tuple(map(Q,c['start']));v=tuple(map(Q,c['target']))
    assert type(d)is int and 0<=d<len(a) and len(set(a))==len(a)
    assert len(u)==len(v)==d
    A=pivot.rows(a,d);J=c['target_active'];R=[tuple(map(Q,r)) for r in c['target_inverse']]
    assert J==[i for i,r in enumerate(A) if dot(r,v)==1] and len(J)==d
    assert len(R)==d and all(len(r)==d for r in R) and all(dot(r,v)<=1 for r in A)
    assert all(sum((A[J[i]][k]*R[k][j] for k in range(d)),Q(0))==int(i==j) for i in range(d) for j in range(d))
    objective=tuple(sum((A[i][j] for i in J),Q(0)) for j in range(d))
    cur=u;seen={u};decompositions=0
    for s in c['steps']:
        assert tuple(map(Q,s['a']))==a and s['dimension']==d and tuple(map(Q,s['u']))==cur
        pivot.verify(s)
        nxt=tuple(map(Q,s['v']));assert dot(objective,nxt)>dot(objective,cur)
        I=s['I'];p=s['p'];B=[tuple(map(Q,r)) for r in s['inverse']]
        coeff=[1-dot(A[i],v) for i in I]
        directions=[tuple(-r[j] for r in B) for j in range(d)]
        assert all(t>=0 for t in coeff)
        assert tuple(sum((t*w[j] for t,w in zip(coeff,directions)),Q(0)) for j in range(d))==tuple(t-s for s,t in zip(cur,v))
        assert coeff[I.index(p)]>0 and dot(objective,tuple(map(Q,s['w'])))>0
        assert all(dot(A[i],nxt)==1 for i in set(I)&set(J))
        assert nxt not in seen;seen.add(nxt);cur=nxt;decompositions+=1
    assert cur==v and len(c['steps'])<__import__('math').comb(len(a),d)
    return dict(status='PASS',edges=len(c['steps']),decompositions=decompositions,vertices=len(seen),
                acquired_target_rows_never_lost=True)


def reference(a,d):
    A=pivot.rows(a,d);V={};systems=0
    for I in combinations(range(len(a)),d):
        systems+=1;x,rank,inconsistent=roots.square_solve([A[i] for i in I],[Q(1)]*d)
        if x is None or any(dot(r,x)>1 for r in A):continue
        J={i for i,r in enumerate(A) if dot(r,x)==1};assert len(J)==d
        V[x]=J
    G={x:set() for x in V}
    for x,y in combinations(V,2):
        common=sorted(V[x]&V[y])
        if len(common)==d-1:
            import sympy as sp
            assert sp.Matrix([A[i] for i in common]).rank()==d-1
            G[x].add(y);G[y].add(x)
    return V,G,systems


def distance(G,u,v):
    q=deque([u]);D={u:0}
    while q:
        x=q.popleft()
        if x==v:return D[x]
        for y in G[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    raise AssertionError('disconnected reference')


def small(out):
    rng=random.Random(301);records=[];stats=dict(models=0,systems=0,vertices=0,routes=0,edges=0,shortest_edges=0,nonshortest=0,target_losses=0)
    saved=[]
    for d,m in [(0,2),(1,4),(2,5),(3,6),(4,7),(4,8),(5,8),(6,9)]:
        a=[Q(n,7) for n in rng.sample(range(-40,60),m)]
        V,G,systems=reference(a,d)
        pairs=[(u,v) for u in V for v in V];rng.shuffle(pairs);pairs=pairs[:60]
        local=dict(dimension=d,labels=m,vertices=len(V),systems=systems,routes=0,edges=0,shortest_edges=0,nonshortest=0,max_length=0)
        for u,v in pairs:
            c=construct(a,d,u,v);r=verify(c);D=distance(G,u,v)
            for step in c['steps']:assert tuple(step['v']) in G[tuple(step['u'])]
            assert r['edges']>=D
            local['routes']+=1;local['edges']+=r['edges'];local['shortest_edges']+=D;local['nonshortest']+=r['edges']>D;local['max_length']=max(local['max_length'],r['edges'])
            if not any(s['dimension']==d and len(s['a'])==m for s in saved) or r['edges']>D and not any(s.get('adverse') for s in saved):
                c['reference_distance']=D;c['adverse']=r['edges']>D;saved.append(c)
        stats['models']+=1;stats['systems']+=systems;stats['vertices']+=len(V)
        for key in ['routes','edges','shortest_edges','nonshortest']:stats[key]+=local[key]
        records.append(local)
    save(out/'small-fixtures.json',saved)
    return dict(status='PASS',stats=stats,models=records,scope='Exact finite tests, not formal verification or a polynomial step bound.')


def large(out):
    saved=[];records=[]
    for d in [8,12,16]:
        m=2*d+1;a=list(map(Q,range(m)))
        rootsets=[tuple(range(d)),tuple([0,m-1]+list(range(2,d))),tuple(j for i in range(d//2) for j in [3*i,3*i+1])]
        vertices=[]
        for S in rootsets:
            c=roots.candidate(a,d,tuple(sorted(S)));assert c['status']=='VERTEX';vertices.append(tuple(map(Q,c['point'])))
        for u,v in [(vertices[0],vertices[1]),(vertices[1],vertices[2])]:
            c=construct(a,d,u,v);saved.append(c);records.append(dict(dimension=d,labels=m,**verify(c)))
    save(out/'large-fixtures.json',saved)
    return dict(status='PASS',records=records,scope='Selected actual routes only; no full large graph enumeration.')


def audit(out):
    fixtures=json.loads((out/'small-fixtures.json').read_text())+json.loads((out/'large-fixtures.json').read_text())
    oldmake,oldinverse=pivot.make,pivot.inverse;oldconstruct=globals()['construct']
    def forbidden(*args,**kwargs):raise AssertionError('discovery called in verifier')
    try:
        pivot.make=pivot.inverse=globals()['construct']=forbidden
        checks=[verify(c) for c in fixtures]
    finally:pivot.make,pivot.inverse,globals()['construct']=oldmake,oldinverse,oldconstruct
    sample=next(c for c in fixtures if len(c['steps'])>1)
    bad=[]
    for name,change in [
      ('false target',lambda c:c['target'].__setitem__(0,'999')),
      ('wrong target inverse',lambda c:c['target_inverse'][0].__setitem__(0,'999')),
      ('omitted step',lambda c:c['steps'].pop(0)),
      ('loop',lambda c:c['steps'].append(deepcopy(c['steps'][0]))),
      ('nonfirst blocker',lambda c:c['steps'][0].__setitem__('t','999')),
      ('wrong direction',lambda c:c['steps'][0]['w'].__setitem__(0,'999'))]:
        c=deepcopy(sample);change(c)
        try:verify(c)
        except (AssertionError,ValueError,IndexError,ZeroDivisionError):bad.append(name)
        else:raise AssertionError('forgery accepted '+name)
    return dict(status='PASS',records=len(checks),edges=sum(c['edges'] for c in checks),discovery_disabled=True,rejected=bad)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['small','large','audit'],required=True);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    report=globals()[args.stage](args.out)
    report['sources']={f:hashlib.sha256((Path(__file__).parent/f).read_bytes()).hexdigest() for f in ['test_moment_monotone_routes.py','test_moment_release_pivots.py','test_moment_root_catalogue.py']}
    save(args.out/(args.stage+'.json'),report);print(json.dumps(serial(report),sort_keys=True))
if __name__=='__main__':main()
