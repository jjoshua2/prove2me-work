#!/usr/bin/env python3
"""Exact finite regression for the separate Lean original-H/compact-summand theorem.
Uses the unchanged #309 hull/edge routines as an independent sum reference.
"""
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse, json, hashlib, random
import test_summand_contraction as old


def hrows(P):
    if len(P)==1:
        p=P[0];return [((F(1),F(0)),p[0]),((F(-1),F(0)),-p[0]),
                       ((F(0),F(1)),p[1]),((F(0),F(-1)),-p[1])]
    if len(P)==2:
        x,y=P;D=old.sub(y,x);n=(D[1],-D[0])
        return [(n,old.dot(n,x)),(tuple(-a for a in n),-old.dot(n,x)),
                (D,old.dot(D,y)),(tuple(-a for a in D),-old.dot(D,x))]
    rows=[]
    for p,q in zip(P,P[1:]+P[:1]):
        D=old.sub(q,p);a=(D[1],-D[0]);rows.append((a,old.dot(a,p)))
    return rows


def vertices_from_rows(rows):
    result=set()
    for (a,b),(c,d) in combinations(rows,2):
        det=a[0]*c[1]-a[1]*c[0]
        if not det:continue
        x=((b*c[1]-a[1]*d)/det,(a[0]*d-b*c[0])/det)
        if all(old.dot(e,x)<=f for e,f in rows):result.add(x)
    return result


def expose_lex(face,q):
    # Strictly favors lexicographic maximum within this finite maximizing face.
    deltas=[q[0]-x[0] for x in face if x[0]<q[0]]
    spread=max([abs(q[1]-x[1]) for x in face]+[F(0)])
    eta=min(deltas)/(2*(1+spread)) if deltas else F(1)
    g=(F(1),eta)
    assert all(x==q or old.dot(g,x)<old.dot(g,q) for x in face)
    return g


def lift(rows,P,Q,u,rays=()):
    active=[a for a,b in rows if old.dot(a,u)==b]
    f=tuple(sum((a[j] for a in active),F(0)) for j in range(2))
    top=max(old.dot(f,y) for y in Q);face=[y for y in Q if old.dot(f,y)==top]
    q=max(face);g=expose_lex(face,q)
    # An independently checkable strict exposure of this chosen sum point.
    bounds=[F(1)]
    for x in P:
        if x!=u:
            gap=old.dot(f,old.sub(u,x));assert gap>0
            bounds.append(gap/(2*(1+abs(old.dot(g,old.sub(u,x))))))
    for x in Q:
        gap=top-old.dot(f,x)
        if gap>0:bounds.append(gap/(2*(1+abs(old.dot(g,old.sub(q,x))))))
    for r in rays:
        gap=-old.dot(f,r);assert gap>0
        bounds.append(gap/(2*(1+abs(old.dot(g,r)))))
    e=min(bounds);support=tuple(f[j]+e*g[j] for j in range(2))
    return dict(rows=rows,P=P,Q=Q,u=u,q=q,z=old.add(u,q),f=f,g=g,epsilon=e,
                support=support,rays=rays,face=face)


def audit(c):
    rows=[(tuple(map(F,a)),F(b)) for a,b in c['rows']]
    P,Q=[list(map(lambda x:tuple(map(F,x)),c[k])) for k in ('P','Q')]
    u,q,z,f,g,s=[tuple(map(F,c[k])) for k in ('u','q','z','f','g','support')]
    rays=[tuple(map(F,x)) for x in c['rays']];e=F(c['epsilon'])
    assert u in P and q in Q and z==old.add(u,q) and e>0
    assert all(old.dot(a,u)<=b for a,b in rows)
    active=[a for a,b in rows if old.dot(a,u)==b]
    assert f==tuple(sum((a[j] for a in active),F(0)) for j in range(2))
    assert all(x==u or old.dot(f,x)<old.dot(f,u) for x in P)
    top=max(old.dot(f,x) for x in Q);face=[x for x in Q if old.dot(f,x)==top]
    assert q in face and sorted(face)==sorted(tuple(map(F,x)) for x in c['face'])
    assert all(x==q or old.dot(g,x)<old.dot(g,q) for x in face)
    assert s==tuple(f[j]+e*g[j] for j in range(2))
    assert all(x==u or old.dot(s,x)<old.dot(s,u) for x in P)
    assert all(x==q or old.dot(s,x)<old.dot(s,q) for x in Q)
    assert all(old.dot(s,r)<0 and all(old.dot(a,r)<=0 for a,b in rows) for r in rays)
    assert all((x==u and y==q) or old.dot(s,old.add(x,y))<old.dot(s,z) for x in P for y in Q)
    return dict(sum_generator_comparisons=len(P)*len(Q),active_rows=len(active),face_size=len(face))


def run():
    rng=random.Random(310);counts=Counter();saved=[];models=[]
    square=[(F(0),F(0)),(F(1),F(0)),(F(1),F(1)),(F(0),F(1))]
    inputs=[(square,square), ([(0,0),(0,1)],[(F(1,2),0),*square]),
            ([(0,0)],square),(square,[(3,2)]), ([(0,0),(1,0)],[(0,0),(0,1)])]
    for n in range(20):
        P=old.hull([(rng.randrange(-7,8),rng.randrange(-7,8)) for _ in range(7)])
        Q=old.hull([(rng.randrange(-5,6),rng.randrange(-5,6)) for _ in range(6)])
        inputs.append((P,Q))
    for model,(p0,q0) in enumerate(inputs):
        P=old.hull(p0);Q=list(dict.fromkeys(tuple(map(F,x)) for x in q0));Hq=old.hull(Q)
        if len(Hq)>1:Q.append(tuple((Hq[0][j]+Hq[1][j])/2 for j in range(2)))
        rows=hrows(P)
        # Redundant active duplicates, inactive constraints and a zero row.
        rows=[(tuple((i+1)*x for x in a),(i+1)*b) for i,(a,b) in enumerate(rows)]
        rows.extend([rows[0],((F(0),F(0)),F(1))])
        assert vertices_from_rows(rows)==set(P)
        R=old.hull([old.add(p,q) for p in P for q in Q]);lifts={};stat=Counter()
        for u in P:
            rec=lift(rows,P,Q,u);res=audit(rec);lifts[u]=rec['z'];assert rec['q'] in Hq and rec['z'] in R
            assert old.unique_components(P,Q,rec['z'])==(u,rec['q'])
            stat.update(res);stat['lifts']+=1;stat['tied_max_faces']+=res['face_size']>1
            if len(saved)<15:saved.append(rec)
        for u,v in product(P,repeat=2):
            i,j=R.index(lifts[u]),R.index(lifts[v]);n=len(R)
            forward=(j-i)%n;backward=(i-j)%n;direction=1 if forward<=backward else -1
            N=min(forward,backward);walk=[R[(i+direction*k)%n] for k in range(N+1)]
            comp=[old.unique_components(P,Q,z)[0] for z in walk];path=old.contract(comp)
            assert path[0]==u and path[-1]==v and len(path)-1<=N<=len(R)//2
            assert all(old.consecutive(P,x,y) for x,y in zip(path,path[1:]))
            stat['endpoint_pairs']+=1;stat['sum_route_edges']+=N;stat['factor_route_edges']+=len(path)-1
            stat['stationary_steps_removed']+=N-(len(path)-1)
        counts.update(stat);counts['models']+=1;models.append(dict(model=model,P_vertices=len(P),Q_vertices=len(Hq),sum_vertices=len(R),**stat))
    unbounded=[]
    for rows,P,rays in [
        ([((-1,0),0),((0,-1),0)],[(0,0)],[(1,0),(0,1)]),
        ([((-1,0),0),((1,0),1),((0,-1),0)],[(0,0),(1,0)],[(0,1)]),
        ([((-1,0),0),((1,0),0),((0,-1),0)],[(0,0)],[(0,1)])]:
        rows=[(tuple(map(F,a)),F(b)) for a,b in rows];P=[tuple(map(F,x)) for x in P]
        for u in P:
            rec=lift(rows,P,square,u,rays);res=audit(rec);saved.append(rec);unbounded.append(res)
    high=[]
    for d in [0,1,2,8,16,64]:
        for bits in [[0]*d,[i%2 for i in range(d)]]:
            f=[F(i+1) if bit else F(-i-1) for i,bit in enumerate(bits)]
            q=[F(3,2) if bit else F(-1,3) for bit in bits]
            assert all((f[i]>0)==bool(bits[i]) for i in range(d))
            # Compact box support is separable, no vertex enumeration.
            support=sum(max(f[i]*F(-1,3),f[i]*F(3,2)) for i in range(d))
            assert support==sum(f[i]*q[i] for i in range(d))
            high.append(dict(dimension=d,selected_endpoint=True,coordinate_support_checks=d,full_graph_enumerated=False))
    # Retain why compatible extreme selection, not an arbitrary q, is needed.
    assert (F(1),F(1)) not in old.hull([old.add(p,q) for p in square for q in square])
    assert (F(1,2),F(0)) not in old.hull([old.add(p,q) for p in [(0,0),(0,1)] for q in square])
    old_funcs={n:getattr(old,n) for n in ('hull','unique_components','contract')}
    def forbidden(*a,**k):raise AssertionError('discovery during saved audit')
    try:
        for n in old_funcs:setattr(old,n,forbidden)
        for c in saved:audit(c)
    finally:
        for n,f in old_funcs.items():setattr(old,n,f)
    base=next(c for c in saved if len(c['P'])>1 and len(c['Q'])>1);bad=[]
    edits=[('wrong sum point',lambda c:c.update(z=(F(123),F(456)))),
           ('wrong active score',lambda c:c.update(f=(F(0),F(0)))),
           ('negative perturbation',lambda c:c.update(epsilon=F(-1))),
           ('false exposing objective',lambda c:c.update(support=(F(0),F(0)))),
           ('omitted maximizer face',lambda c:c.update(face=[]))]
    for name,edit in edits:
        c=deepcopy(base);edit(c)
        try:audit(c)
        except (AssertionError,ValueError):bad.append(name)
        else:raise AssertionError('forgery accepted '+name)
    return dict(status='PASS',counts=dict(counts),models=models,unbounded=unbounded,high_dimensional=high,
                saved_audits=len(saved),construction_disabled=True,rejected=bad,
                countercontrols=['arbitrary summand vertex may not lift','nonextreme face maximizer may not lift'],
                scope='Exact finite supporting checks, not Lean extraction or verification of arbitrary H input/parser.'),saved


def encode(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [encode(v) for v in x]
    return x


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    report,fixtures=run();report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report['dependency_sha256']=hashlib.sha256(Path(old.__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',report),('fixtures.json',fixtures)]:
        (a.out/name).write_text(json.dumps(encode(obj),sort_keys=True,indent=2)+'\n')
    print(json.dumps(report['counts'],sort_keys=True))
if __name__=='__main__':main()
