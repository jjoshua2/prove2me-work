#!/usr/bin/env python3
"""Exact actual-neighbor transport checks; separate from Lean verification."""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
from copy import deepcopy
import hashlib,json,argparse,random
import test_moment_release_pivots as piv
import test_moment_root_catalogue as roots


def make(a,d,u,v):
    A=piv.rows(a,d); I=[i for i,r in enumerate(A) if piv.dot(r,u)==1]
    J=[i for i,r in enumerate(A) if piv.dot(r,v)==1]
    assert u!=v and len(I)==len(J)==d
    edges=[piv.make(a,d,u,p) for p in I]
    b=[(1-piv.dot(A[p],v))/e['t'] for p,e in zip(I,edges)]
    mass=sum(b,Q(0));f=lambda x:sum((piv.dot(A[i],x) for i in J),Q(0))
    gains=[f(e['v'])-f(u) for e in edges];gap=f(v)-f(u)
    best=max((i for i,c in enumerate(b) if c>0),key=lambda i:gains[i])
    return dict(dimension=d,a=list(a),u=list(u),v=list(v),I=I,J=J,edges=edges,
                weights=b,mass=mass,gains=gains,gap=gap,selected=best)


def verify(c):
    d=c['dimension'];a=list(map(Q,c['a']));u=tuple(map(Q,c['u']));v=tuple(map(Q,c['v']))
    A=piv.rows(a,d);I=c['I'];J=c['J'];edges=c['edges'];b=list(map(Q,c['weights']))
    assert u!=v and len(u)==len(v)==d and len(set(a))==len(a)>d
    assert I==[i for i,r in enumerate(A) if piv.dot(r,u)==1] and len(I)==d
    assert J==[i for i,r in enumerate(A) if piv.dot(r,v)==1] and len(J)==d
    assert all(piv.dot(r,u)<=1 and piv.dot(r,v)<=1 for r in A)
    assert len(edges)==len(b)==d and len(c['gains'])==d
    f=lambda x:sum((piv.dot(A[i],x) for i in J),Q(0))
    gap=f(v)-f(u);mass=sum(b,Q(0));gains=[]
    for p,e,weight in zip(I,edges,b):
        assert tuple(map(Q,e['a']))==tuple(a) and e['dimension']==d and e['p']==p
        assert tuple(map(Q,e['u']))==u
        piv.verify(e)
        assert weight==(1-piv.dot(A[p],v))/Q(e['t']) and weight>=0
        gains.append(f(tuple(map(Q,e['v'])))-f(u))
    assert gap==Q(c['gap']) and gap>0 and mass==Q(c['mass']) and mass>=1
    assert gains==list(map(Q,c['gains']))
    assert all(v[j]-u[j]==sum((b[i]*(Q(e['v'][j])-u[j]) for i,e in enumerate(edges)),Q(0)) for j in range(d))
    assert gap==sum((x*y for x,y in zip(b,gains)),Q(0))
    assert all(gain<=gap for gain in gains)
    p=c['selected']; assert type(p) is int and 0<=p<d and b[p]>0 and gains[p]>0
    assert gap<=mass*gains[p]
    z=tuple(map(Q,edges[p]['v']))
    assert all(piv.dot(A[i],z)==1 for i in set(I)&set(J))
    return dict(edges=d,rows=len(a),mass=str(mass),improvement_fraction=str(gains[p]/gap),
                guarantee=str(1/mass),equality=(mass*gains[p]==gap))


def run():
    models=[(1,[Q(0),Q(1),Q(2)]),(2,list(map(Q,range(5)))),
            (3,list(map(Q,range(6)))),(4,list(map(Q,range(8))))]
    rng=random.Random(303)
    for d,m in [(2,6),(3,7)]:
        a=[Q(j,7) for j in rng.sample(range(-30,60),m)];models.append((d,a))
    stats=dict(models=0,original_square_systems=0,vertices=0,pairs=0,edge_checks=0,
               vector_coordinate_identities=0,sharp_bounds=0,unit_mass=0)
    saved=[];largest=None;reports=[]
    for d,a in models:
        A=roots.row_matrix(a,d);V=[];systems=0
        for S in combinations(range(len(a)),d):
            systems+=1
            x,rank,inconsistent=roots.square_solve([A[i] for i in S],[Q(1)]*d)
            if x is not None and all(roots.dot(r,x)<=1 for r in A):V.append(x)
        assert len(V)==len(set(V))
        count=sharp=0
        for u in V:
            for v in V:
                if u==v:continue
                c=make(a,d,u,v);out=verify(c)
                assert all(tuple(e['v']) in V for e in c['edges'])
                stats['pairs']+=1;count+=1;stats['edge_checks']+=d
                stats['vector_coordinate_identities']+=d
                stats['sharp_bounds']+=out['equality'];sharp+=out['equality']
                stats['unit_mass']+=Q(c['mass'])==1
                if largest is None or c['mass']>largest['mass']:largest=c
                if not any(s['dimension']==d and len(s['a'])==len(a) for s in saved):saved.append(c)
        stats['models']+=1;stats['original_square_systems']+=systems;stats['vertices']+=len(V)
        reports.append(dict(dimension=d,labels=len(a),vertices=len(V),pairs=count,sharp_bounds=sharp))
    # Adversarial spacing test: mass is measured, never postulated small.
    spacing=[]
    for e in [Q(1,2),Q(1,16),Q(1,256),Q(1,2**16)]:
        a=[Q(0),e,Q(1),Q(2),Q(3)];d=2
        V=[]
        for S in combinations(range(5),2):
            c=roots.candidate(a,d,S)
            if c['status']=='VERTEX':V.append(tuple(map(Q,c['point'])))
        best=max((make(a,d,u,v) for u in V for v in V if u!=v),key=lambda c:c['mass'])
        out=verify(best);spacing.append(dict(epsilon=str(e),**out));saved.append(best)
    large=[]
    for d in [8,16]:
        a=list(map(Q,range(2*d+1)))
        u=tuple(map(Q,roots.candidate(a,d,tuple(range(d)))['point']))
        v=tuple(map(Q,roots.candidate(a,d,tuple([0,*range(2,d),2*d]))['point']))
        c=make(a,d,u,v);out=verify(c);large.append(dict(dimension=d,**out));saved.append(c)
    old=(piv.make,piv.inverse,roots.candidate,roots.square_solve)
    def stop(*a,**k):raise AssertionError('producer called during saved replay')
    try:
        piv.make=piv.inverse=roots.candidate=roots.square_solve=stop
        replay=[verify(c) for c in saved]
    finally:piv.make,piv.inverse,roots.candidate,roots.square_solve=old
    forged=[];base=next(c for c in saved if c['dimension']==3)
    for name,mut in [('mass',lambda c:c.update(mass=Q(0))),
          ('coefficient',lambda c:c['weights'].__setitem__(0,Q(-1))),
          ('gap',lambda c:c.update(gap=c['gap']+1)),
          ('target',lambda c:c['v'].__setitem__(0,c['v'][0]+1)),
          ('no edges',lambda c:c.update(edges=[])),
          ('index',lambda c:c.update(selected=-1))]:
        c=deepcopy(base);mut(c)
        try:verify(c)
        except (ValueError,AssertionError,IndexError,ZeroDivisionError):forged.append(name)
        else:raise AssertionError('accepted forgery '+name)
    return dict(status='PASS',counts=stats,models=reports,large=large,
        adversarial_spacing=spacing,largest_small_mass=str(largest['mass']),
        replay_records=len(replay),replay_edges=sum(r['edges'] for r in replay),
        producers_disabled=True,rejected=forged,
        scope='Exact finite checks of actual original-edge witnesses, not Lean verification or a polynomial mass bound.'),saved


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r,s=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    piv.dump(a.out/'report.json',r);piv.dump(a.out/'fixtures.json',s)
    print(json.dumps(r,sort_keys=True))
if __name__=='__main__':main()
