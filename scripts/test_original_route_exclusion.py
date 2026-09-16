#!/usr/bin/env python3
"""Independent reference graphs, certificate mutations, and capping controls."""
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,permutations,product
from pathlib import Path
import argparse,hashlib,json,random
import sympy as sp
import original_route_exclusion as R


def kw(cap=None):
    A=[[6,3,0,-1],[3,6,-1,0],[35,45,-6,-3],[45,35,-3,-6],[-1,0,0,0],[0,-1,0,0],[0,0,-1,0],[0,0,0,-1]]
    b=[1,1,8,8,0,0,0,0]
    if cap is not None:A.append([1,1,1,1]);b.append(cap)
    return {'A':A,'b':b,'start':[0]*4,'target':[1,1,8,8]}


def cube(d):
    return [[s*int(i==j) for j in range(d)] for i in range(d) for s in (-1,1)],[0,1]*d


def birkhoff(n):
    d=(n-1)**2;A=[[-int(i==j) for j in range(d)] for i in range(d)];b=[0]*d
    for i in range(n-1):A.append([int(j//(n-1)==i) for j in range(d)]);b.append(1)
    for i in range(n-1):A.append([int(j%(n-1)==i) for j in range(d)]);b.append(1)
    A.append([-1]*d);b.append(2-n)
    V=[tuple(Q(p[i]==j) for i in range(n-1) for j in range(n-1)) for p in permutations(range(n))]
    return A,b,V


def reference(A,b,known=None):
    A=sp.Matrix(A);b=sp.Matrix(b);m,d=A.shape;V={};systems=0
    cand=[] if known is None else known
    if known is None:
        for J in combinations(range(m),d):
            systems+=1;M=A[list(J),:]
            if M.det():cand.append(tuple(Q(str(t)) for t in M.inv()*b[list(J),:]))
    for x in cand:
        z=A*sp.Matrix(x)
        if all(z[i]<=b[i] for i in range(m)):V[x]=tuple(i for i in range(m) if z[i]==b[i])
    G={x:set() for x in V}
    for x,y in combinations(V,2):
        I=sorted(set(V[x])&set(V[y]));rank=A[I,:].rank() if I else 0
        if rank==d-1:G[x].add(y);G[y].add(x)
    D={}
    for x in V:
        D[x]={x:0};todo=deque([x])
        while todo:
            y=todo.popleft()
            for z in G[y]:
                if z not in D[x]:D[x][z]=D[x][y]+1;todo.append(z)
        assert len(D[x])==len(V)
    return V,G,D,systems


def run(fixtures):
    cases=[('cube2',*cube(2),None),('cube3',*cube(3),None),
      ('pyramid',[[1,0,1],[-1,0,1],[0,1,1],[0,-1,1],[0,0,-1]],[1,1,1,1,0],None),
      ('octahedron',[list(v) for v in product((-1,1),repeat=3)],[1]*8,None),
      ('embedded_square',[[1,0,0],[-1,0,0],[0,1,0],[0,-1,0],[0,0,1],[0,0,-1]],[1,0,1,0,0,0],None),
      ('duplicate_zero_rows',[[1,0],[-1,0],[0,1],[0,-1],[2,0],[0,0]],[1,0,1,0,2,0],None),
      ('birkhoff3',*birkhoff(3)),('birkhoff4',*birkhoff(4))]
    out={'models':[]};saved=[];stats=dict(positive=0,excluded=0,star_neighbor_checks=0,negative_controls=0,producer_disabled=0)
    rng=random.Random(271)
    def save(name,data,L,B=None):
        r=R.solve(data,L,B);assert r['status']!='UNKNOWN'
        stats['excluded' if r['status']=='EXCLUDED' else 'positive']+=1
        f={'name':name,'input':R.serial(data),'result':r};saved.append(f);return f
    for name,A,b,known in cases:
        V,G,D,systems=reference(A,b,known);pairs=list(combinations(V,2));rng.shuffle(pairs);far=max(pairs,key=lambda p:D[p[0]][p[1]]);pairs=[far]+[p for p in pairs if p!=far][:3];count=0
        for u,v in pairs:
            data=R.serial({'A':A,'b':b,'start':u,'target':v});L=D[u][v]
            for bound in (L-1,L):
                f=save(name,data,bound);r=f['result'];assert r['status']==('EXCLUDED' if bound<L else 'FOUND')
                if bound<L:
                    c=r['certificate'];vv=[tuple(map(Q,p['point'])) for p in c['vertices']]
                    for s in c['stars']:
                        assert {vv[e['target']] for e in s['rays'] if e['kind']=='edge'}==G[vv[s['vertex']]];count+=1
        stats['star_neighbor_checks']+=count
        out['models'].append({'name':name,'dimension':len(A[0]),'rows':len(A),'vertices':len(V),
          'reference_edges':sum(map(len,G.values()))//2,'complete_square_systems':systems,
          'reference_vertex_source':'classical permutations' if known else 'all active bases','pairs':len(pairs),'matched_stars':count})
        print('checked',name,count,flush=True)
    family=[]
    for cap in (None,Q(18001,1000),19,100,10**6):
        row={'cap':None if cap is None else str(cap),'queries':[]}
        for L,B in ((4,None),(5,None),(None,0)):
            f=save('kw_'+str(cap)+'_'+str(L)+'_'+str(B),kw(cap),L,B);r=f['result']
            assert r['status']==('EXCLUDED' if L==4 or cap is None and B==0 else 'FOUND')
            row['queries'].append({'length':L,'reentries':B,'status':r['status'],'verified':r['verified']})
        family.append(row)
    out['cap_family']=family
    for cap in (None,19):
        data=kw(cap);V,G,D,n=reference(data['A'],data['b']);assert D[tuple(map(Q,data['start']))][tuple(map(Q,data['target']))]==5
        out.setdefault('kw_reference',[]).append({'cap':cap,'vertices':len(V),'edges':sum(map(len,G.values()))//2,
          'active_systems':n,'max_sum_finite_vertices':str(max(sum(x) for x in V)),'distance':5})
    A,b,_=birkhoff(4);u=[int(i==j) for i in range(3) for j in range(3)];perm=(1,0,3,2)
    v=[int(perm[i]==j) for i in range(3) for j in range(3)]
    nn=save('rank_trap',{'A':A,'b':b,'start':u,'target':v},1);assert nn['result']['status']=='EXCLUDED'
    out['rank_trap']=nn['result']['verified']
    save('embedded_segment',{'A':[[1,0],[-1,0],[0,1],[0,-1]],'b':[1,0,0,0],'start':[0,0],'target':[1,0]},0)
    save('isolated_point',{'A':[[1],[-1]],'b':[0,0],'start':[0],'target':[0]},0)
    controls=[];neg=next(f for f in saved if f['name']=='kw_None_4_None');nr=next(f for f in saved if f['name']=='kw_None_None_0')
    def rejects(label,f,mut):
        c=deepcopy(f['result']['certificate']);mut(c)
        try:R.verify_exclusion(f['input'],c)
        except (ValueError,IndexError,KeyError,TypeError,ZeroDivisionError):controls.append(label);return
        raise AssertionError('forgery accepted '+label)
    rejects('binding',neg,lambda c:c.update(input_sha256='bad'))
    rejects('missing star',neg,lambda c:c['stars'].pop())
    rejects('missing active subset',neg,lambda c:c['stars'][0]['entries'].pop())
    rejects('source depth',neg,lambda c:c['states'][0].update(depth=1))
    rejects('missing successor',neg,lambda c:c['states'].pop())
    rejects('slice inverse',neg,lambda c:c['stars'][0]['entries'][0]['inverse'][0].__setitem__(0,'12345'))
    rejects('normalized ray',neg,lambda c:c['stars'][0]['rays'][0]['direction'].__setitem__(0,'12345'))
    rejects('maximal step',neg,lambda c:next(e for s in c['stars'] for e in s['rays'] if e['kind']=='edge').update(step='12345'))
    rejects('fake recession',neg,lambda c:next(e for s in c['stars'] for e in s['rays'] if e['kind']=='edge').update(kind='unbounded_ray'))
    rejects('target',neg,lambda c:c['target']['point'].__setitem__(0,'999'))
    rejects('active list',neg,lambda c:c['vertices'][0]['active'].pop())
    rejects('vertex inverse',neg,lambda c:c['vertices'][0]['inverse'][0].__setitem__(0,'12345'))
    def kernel(c):next(e for s in c['stars'] for e in s['entries'] if e['kind']=='singular')['kernel']=['0']*9
    rejects('zero kernel',nn,kernel)
    def blocker(c):next(e for s in c['stars'] for e in s['entries'] if e['kind']=='blocked')['violated']=999
    rejects('false violated row',nn,blocker)
    rejects('negative debt',nr,lambda c:c['states'][-1].update(used=-1))
    rejects('erase memory',nr,lambda c:c['states'][-1].update(left=[]))
    rejects('relax restriction without coverage',nr,lambda c:c.update(max_row_reentries=1))
    out['controls']=controls;stats['negative_controls']=len(controls);out['caps']=[]
    for params in ({'state_cap':1},{'star_cap':0},{'vertex_cap':1}):
        r=R.solve(kw(),4,**params);assert r['status']=='UNKNOWN' and 'certificate' not in r;out['caps'].append(r)
    # Affine coordinates and positive rescaling do not alter the geometric results.
    M=sp.Matrix([[1,1,0,0],[0,1,1,0],[0,0,1,1],[0,0,0,1]]);h=sp.Matrix([2,-3,5,1]);data=kw();A=sp.Matrix(data['A']);b=sp.Matrix(data['b']);D=sp.diag(1,2,3,5,7,11,13,17)
    changed={'A':[[str(z) for z in r] for r in (D*A*M).tolist()],'b':[str(z) for z in D*(b-A*h)],
      'start':[str(z) for z in M.inv()*(sp.Matrix(data['start'])-h)],'target':[str(z) for z in M.inv()*(sp.Matrix(data['target'])-h)]}
    out['affine_rescaling']=[]
    for L,B in ((4,None),(None,0),(5,None)):
        f=save('affine_scaled',changed,L,B);assert f['result']['status']==('FOUND' if L==5 else 'EXCLUDED');out['affine_rescaling'].append(f['result']['verified'])
    old={n:getattr(R,n) for n in ('solve','inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses')};star=R.Producer.star
    def kill(*a,**k):raise AssertionError('producer invoked by checker')
    try:
        for n in old:setattr(R,n,kill)
        R.Producer.star=kill
        for f in saved:
            c=f['result']['certificate'];fun=R.verify_exclusion if f['result']['status']=='EXCLUDED' else R.verify_path
            assert fun(f['input'],c)==f['result']['verified'];stats['producer_disabled']+=1
    finally:
        for n,v in old.items():setattr(R,n,v)
        R.Producer.star=star
    f=fixtures/'exclusions_and_paths.json';f.write_text(json.dumps(saved,sort_keys=True,indent=2)+'\n')
    out.update(status='PASS',stats=stats,fixture_sha256=hashlib.sha256(f.read_bytes()).hexdigest(),
      scope='Independent rational proof certificates; no Lean/Prove2Me or universal diameter bound. Exponential certificate size is possible.')
    return out


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args();a.fixtures.mkdir(parents=True,exist_ok=True)
    r=run(a.fixtures);r['source_sha256']={f:hashlib.sha256((Path(__file__).parent/f).read_bytes()).hexdigest() for f in ('original_route_exclusion.py','test_original_route_exclusion.py')}
    a.out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['stats'])
if __name__=='__main__':main()
