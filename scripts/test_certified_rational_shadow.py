#!/usr/bin/env python3
"""Independent exact tests, not Lean verification. No reference graph is an input."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
from collections import deque
import argparse, hashlib, json, random, time
import certified_rational_shadow as s
ROOT=Path(__file__).resolve().parents[1]

def dump(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(s.serial(obj),sort_keys=True,indent=2)+'\n')

def hashes():
    return {f'scripts/{n}':hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest()
            for n in ['certified_rational_shadow.py','test_certified_rational_shadow.py','exact_farkas_lp.py']}

def models():
    A=[[-int(i==j) for j in range(3)]for i in range(3)]+[[int(i==j)for j in range(3)]for i in range(3)]
    b=[0]*3+[1]*3
    return {
      'sheared_hexagon':([[0,1],[0,-1],[1,3],[-1,-1],[1,1],[-1,-3]],[1,1,2,2,2,2]),
      'pentagon':([[-1,0],[0,-1],[1,0],[0,1],[1,1]],[0,0,2,2,3]),
      'cube3':(A,b),
      'octahedron3':([list(q)for q in product((-1,1),repeat=3)],[1]*8),
      'crosspolytope4':([list(q)for q in product((-1,1),repeat=4)],[1]*16),
      'square_pyramid':([[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],[0,1,1,1,1]),
      'cube4_pyramid':([[0]*4+[-1]]+[[sign*int(i==j)for j in range(4)]+[1]
                         for i in range(4)for sign in(-1,1)],[0]+[1]*8),
      'embedded_square':([[-1,0,0],[1,0,0],[0,-1,0],[0,1,0],[0,0,1],[0,0,-1]],[0,1,0,1,0,0]),
      'redundant_cube':(A+[A[0],[1,1,0],[0,0,0]],b+[b[0],2,1]),
      'line1':([[-1],[1]],[0,2]),
      'single_point':([[1,0],[-1,0],[0,1],[0,-1]],[0,0,0,0])}

def reference(Araw,braw):
    from sympy import Matrix,Rational
    A,b=s.lp.parse(Araw,braw);d=len(A[0]);V={};tried=0
    for I in combinations(range(len(A)),d):
        M=Matrix([[Rational(z)for z in A[i]]for i in I]);tried+=1
        if M.det()==0:continue
        x=tuple(Q(z)for z in M.inv()*Matrix([Rational(b[i])for i in I]))
        if all(s.dot(a,x)<=t for a,t in zip(A,b)):V[x]=frozenset(s.active(A,b,x))
    s.require(V,'empty reference polytope');G={x:set()for x in V}
    for x,y in combinations(V,2):
        I=sorted(V[x]&V[y]);rank=Matrix([list(A[i])for i in I]).rank()if I else 0
        if rank==d-1:G[x].add(y);G[y].add(x)
    return A,b,V,G,tried

def distances(G,start):
    D={start:0};q=deque([start])
    while q:
        x=q.popleft()
        for y in G[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    s.require(len(D)==len(G),'reference graph disconnected');return D

def canonical(v):
    q=next(z for z in v if z);return tuple(z/q for z in v)

def geometry_check(data,out,V,G):
    A,b,u,v=s.parse(data);r=out['verified'];path=[tuple(map(Q,x))for x in r['path']]
    s.require(path[0]==u and path[-1]==v,'reference endpoints')
    s.require(all(y in G[x]for x,y in zip(path,path[1:])),'reference rejects original edge')
    pu,pv=out['certificate']['endpoint_bases'];f,h,_=s.generic_objectives(A,b,pu,pv)
    walls=list(map(Q,r['crossing_times']));locked=V[u]&V[v];face=[x for x in V if locked<=V[x]];tests=0
    for i,t in enumerate(walls):
        c=[(1-t)*p+t*q for p,q in zip(f,h)];best=max(s.dot(c,x)for x in face)
        s.require({x for x in face if s.dot(c,x)==best}=={path[i],path[i+1]},'whole exposed face is not exactly edge')
        tests+=len(face)
    for i,(l,r)in enumerate(zip([Q(0)]+walls,walls+[Q(1)])):
        t=(l+r)/2;c=[(1-t)*p+t*q for p,q in zip(f,h)];best=max(s.dot(c,x)for x in face)
        s.require({x for x in face if s.dot(c,x)==best}=={path[i]},'missing envelope interval winner');tests+=len(face)
    ds=sorted({canonical(tuple(b-a for a,b in zip(x,y)))for x in G for y in G[x]})
    for g in ds:s.require(s.dot(f,g)and s.dot(h,g),'genericity missed an actual edge')
    for g,k in combinations(ds,2):s.require(s.dot(f,g)*s.dot(h,k)-s.dot(f,k)*s.dot(h,g)!=0,'independent simultaneous tie')
    return tests,len(ds)*(len(ds)-1)//2

def small_stage(only=None):
    keys=['models','reference_vertices','reference_edges','square_systems','routes','route_edges','bfs_edges',
          'nonshortest','primary_queries','tie_queries','support_comparisons','genericity_determinants','extra_tight_vertex_occurrences']
    total=dict.fromkeys(keys,0);rng=random.Random(268);records=[];fixtures=[]
    for name,(A,b)in models().items():
        if only and name!=only:continue
        begin=time.monotonic();A,b,V,G,tried=reference(A,b);pts=sorted(V)
        pairs=[(x,y)for i,x in enumerate(pts)for y in pts[i:]]
        if len(pairs)>55:rng.shuffle(pairs);pairs=pairs[:55]
        D={x:distances(G,x)for x in pts};rows=[]
        for u,v in pairs:
            data={'A':A,'b':b,'start':u,'target':v};out=s.construct(data);checks,dets=geometry_check(data,out,V,G)
            r=out['verified'];L=r['original_edges'];s.require(L>=D[u][v],'beats shortest path')
            total['routes']+=1;total['route_edges']+=L;total['bfs_edges']+=D[u][v];total['nonshortest']+=L>D[u][v]
            total['primary_queries']+=r['primary_support_queries'];total['tie_queries']+=r['tie_resolution_queries']
            total['support_comparisons']+=checks;total['genericity_determinants']+=dets
            total['extra_tight_vertex_occurrences']+=r['vertices_with_more_than_d_tight_rows']
            rows.append({'start':u,'target':v,'edges':L,'shortest':D[u][v],'primary_queries':r['primary_support_queries'],
                         'tie_queries':r['tie_resolution_queries'],'objective_bits':r['endpoint_objective_max_bits']})
            if len(fixtures)<8 and name in('octahedron3','embedded_square','redundant_cube','cube4_pyramid')and u!=v:
                fixtures.append({'name':name,'input':data,**out,'shortest':D[u][v]})
        total['models']+=1;total['reference_vertices']+=len(V);total['reference_edges']+=sum(map(len,G.values()))//2;total['square_systems']+=tried
        records.append({'name':name,'vertices':len(V),'edges':sum(map(len,G.values()))//2,'pairs':rows,'seconds':round(time.monotonic()-begin,3)})
        print(name,len(V),len(pairs),sum(x['edges']for x in rows),flush=True)
    dump(ROOT/'fixtures/certified_shadow_small.json',fixtures)
    return {'totals':total,'models':records}

def auxiliary_stage():
    from sympy import Matrix
    sums=minors=coefftests=0
    for name in['pentagon','cube3','square_pyramid']:
        A,b,V,G,_=reference(*models()[name]);pts=sorted(V)
        for u,v in[(pts[0],pts[-1]),(pts[1],pts[-2])]:
            pu,pv=s.vertex_packet(A,b,u),s.vertex_packet(A,b,v);f,h,meta=s.generic_objectives(A,b,pu,pv)
            AA,bb=s.integer_rows(A,b);d=len(u);ds=set()
            for I in combinations(range(len(A)),d-1):
                M=Matrix([AA[i]for i in I]);g=tuple(Q((-1)**j*M[:,[k for k in range(d)if k!=j]].det())for j in range(d))
                if not any(g):continue
                s.require(max(abs(q)for q in g)<=meta['cofactor_bound'],'cofactor bound');minors+=1;ds.add(canonical(g))
                s.require(s.dot(f,g)and s.dot(h,g),'minor direction vanished')
            for g,k in combinations(ds,2):
                s.require(s.dot(f,g)*s.dot(h,k)-s.dot(f,k)*s.dot(h,g)!=0,'cofactor determinant vanished');sums+=1
    for C in range(1,5):
        R=2*C+2
        for coeff in product(range(-C,C+1),repeat=4):
            if any(coeff):s.require(sum(c*R**i for i,c in enumerate(coeff))!=0,'integer cancellation');coefftests+=1
    A,b=s.lp.parse([[1,-1],[-1,-1],[0,1]],[0,0,1]);p=s.lp.ExactLP(A,b,[0,0]).maximize([0,1]);point=tuple(map(Q,p['point']))
    s.require(point==(Q(0),Q(1)),'nonvertex control changed')
    y,o,piv=s.tie_vertex(A,b,(Q(0),Q(1)),p,(Q(1),Q(0)),20000)
    s.require(y==(Q(1),Q(1)),'tie resolver failed');s.vertex_packet(A,b,y)
    A,b=s.lp.parse(*models()['cube3']);u=(Q(0),)*3;v=(Q(1),)*3;data={'A':A,'b':b,'start':u,'target':v}
    out=s.construct(data);c=out['certificate'];names=[]
    def reject(name,call):
        try:call()
        except(ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('forgery accepted '+name)
    def mutation(name,change):
        bad=deepcopy(c);change(bad);reject(name,lambda:s.verify(data,bad))
    mutation('hash',lambda z:z.update(problem_sha256='bad'))
    mutation('generic_base',lambda z:z['genericity'].update(base=1))
    mutation('missing_bound',lambda z:z['boundedness'].pop())
    mutation('nonpositive_dual',lambda z:z['boundedness'][0]['optimum'].update(dual=[[0,-1]]))
    mutation('omitted_query',lambda z:z['queries'].pop())
    mutation('wrong_time',lambda z:z['queries'][0].update(time='0'))
    mutation('wrong_order',lambda z:z['queries'].reverse())
    mutation('nonmaximal_support',lambda z:z['queries'][0]['primary'].update(value='999'))
    mutation('wrong_midpoint',lambda z:next(q for q in z['queries']if q['kind']=='split').update(middle=['1/2']*3))
    mutation('false_rank',lambda z:z['vertices'][0]['right_inverse'][0].__setitem__(0,'9'))
    def break_edge_inverse(z):
        e=next(q for q in z['queries']if q['kind']=='edge')['edge']
        k=next(k for k,x in enumerate(A[e['rows'][0]])if x)
        e['right_inverse'][k][0]=str(Q(e['right_inverse'][k][0])+1)
    mutation('false_edge_rank',break_edge_inverse)
    mutation('missing_vertex',lambda z:z['vertices'].pop())
    mutation('changed_lock',lambda z:z.update(locked_rows=[0]))
    reject('diagonal_rank',lambda:s.edge_packet(A,b,u,v))
    reject('query_cap',lambda:s.construct(data,query_cap=1))
    bad=deepcopy(data);bad['start']=['1/2']*3;reject('nonvertex_source',lambda:s.construct(bad))
    bad=deepcopy(data);bad['A']=[[float(x)for x in row]for row in A];reject('float_data',lambda:s.construct(bad))
    reject('unbounded_input',lambda:s.construct({'A':[[-1,0],[0,-1]],'b':[0,0],'start':[0,0],'target':[0,0]}))
    saved=[]
    def forbidden(*a,**kw):raise AssertionError('verification invoked production')
    for obj,name in[(s.lp,'ExactLP'),(s,'inverse'),(s,'independent_rows'),(s,'rank_packet')]:
        saved.append((obj,name,getattr(obj,name)));setattr(obj,name,forbidden)
    try:s.require(s.verify(data,c)==out['verified'],'search-disabled replay changed')
    finally:
        for obj,name,fn in saved:setattr(obj,name,fn)
    return {'cofactor_vectors':minors,'cofactor_direction_pair_determinants':sums,'integer_polynomial_checks':coefftests,
            'lifted_LP_nonvertex_control':{'primary_point':point,'true_vertex_after_secondary':y,'secondary_pivots':piv},
            'rejected':len(names),'rejections':names,'LP_inverse_rank_search_disabled_audit':True}

def large_stage():
    results=[]
    for d in[6,8,10,12]:
        A=[[-int(i==j)for j in range(d)]for i in range(d)]+[[int(i==j)for j in range(d)]for i in range(d)]
        b=[0]*d+[1]*d;data={'A':A,'b':b,'start':[0]*d,'target':[1]*d};start=time.monotonic();out=s.construct(data);r=out['verified']
        s.require(r['original_edges']==d,'box coordinate-crossing count')
        record={k:v for k,v in r.items()if k not in('path','crossing_times')}
        record.update(known_vertices=2**d,independent_hamming_lower_bound=d,discovery=out['discovery'],seconds=round(time.monotonic()-start,3))
        results.append(record);print('box',d,r['original_edges'],r['endpoint_objective_max_bits'],record['seconds'],flush=True)
        if d in(6,12):dump(ROOT/f'fixtures/certified_shadow_box{d}.json',{'input':data,**out})
    return results

def main():
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(250000)
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','auxiliary','large','assemble']);a=p.parse_args()
    (ROOT/'research').mkdir(exist_ok=True)
    for stage in['small','auxiliary','large']if a.stage is None else[a.stage]:
        if stage=='assemble':continue
        r=globals()[stage+'_stage']();dump(ROOT/f'research/SHADOW_STAGE_{stage}.json',{'source_sha256':hashes(),'result':r})
    if a.stage in(None,'assemble'):
        stages={k:json.loads((ROOT/f'research/SHADOW_STAGE_{k}.json').read_text())for k in['small','auxiliary','large']}
        s.require(all(v['source_sha256']==hashes()for v in stages.values()),'stale source receipts')
        out={'status':'PASS','source_sha256':hashes(),'stages':stages,'scope':'Independent exact graph/arithmetic tests; not Lean or Prove2Me verification.'}
        dump(ROOT/'research/CERTIFIED_SHADOW_CHECK.json',out);print('ASSEMBLED',stages['small']['result']['totals'],flush=True)
if __name__=='__main__':main()
