#!/usr/bin/env python3
"""Independent H/V checks, thin-cone/large-direction fixtures, and rejection
controls for implicit-base Minkowski route lifting. No random shadow sampler.
Large cases use explicit cubical base routes, not full vertex enumeration.
"""
from __future__ import annotations
import argparse, hashlib, json, random, time
from collections import deque
from copy import deepcopy
from itertools import combinations, product
from pathlib import Path
from implicit_minkowski_lift import *
ROOT=Path(__file__).resolve().parents[1]


def inverse(A):
    n=len(A);a=[list(map(rat,row))+[Q(i==j) for j in range(n)] for i,row in enumerate(A)]
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return [row[n:] for row in a]


def vertices(A,b):
    A=[tuple(map(rat,a)) for a in A];b=list(map(rat,b));d=len(A[0]);V=set()
    for ids in combinations(range(len(A)),d):
        inv=inverse([A[i] for i in ids])
        if inv is None:continue
        x=tuple(dot(row,[b[i] for i in ids]) for row in inv)
        if all(dot(a,x)<=z for a,z in zip(A,b)):V.add(x)
    return sorted(V)


def kernel_line(rows,d):
    a=[list(map(rat,row)) for row in rows];piv=[];k=0
    for j in range(d):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(len(a)):
            if i!=k:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
    if k!=d-1:return None
    free=next(i for i in range(d) if i not in piv);v=[Q(0)]*d;v[free]=1
    for row,j in zip(a,piv):v[j]=-row[free]
    return tuple(v)


def hull(points,d):
    """Independent complete small V-to-H conversion by supporting planes."""
    V=sorted(set(points));H=set()
    for ids in combinations(range(len(V)),d):
        x=V[ids[0]];a=kernel_line([sub(V[j],x) for j in ids[1:]],d)
        if a is None:continue
        b=dot(a,x);values=[dot(a,v)-b for v in V]
        if all(z<=0 for z in values) and any(z<0 for z in values):pass
        elif all(z>=0 for z in values) and any(z>0 for z in values):a=scale(-1,a);b=-b
        else:continue
        normal=line(a+(b,))
        if dot(a,normal[:d])<0:normal=tuple(-z for z in normal)
        H.add(normal)
    H=sorted(H);A=[tuple(map(Q,h[:d])) for h in H];b=[Q(h[-1]) for h in H]
    verts=[v for v in V if rank(tuple(a for a,z in zip(A,b) if dot(a,v)==z))==d]
    require(verts,'full-dimensional independent hull expected')
    return A,b,verts


def graph(A,b,V):
    d=len(A[0]);active=[{i for i,(a,z) in enumerate(zip(A,b)) if dot(a,v)==z} for v in V]
    G=[set() for _ in V]
    for i,j in combinations(range(len(V)),2):
        if rank(tuple(tuple(A[k]) for k in sorted(active[i]&active[j])))==d-1:G[i].add(j);G[j].add(i)
    return G,active


def bfs(G,u):
    parent={u:None};todo=deque([u])
    while todo:
        x=todo.popleft()
        for y in sorted(G[x]):
            if y not in parent:parent[y]=x;todo.append(y)
    return parent


def path_from(parent,v):
    result=[]
    while v is not None:result.append(v);v=parent[v]
    return result[::-1]


def support_weights(A,b,x,c):
    """Test-only small positive-dual search; result is independently checked.
    Does not appear in the lift's complexity or correctness assumptions."""
    ids=[i for i,(a,z) in enumerate(zip(A,b)) if dot(a,x)==z];d=len(x)
    for B in combinations(ids,d):
        inv=inverse([A[i] for i in B])
        if inv is None:continue
        for power in range(64):
            t=Q(0) if power==0 else Q(1,2**power)
            adjusted=sub(c,tuple(t*sum(A[i][j] for i in ids) for j in range(d)))
            coeff=[sum(adjusted[k]*inv[k][j] for k in range(d)) for j in range(d)]
            if all(a>=0 for a in coeff):
                weights=[Q(0)]*len(A)
                for i in ids:weights[i]=t
                for i,w in zip(B,coeff):weights[i]+=w
                if rank(tuple(tuple(A[i]) for i,w in enumerate(weights) if w))==d:return weights
    raise AssertionError('could not recover positive exposing multipliers in test fixture')


def all_sums(V,summands):
    out=set(V)
    for block in summands:out={add(x,tuple(map(rat,y))) for x in out for y in block}
    return out


def cube(d):
    return [[sign*int(i==j) for j in range(d)] for sign in(-1,1) for i in range(d)],[0]*d+[1]*d


def small_stage():
    square=cube(2);cube3=cube(3)
    models=[('triangle',([[-1,0],[0,-1],[1,1]],[0,0,1]),[[[0,0],[1,-2]]]),
      ('square_thin',square,[[[0,0],[1,'1/4096']]]),
      ('square_four_directions',square,[[[0,0],[1,1]],[[0,0],[1,'4097/4096']]]),
      ('pentagon',([[-1,0],[0,-1],[1,0],[0,1],[1,1]],[0,0,2,2,3]),[[[0,0],[1,-1],[2,1]]]),
      ('tetrahedron',([[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],[0,0,0,1]),[[[0,0,0],[1,-1,2]]]),
      ('cube3',cube3,[[[0,0,0],[1,2,-1]]]),
      ('nonsimple_pyramid',([[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],[0,1,1,1,1]),[[[0,0,0],[1,0,0]]]),
      ('parallel_redundancy',(square[0]+[[-2,0],[0,0]],square[1]+[0,1]),
        [[[0,0],[1,0],[1,0]],[[0,0],[-2,0]],[[0,0],[1,1],[2,2]],[[3,4]]])]
    counts={'models':0,'base_vertices':0,'base_edges':0,'refined_vertices':0,'refined_edges':0,
      'ordered_refined_distances':0,'routes':0,'ordinary_edges':0,'stationary_base_routes':0,
      'nonshortest_lifts':0,'parallel_expansions':0,'source_dual_checks':0}
    records=[];saved=False
    for name,(aa,bb),summands in models:
        A=[tuple(map(rat,a)) for a in aa];b=list(map(rat,bb));d=len(A[0])
        V=vertices(A,b);G,acts=graph(A,b,V);AA,bb,W=hull(all_sums(V,summands),d);GG,wacts=graph(AA,bb,W)
        exposers=[tuple(sum(AA[j][k] for j in wacts[i]) for k in range(d)) for i in range(len(W))]
        parents=[bfs(G,i) for i in range(len(V))];wp=[bfs(GG,i) for i in range(len(W))]
        base_ids=[];weights=[]
        for c in exposers:
            values=[dot(c,x) for x in V];maximum=max(values);hits=[i for i,x in enumerate(values) if x==maximum]
            require(len(hits)==1,'refined vertex lacks unique base decomposition');i=hits[0]
            base_ids.append(i);weights.append(support_weights(A,b,V[i],c));counts['source_dual_checks']+=1
        rec={'name':name,'dimension':d,'base_vertices':len(V),'refined_vertices':len(W),'routes':0,'max_route':0}
        for i in range(len(W)):
            counts['ordered_refined_distances']+=len(wp[i])
            for j in range(i+1):
                u,v=base_ids[i],base_ids[j];basepath=[V[k] for k in path_from(parents[u],v)]
                data={'A':A,'b':b,'base_route':basepath,'summands':summands,
                      'source_weights':weights[i],'target_weights':weights[j]}
                out=build(data);got=out['verified'];route=[tuple(map(rat,x)) for x in out['certificate']['route']]
                require(route[0]==W[i] and route[-1]==W[j],'independent hull endpoint mismatch')
                require(all(x in W for x in route),'lift produced a nonvertex of independent hull')
                require(all(W.index(y) in GG[W.index(x)] for x,y in zip(route,route[1:])), 'lift is not ordinary edges of independent sum graph')
                exact=len(path_from(wp[i],j))-1
                require(got['ordinary_edges']>=exact,'lift beats independently computed graph distance')
                counts['routes']+=1;counts['ordinary_edges']+=got['ordinary_edges'];counts['stationary_base_routes']+=int(u==v)
                counts['nonshortest_lifts']+=int(got['ordinary_edges']>exact);counts['parallel_expansions']+=got['expanded_parallel_base_edges']
                rec['routes']+=1;rec['max_route']=max(rec['max_route'],got['ordinary_edges'])
                if not saved and got['ordinary_edges']>exact:
                    (ROOT/'fixtures/lift_not_shortest.json').write_text(json.dumps(serial({'input':data,**out,'independent_distance':exact}),indent=2)+'\n');saved=True
        counts['models']+=1;counts['base_vertices']+=len(V);counts['base_edges']+=sum(map(len,G))//2
        counts['refined_vertices']+=len(W);counts['refined_edges']+=sum(map(len,GG))//2;records.append(rec)
        print(name,rec,flush=True)
    require(counts['nonshortest_lifts']>0,'missing deliberate nonshortest-lift control')
    return {'counts':counts,'examples':records}


def star_box(d):
    """A (d-2)-dimensional variable-width star box times a square."""
    require(d>=4,'star-square fixture needs dimension at least four')
    p=d-2;A=[[-int(i==j) for j in range(d)] for i in range(d)]
    for i in range(d):
        row=[int(i==j) for j in range(d)]
        if 0<i<p:row[0]=-1
        A.append(row)
    return [tuple(map(Q,a)) for a in A],[Q(0)]*d+[Q(1)]*d


def star_vertex(bits,p):
    return tuple(Q(bits[0]) if i==0 else Q(bits[i]*(1+bits[0])) if i<p else Q(bits[i]) for i in range(len(bits)))


def star_objective_weights(c):
    d=len(c);p=d-2;w=[Q(0)]*(2*d)
    for i in range(1,d):w[(d if c[i]>0 else 0)+i]=abs(c[i])
    central=c[0]+sum(x for x in c[1:p] if x>0)
    require(central and all(c[i] for i in range(1,d)),'nongeneric star objective')
    w[d if central>0 else 0]=abs(central)
    bits=[int(central>0)]+[int(c[i]>0) for i in range(1,d)]
    return w,bits


def large_input(d,q,epsilon_power,seed):
    A,b=star_box(d);p=d-2;eps=Q(1,2**epsilon_power);rng=random.Random(seed)
    cs=tuple(Q(-i-1) for i in range(d));ct=tuple(Q(i+2) for i in range(d))
    ws,sbits=star_objective_weights(cs);wt,tbits=star_objective_weights(ct)
    bits=sbits[:];path=[star_vertex(bits,p)]
    for i in range(d):
        if bits[i]!=tbits[i]:bits[i]=tbits[i];path.append(star_vertex(bits,p))
    z=(Q(0),)*d;g=(Q(0),)*p+(Q(1),Q(1));h=(Q(0),)*p+(Q(1),1+eps)
    summands=[[z,g],[z,h]]
    while len(summands)<q:
        v=tuple(Q(rng.randrange(-9,10),len(summands)+1) for _ in range(d))
        if all(v) and sum(v[:p]) and v[-2]+2*v[-1] and dot(cs,v) and dot(ct,v):summands.append([z,v])
    return {'A':A,'b':b,'base_route':path,'summands':summands,'source_weights':ws,'target_weights':wt},eps


def exposed_obstructions(data,eps):
    """Exact face certificates: an octagon and a whole star survive all
    additional dense summands. These imply small cones AND many directions.
    """
    P=Model(data);d=P.d;p=d-2
    # c_plane exposes base star at zero, leaves its square free; added dense
    # summands are points while both nearly parallel planar segments survive.
    c_plane=(Q(-1),)*p+(Q(0),Q(0))
    require(rank(tuple(P.A[i] for i in range(p)))==p,'plane face equality rank')
    for i in range(p):require(P.A[i]==tuple(-Q(i==j) for j in range(d)),'star coordinate support')
    maxima=P.maxima(c_plane)
    require(len(maxima[0])==2 and len(maxima[1])==2 and all(len(x)==1 for x in maxima[2:]),'plane face not retained')
    # c_star exposes a square vertex, leaves the whole star; every added
    # summand is a point. The entire exponential-direction star is a face.
    c_star=(Q(0),)*p+(Q(1),Q(2))
    require(all(len(x)==1 for x in P.maxima(c_star)),'star face not retained')
    require(rank(tuple(P.A[d+i] for i in (p,p+1)))==2,'star face equality rank')
    # Independently compute the small planar section as a 4-generator zonogon.
    planar=[(Q(0),Q(0))]
    for v in[(Q(1),Q(0)),(Q(0),Q(1)),(Q(1),Q(1)),(Q(1),1+eps)]:
        planar=list(set(planar+[add(x,v) for x in planar]))
    AA,bb,V=hull(planar,2);GG,_=graph(AA,bb,V)
    require(len(V)==8 and all(len(x)==2 for x in GG),'planar face is not the certified octagon')
    return {'exposed_octagon_vertices':8,'exposed_star_dimension':p,
        'proved_distinct_edge_direction_lower_bound':2**(p-1)+p-1,
        'affine_invariant_minimum_cone_width_upper_squared':str(eps),
        'all_endpoint_route_bound':(P.q+1)*d+P.q,
        'base_H_rows':P.m,'added_directions':P.q,
        'full_refined_graph_enumerated':False}


def large_stage():
    results=[]
    for d,q,power,seed in[(12,6,80,601),(24,12,120,602),(32,18,160,603)]:
        start=time.monotonic();data,eps=large_input(d,q,power,seed);out=build(data)
        obs=exposed_obstructions(data,eps);r={'name':f'thin_refinement_{d}d',**out['verified'],**obs,'epsilon_power':power,'seconds':round(time.monotonic()-start,3)}
        results.append(r);print(r,flush=True)
        (ROOT/f'fixtures/thin_refinement_{d}d.json').write_text(json.dumps(serial({'input':data,**out,'obstruction':obs}),indent=2)+'\n')
    return {'examples':results,'routes':len(results),'ordinary_edges':sum(x['ordinary_edges'] for x in results)}


def cross_ratio_stage():
    def det(a,b):return a[0]*b[1]-a[1]*b[0]
    rng=random.Random(604);tested=0
    for power in(8,40,120,240):
        eps=Q(1,2**power)
        for _ in range(30):
            while True:
                u=tuple(Q(rng.randrange(-9,10),rng.randrange(1,10)) for _ in range(2))
                v=tuple(Q(rng.randrange(-9,10),rng.randrange(1,10)) for _ in range(2))
                if det(u,v):break
            p=add(u,v);w=add(u,scale(1+eps,v))
            sine2=lambda a,b:det(a,b)**2/(dot(a,a)*dot(b,b))
            require(sine2(p,w)*sine2(u,v)==eps**2*sine2(u,p)*sine2(v,w),'cross ratio not affine invariant')
            require(min(sine2(a,b) for a,b in combinations((u,v,p,w),2))<=eps,'transformed direction separation exceeds bound')
            tested+=1
    counts=0
    for L,q in product(range(31),range(21)):
        require(L+(L+1)*q==(q+1)*L+q,'lift budget algebra')
        counts+=1
    return {'dense_affine_cross_ratio_checks':tested,'integer_lift_budget_checks':counts}


def negatives_stage():
    data,eps=large_input(4,3,20,605);out=build(data);c=out['certificate'];rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('accepted negative control '+name)
    for key,val in [('input_sha256','bad'),('budget',1),('added_direction_count',0),('base_edge_count',0),('kind','edge')]:
        x=deepcopy(c);x[key]=val;reject(key,lambda x=x:verify(data,x))
    x=deepcopy(c);x['route']=[x['route'][0],x['route'][-1]];reject('diagonal_as_edge',lambda:verify(data,x))
    x=deepcopy(c);x['events']=x['events'][1:];reject('missing_event',lambda:verify(data,x))
    x=deepcopy(c);x['events']=x['events'][::-1];reject('event_order',lambda:verify(data,x))
    x=deepcopy(c);x['objectives']=x['objectives'][:-1];reject('missing_corner',lambda:verify(data,x))
    x=deepcopy(c);x['objectives'][1]['weights']=[0]*len(data['A']);reject('zero_support_face_rank',lambda:verify(data,x))
    x=deepcopy(c);x['objectives'][0]['normal'][0]='99';reject('forged_normal',lambda:verify(data,x))
    x=deepcopy(c);x['objectives'][0]['weights'][0]='-1';reject('negative_multiplier',lambda:verify(data,x))
    x=deepcopy(data);x['summands'][0][1]=[1,0,0,0];reject('changed_refinement',lambda:verify(x,c))
    x=deepcopy(data);x['source_weights']=x['target_weights'];reject('changed_endpoint',lambda:build(x))
    x=deepcopy(data);x['A'][0]=[1.0,0,0,0];reject('float',lambda:build(x))
    x=deepcopy(data);x['base_route']=[x['base_route'][0],x['base_route'][-1]];reject('base_diagonal',lambda:build(x))
    x=deepcopy(data);x['base_route'][1]=[99]*4;reject('infeasible_base',lambda:build(x))
    x=deepcopy(data);x['base_route'][1]=[Q(1,2),0,0,0];reject('nonvertex_base',lambda:build(x))
    x=deepcopy(data);x['base_route'].insert(1,x['base_route'][0]);reject('repeated_base_vertex',lambda:build(x))
    x=deepcopy(data);x['summands'][0]=[];reject('empty_summand',lambda:build(x))
    # Positive boundary cases, including implicit equality in a line model.
    cases=[{'A':[[-1],[1]],'b':[0,1],'base_route':[[0],[1]],'summands':[[[0],[2]]], 'source_weights':[1,0],'target_weights':[0,1]},
      {'A':[[-1,0],[1,0],[0,1],[0,-1]],'b':[0,1,0,0],'base_route':[[0,0],[1,0]],'summands':[[[0,0],[1,1]]],
       'source_weights':[2,0,2,1],'target_weights':[0,2,1,2]},
      {'A':[[-1,0],[0,-1],[1,0],[0,1]],'b':[0,0,1,1],'base_route':[[0,0],[1,0],[1,1]],'summands':[],
       'source_weights':[1,1,0,0],'target_weights':[0,0,1,1]}]
    good=[build(p)['verified'] for p in cases]
    return {'rejected':len(rejected),'names':rejected,'boundary_positive':good}


def sources():
    paths=[ROOT/'scripts/implicit_minkowski_lift.py',ROOT/'scripts/test_implicit_minkowski_lift.py']+sorted((ROOT/'Solutions').glob('*.lean'))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--stage',choices=['small','large','aux','assemble']);args=parser.parse_args()
    stages=['small','large','aux'] if args.stage is None else [args.stage]
    for stage in stages:
        if stage=='assemble':continue
        begin=time.monotonic()
        result=small_stage() if stage=='small' else large_stage() if stage=='large' else {'cross_ratio':cross_ratio_stage(),'rejections':negatives_stage()}
        out={'stage':stage,'status':'PASS','seconds':round(time.monotonic()-begin,3),'source_sha256':sources(),'result':result}
        (ROOT/f'research/WALL_REFINEMENT_STAGE_{stage}.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
        print(stage,'PASS',out['seconds'],flush=True)
    if args.stage is None or args.stage=='assemble':
        loaded=[]
        for stage in ['small','large','aux']:
            out=json.loads((ROOT/f'research/WALL_REFINEMENT_STAGE_{stage}.json').read_text())
            require(out['status']=='PASS' and out['source_sha256']==sources(),'stale or failed stage')
            loaded.append(out)
        summary={'status':'PASS','scope':'Exact supplied-base-route refinement certificates, not Lean/platform acceptance.',
                 'source_sha256':sources(),'small':loaded[0]['result'],'large':loaded[1]['result'],'aux':loaded[2]['result'],
                 'stage_seconds':{o['stage']:o['seconds'] for o in loaded}}
        summary['route_certificates']=summary['small']['counts']['routes']+summary['large']['routes']+len(summary['aux']['rejections']['boundary_positive'])
        summary['ordinary_edge_occurrences']=summary['small']['counts']['ordinary_edges']+summary['large']['ordinary_edges']+sum(x['ordinary_edges'] for x in summary['aux']['rejections']['boundary_positive'])
        (ROOT/'research/WALL_REFINEMENT_CHECK_2026-09-13.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')
        print('ASSEMBLED',summary['route_certificates'],summary['ordinary_edge_occurrences'],flush=True)
if __name__=='__main__':main()
