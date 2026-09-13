#!/usr/bin/env python3
"""Exact small H/V cross-checks, large nonenumerating sweeps, and rejection tests."""
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import random
import time
from minkowski_wall_sweep import MinkowskiInput,add,sub,scale,dot,line,rat,serial,require,sweep,verify

ROOT=Path(__file__).resolve().parents[1]


def rank(rows):
    a=[list(r) for r in rows]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v:a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def kernel_line(rows,d):
    a=[list(r) for r in rows];piv=[];k=0
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
    free=next(j for j in range(d) if j not in piv);g=[Q(0)]*d;g[free]=Q(1)
    for row,j in zip(a,piv):g[j]=-row[free]
    return tuple(g)


def solve(rows,rhs):
    n=len(rows);a=[list(r)+[b] for r,b in zip(rows,rhs)]
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return tuple(r[-1] for r in a)


def hull(points,d):
    """Complete exact supporting-hyperplane enumeration for small point sets."""
    pts=sorted(set(points));facets=set()
    for ids in combinations(range(len(pts)),d):
        p=pts[ids[0]];g=kernel_line([sub(pts[i],p) for i in ids[1:]],d)
        if g is None:continue
        b=dot(g,p);sgn=[dot(g,x)-b for x in pts]
        if all(x<=0 for x in sgn) and any(x<0 for x in sgn):pass
        elif all(x>=0 for x in sgn) and any(x>0 for x in sgn):g=scale(-1,g);b=-b
        else:continue
        # Preserve orientation while normalizing the full supporting equation.
        row=g+(b,);c=line(row)
        if dot(g,tuple(c[:d]))<0:c=tuple(-x for x in c)
        facets.add(c)
    facets=sorted(facets)
    active={p:frozenset(i for i,f in enumerate(facets) if dot(f[:d],p)==f[-1]) for p in pts}
    vs=[p for p in pts if rank([facets[i][:d] for i in active[p]])==d]
    require(vs and facets,'lower-dimensional input in independent full-dimensional hull test')
    G={p:set() for p in vs}
    for u,v in combinations(vs,2):
        if rank([facets[i][:d] for i in active[u]&active[v]])==d-1:G[u].add(v);G[v].add(u)
    return facets,vs,active,G


def graph_dist(G,u):
    dist={u:0};todo=deque([u])
    while todo:
        x=todo.popleft()
        for y in G[x]:
            if y not in dist:dist[y]=dist[x]+1;todo.append(y)
    return dist


def all_sums(summands,d):
    pts={(Q(0),)*d}
    for block in summands:pts={add(a,tuple(map(rat,b))) for a in pts for b in block}
    return pts


def coordinate_simplex_sum(p,subsets,weights=None):
    d=p-1;weights=weights or [Q(1)]*len(subsets)
    e=[tuple(Q(i==j) for j in range(d)) for i in range(p)]
    return {'dimension':d,'summands':[[scale(w,e[i]) for i in S] for S,w in zip(subsets,weights)],
            'source_objective':list(range(1,p)), 'target_objective':list(range(-1,-p,-1))}


def spread_input(d,t=Q(2,3)):
    z=(Q(0),)*d
    return {'dimension':d,'summands':[[z,tuple(t*int(i==j) for j in range(d))] for i in range(d)]+[[z,(1-t,)*d]],
            'source_objective':[-i for i in range(1,d+1)],
            'target_objective':[i for i in range(1,d+1)]}


def spread_rows(d,t):
    A=[];b=[]
    for sign in (-1,1):
        for i in range(d):A.append(tuple(Q(sign*int(i==j)) for j in range(d)));b.append(Q(sign==1))
    for i in range(d):
        for j in range(d):
            if i!=j:A.append(tuple(Q(int(k==j)-int(k==i)) for k in range(d)));b.append(t)
    return A,b


def spread_check(d):
    data=spread_input(d);got=sweep(data);route=[tuple(map(rat,v)) for v in got['certificate']['route']]
    t=Q(2,3);A,b=spread_rows(d,t);evals=0
    active=[]
    for x in route:
        vals=[dot(a,x) for a in A];evals+=len(A)
        require(all(v<=c for v,c in zip(vals,b)),'spread H feasibility')
        act={i for i,(v,c) in enumerate(zip(vals,b)) if v==c};active.append(act)
        require(rank([A[i] for i in act])==d,'spread vertex rank')
    for i in range(len(route)-1):
        require(rank([A[j] for j in active[i]&active[i+1]])==d-1,'spread actual H-edge rank')
    require(len(route)-1==d+1,'spread antipodal distance must equal d+1')
    # Exact empty source/target facet intersections: y_j=1 forces every y_i>=1-t.
    for x in route:
        if any(v==1 for v in x):require(all(v>=1-t for v in x),'target row cannot meet any source row')
    # Two ordinary edges can connect a full-dimensional endpoint carrier.
    bridge=[(Q(0),)*d,tuple(t*int(i==0) for i in range(d))]
    bridge.append(add(bridge[-1],(1-t,)*d))
    ba=[]
    for x in bridge:
        vals=[dot(a,x) for a in A];evals+=len(A)
        require(all(v<=c for v,c in zip(vals,b)),'bridge H feasibility')
        act={i for i,(v,c) in enumerate(zip(vals,b)) if v==c};ba.append(act)
        require(rank([A[i] for i in act])==d,'bridge vertex rank')
    require(not(ba[0]&ba[-1]),'bridge endpoint carrier should be the WHOLE polytope')
    for i in (0,1):require(rank([A[j] for j in ba[i]&ba[i+1]])==d-1,'bridge step is not an edge')
    # Completely enumerate small H-vertex sets independently of the sum description.
    independent_vertices=None
    if d<=4:
        vs=set()
        for ids in combinations(range(len(A)),d):
            x=solve([A[i] for i in ids],[b[i] for i in ids])
            if x is not None and all(dot(a,x)<=c for a,c in zip(A,b)):vs.add(x)
        expected={(Q(0),)*d,(Q(1),)*d}
        for mask in range(1,(1<<d)-1):
            v=tuple(t*int(mask>>j&1) for j in range(d));expected.add(v);expected.add(add(v,(1-t,)*d))
        require(vs==expected,'spread H/V equality enumeration disagreement')
        independent_vertices=len(vs)
    rec={**got['verified'],'description_facets':len(A),'full_vertex_count_formula':(1<<(d+1))-2,
         'original_H_evaluations':evals,'independently_enumerated_vertices':independent_vertices,
         'source_target_facet_stars_disjoint':True, 'full_dimensional_carrier_two_edge_bridge':d}
    if d==24:
        (ROOT/'fixtures/spread_24_input.json').write_text(json.dumps(serial(data),indent=2)+'\n')
        (ROOT/'fixtures/spread_24_certificate.json').write_text(json.dumps(got['certificate'],indent=2)+'\n')
    return rec


def simple_separated_example():
    d=3;A,b=spread_rows(d,Q(2,3));rng=random.Random(210)
    for i in range(2*d,len(b)):b[i]+=Q(rng.randrange(1,500),100000)
    vs=set()
    for ids in combinations(range(len(A)),d):
        x=solve([A[i] for i in ids],[b[i] for i in ids])
        if x is not None and all(dot(a,x)<=c for a,c in zip(A,b)):vs.add(x)
    active={x:{i for i,(a,c) in enumerate(zip(A,b)) if dot(a,x)==c} for x in vs}
    require(all(len(s)==d and rank([A[i] for i in s])==d for s in active.values()),'perturbed example must be simple')
    for i in range(len(A)):
        pts=[x for x in vs if i in active[x]]
        require(pts and rank([sub(x,pts[0]) for x in pts[1:]])==d-1,'perturbed row is not a facet')
    u=(Q(0),)*d;v=(Q(1),)*d;require(u in vs and v in vs,'lost distinguished endpoints')
    for x in vs:require(not(any(t==0 for t in x) and any(t==1 for t in x)),'separated facet stars met')
    G={x:set() for x in vs}
    for x,y in combinations(vs,2):
        if len(active[x]&active[y])==d-1:G[x].add(y);G[y].add(x)
    rec={'dimension':d,'facets':len(A),'vertices':len(vs),'simple':True,
         'endpoint_distance':graph_dist(G,u)[v],'source_target_stars_disjoint':True}
    (ROOT/'fixtures/simple_separated_stars_3d.json').write_text(json.dumps(serial({'A':A,'b':b,'vertices':sorted(vs),'result':rec}),indent=2)+'\n')
    return rec


def main():
    start=time.monotonic();small=[];routes=edges=pairdist=enumverts=enumedges=0
    rng=random.Random(210)
    models=[('spread2',spread_input(2)),('spread3',spread_input(3)),
            ('triangle',{'dimension':2,'summands':[[[0,0],[1,0],[0,1]]],
                         'source_objective':[1,-10],'target_objective':[-10,1]})]
    for d,m in ((2,4),(3,4),(4,4)):
        z=(Q(0),)*d
        generators=[tuple(Q(int(i==j)) for j in range(d)) for i in range(d)]
        generators += [tuple(Q(rng.randrange(-5,6)) for _ in range(d)) for i in range(m-d)]
        data={'dimension':d,'summands':[[z,g] for g in generators],
              'source_objective':[-j for j in range(1,d+1)],'target_objective':[j for j in range(1,d+1)]}
        models.append((f'zonotope{d}_{m}',data))
    models.extend([('triangle_sum',{'dimension':2,'summands':[[[0,0],[1,0],[0,1]],[[0,0],[2,1],[1,3]]],
                                   'source_objective':[-2,-3],'target_objective':[3,2]}),
                   ('hypergraph4',coordinate_simplex_sum(4,[[0,1,2],[1,2,3],[0,3]]))])
    for name,data in models:
        d=data['dimension'];pts=all_sums(data['summands'],d)
        facets,vs,active,G=hull(pts,d);enumverts+=len(vs);enumedges+=sum(map(len,G.values()))//2
        normals={v:tuple(sum((Q(facets[i][j]) for i in active[v]),Q(0)) for j in range(d)) for v in vs}
        nr=ne=0
        for i,u in enumerate(vs):
            dist=graph_dist(G,u);require(len(dist)==len(vs),'independent hull graph disconnected');pairdist+=len(vs)
            for v in vs[:i]:
                case=deepcopy(data);case['source_objective']=normals[u];case['target_objective']=normals[v]
                result=sweep(case);route=[tuple(map(rat,p)) for p in result['certificate']['route']]
                require(route[0]==u and route[-1]==v,'H/V endpoints disagree')
                require(all(y in G[x] for x,y in zip(route,route[1:])),'sweep step not an independent hull edge')
                require(len(route)-1>=dist[v],'sweep shorter than graph distance')
                if 'zonotope_shortest_distance' in result['verified']:
                    require(len(route)-1==dist[v],'zonotope route not shortest')
                nr+=1;ne+=len(route)-1
        routes+=nr;edges+=ne;small.append({'name':name,'dimension':d,'vertices':len(vs),'facets':len(facets),
                                        'pair_routes':nr,'edge_occurrences':ne})
    spread=[spread_check(d) for d in (2,3,4,8,16,24)]
    routes+=2*len(spread);edges+=sum(r['ordinary_edges']+2 for r in spread)
    large=[]
    # A complete graphical zonotope: permutohedron, r! vertices, exact inversions.
    data=coordinate_simplex_sum(24,list(combinations(range(24),2)))
    result=sweep(data);require(result['verified']['ordinary_edges']==comb(24,2),'permutohedron inversion distance')
    rec={'name':'permutohedron_24',**result['verified'],'full_vertex_count_formula':factorial(24)}
    large.append(rec)
    (ROOT/'fixtures/permutohedron_24_input.json').write_text(json.dumps(serial(data),separators=(',',':'))+'\n')
    (ROOT/'fixtures/permutohedron_24_certificate.json').write_text(json.dumps(result['certificate'],separators=(',',':'))+'\n')
    # Nonzonotopal sum of coordinate simplices; no whole-polytope enumeration.
    intervals=[list(range(i,j)) for i in range(16) for j in range(i+2,17)]
    data=coordinate_simplex_sum(16,intervals)
    result=sweep(data);require('zonotope_shortest_distance' not in result['verified'],'nonzonotope falsely labeled')
    large.append({'name':'interval_simplex_sum_16',**result['verified']})
    (ROOT/'fixtures/interval_simplex_sum_16_input.json').write_text(json.dumps(serial(data),separators=(',',':'))+'\n')
    (ROOT/'fixtures/interval_simplex_sum_16_certificate.json').write_text(json.dumps(result['certificate'],separators=(',',':'))+'\n')
    # Dense noncoordinate zonotope directions, plus parallel and constant summands.
    data={'dimension':8,'summands':[[[0]*8,[rng.randrange(-50,51) for _ in range(8)]] for _ in range(100)],
          'source_objective':[11,17,23,31,43,59,71,101],'target_objective':[-101,-73,-47,-29,-19,-11,-5,-2]}
    # Correct only rare accidental orthogonality by resampling the objectives.
    for _ in range(10):
        try:result=sweep(data);break
        except ValueError as exc:
            if 'unique summand' not in str(exc):raise
            data['source_objective']=[rng.randrange(101,400) for _ in range(8)]
            data['target_objective']=[-rng.randrange(101,400) for _ in range(8)]
    large.append({'name':'dense_zonotope_8d_100',**result['verified']})
    routes+=len(large);edges+=sum(r['ordinary_edges'] for r in large)
    affine_examples=[]
    for data in (spread_input(4),models[-2][1]):
        d=data['dimension']
        T=[[Q(int(i==j)) if j<=i else Q(rng.randrange(-3,4),5) for j in range(d)] for i in range(d)]
        tr=[Q(rng.randrange(-3,4),7) for _ in range(d)]
        trans=deepcopy(data)
        trans['summands']=[[add(tuple(dot(row,tuple(map(rat,v))) for row in T),tr if k==0 else (Q(0),)*d)
                            for v in block] for k,block in enumerate(data['summands'])]
        TT=list(map(list,zip(*T)))
        trans['source_objective']=solve(TT,list(map(rat,data['source_objective'])))
        trans['target_objective']=solve(TT,list(map(rat,data['target_objective'])))
        r=sweep(trans);o=MinkowskiInput(data);p=MinkowskiInput(trans)
        require(len(o.directions)==len(p.directions),'affine map changed direction count')
        require(p.start==add(tuple(dot(row,o.start) for row in T),tr),'affine source mismatch')
        require(p.end==add(tuple(dot(row,o.end) for row in T),tr),'affine target mismatch')
        affine_examples.append(r['verified']);routes+=1;edges+=r['verified']['ordinary_edges']
    # Exposed faces remain sums of coordinate simplices. Their direction
    # count uses INTRINSIC rank, not the original ambient coordinate count.
    face_examples=[]
    parent=coordinate_simplex_sum(8,[list(range(i,j)) for i in range(8) for j in range(i+2,9)])
    PP=MinkowskiInput(parent)
    for trial in range(12):
        values=list(range(8)) if trial==0 else [rng.randrange(4) for _ in range(8)]
        normal=tuple(Q(values[i]-values[-1]) for i in range(7))
        tops=PP.maxima(normal)
        face=deepcopy(parent)
        face['summands']=[[block[j] for j in top] for block,top in zip(PP.summands,tops)]
        ff=MinkowskiInput(face);result=sweep(face)
        h=rank([sub(v,u) for block in ff.summands for u,v in combinations(block,2)])
        require(2*len(ff.directions)<=h*(h+1),'intrinsic root-direction count failed')
        level=sum(max(dot(v,normal) for v in block) for block in PP.summands)
        for v in result['certificate']['route']:
            require(dot(tuple(map(rat,v)),normal)==level,'face sweep leaves parent supporting face')
        face_examples.append({'intrinsic_dimension':h,**result['verified']})
        routes+=1;edges+=result['verified']['ordinary_edges']
    # Endpoint and collinearity boundary controls: zero-length, duplicates,
    # parallel blocks, and a collinear multi-vertex (nonminimal) description.
    boundary=[]
    for name,data in [
        ('same_endpoint',{'dimension':2,'summands':[[[0,0],[1,0],[0,1]]],'source_objective':[2,1],'target_objective':[3,-1]}),
        ('parallel_and_duplicate',{'dimension':2,'summands':[[[0,0],[1,0],[1,0]],[[0,0],[2,0]],[[0,0],[0,1]],[[3,4]]],
                                   'source_objective':[-1,-2],'target_objective':[2,1]}),
        ('collinear_face',{'dimension':2,'summands':[[[0,0],[1,0],[2,0]],[[0,0],[0,1]]],
                          'source_objective':[-1,-2],'target_objective':[2,1]}),
        ('point',{'dimension':3,'summands':[[[1,2,3]],[[2,3,4]]],'source_objective':[0,0,0],'target_objective':[1,1,1]}),
    ]:
        r=sweep(data);boundary.append({'name':name,**r['verified']});routes+=1;edges+=r['verified']['ordinary_edges']
    # Counterexample to a stronger assertion: sweeps of general sums need not
    # be shortest or stay in the endpoints' smallest common face.
    triangle=models[2][1];tri=sweep(triangle)
    require(tri['verified']['ordinary_edges']==2 and tri['certificate']['route'][1]==['0','0'],
            'triangle common-face counterexample missing')
    simple=simple_separated_example()
    # Rejection controls exercise exact support and endpoint binding.
    good_data=spread_input(3);good=sweep(good_data)['certificate'];rejected=[]
    def reject(name,data,cert=None):
        try:sweep(data) if cert is None else verify(data,cert)
        except (ValueError,KeyError,TypeError,ZeroDivisionError,IndexError):rejected.append(name)
        else:raise AssertionError('accepted negative control '+name)
    bad=deepcopy(good_data);bad['summands'][0][0]=[0.0,0,0];reject('float',bad)
    bad=deepcopy(good_data);bad['dimension']=True;reject('boolean_dimension',bad)
    bad=deepcopy(good_data);bad['summands'][0]=[];reject('empty_summand',bad)
    bad=deepcopy(good_data);bad['source_objective']=[0,0,0];reject('nonvertex_objective',bad)
    for name,key,value in [('hash','input_sha256','0'*64),('count','direction_count',0),
                           ('source','source_used',good['target_used']),('target','target_used',good['source_used'])]:
        bad=deepcopy(good);bad[key]=value;reject(name,good_data,bad)
    bad=deepcopy(good);bad['events']=bad['events'][1:];reject('missing_wall',good_data,bad)
    bad=deepcopy(good);bad['events']=list(reversed(bad['events']));reject('reordered_walls',good_data,bad)
    bad=deepcopy(good);bad['events'][0]['parameter']='1/2';reject('forged_time',good_data,bad)
    bad=deepcopy(good);bad['steps']=bad['steps'][1:];reject('omitted_edge',good_data,bad)
    bad=deepcopy(good);bad['steps'][0]['after_choices'][0]=1-bad['steps'][0]['after_choices'][0];reject('false_maximizer',good_data,bad)
    bad=deepcopy(good);bad['route'][1][0]='17/19';reject('false_coordinate',good_data,bad)
    bad=deepcopy(good);bad['route']=[bad['route'][0],bad['route'][-1]];reject('diagonal_as_edge',good_data,bad)
    bad=deepcopy(good);bad['source_used']=[str(-rat(x)) for x in good['target_used']];reject('simultaneous_crossings',good_data,bad)
    bad=deepcopy(good_data);bad['summands'][0][1]=[rat(1),rat(0),rat(0)];reject('changed_polytope',bad,good)
    budget_cases=0
    for e in range(1,16):
        for H in range(1,10):
            for a,b,c in product(range(H+1),repeat=3):
                if a+b+c<=3*e:
                    q=sum(h*(h+1)//2 for h in (a,b,c))
                    require(2*q<=3*e*(H+1),'same-certificate quadratic resource bound')
                    budget_cases+=1
    result={'status':'PASS','scope':'Exact rational/integer computation, not Lean or Prove2Me acceptance.',
            'small_models':small,'affine_examples':affine_examples,'exposed_face_examples':face_examples,'independently_enumerated_vertices':enumverts,
            'independently_enumerated_edges':enumedges,'independent_ordered_distances':pairdist,
            'total_route_certificates':routes,'total_ordinary_edge_occurrences':edges,
            'spread_family':spread,'large_examples':large,'boundary_examples':boundary,
            'simple_separated_star_example':simple,'triangle_sweep_not_shortest':{'sweep':2,'graph_distance':1},
            'arithmetic_mass_cases':budget_cases,'negative_controls_rejected':len(rejected),
            'negative_controls':rejected,'elapsed_seconds':round(time.monotonic()-start,3)}
    result['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                            for folder,ext in [('scripts','*.py'),('Solutions','*.lean')]
                            for p in sorted((ROOT/folder).glob(ext))}
    (ROOT/'research/DUAL_WALL_SWEEP_CHECK_2026-09-12.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
