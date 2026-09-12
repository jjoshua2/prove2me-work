#!/usr/bin/env python3
"""Reproducible exact regressions, not Lean or global-conjecture verification."""
from __future__ import annotations
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import random
from hirsch_exact_geometry import *
import packing_normalization as pn
import rank_local_monotone_routes as rr
import packing_support_routes as ps

ROOT=Path(__file__).resolve().parents[1]

def orthant(R: Matrix, eta: str='1/100') -> dict:
    d=len(R[0]);return {'A':[[-x for x in row] for row in eye(d)]+R,'b':[0]*d+[1]*len(R),'simple_rows':list(range(d)),'eta':eta}

def polygon(m: int, d: int=2) -> dict:
    return {'B':[[Q(0)]*d for _ in range(d)],'b':[Q(m*m+1)]*d,'weights':[1]*d,
            'cuts':[[Q(2*k+1),Q(1)]+[Q(0)]*(d-2) for k in range(m)],
            'bounds':[Q(m*m+k*(k+1)) for k in range(m)]}

def graph_distances(adj: dict, start: tuple) -> dict:
    out={start:0};todo=deque([start])
    while todo:
        a=todo.popleft()
        for b in adj[a]:
            if b not in out:out[b]=out[a]+1;todo.append(b)
    return out

def affine_input(data: dict, t: int) -> dict:
    a,b=matrix(data['A']),vector(data['b']);d=len(a[0])
    # x = T z + v, exact unimodular upper-triangular spatial change.
    T=[[Q(i==j)+Q(t if j==i+1 else 0) for j in range(d)] for i in range(d)]
    v=[Q((i+1)*t,3) for i in range(d)]
    return dict(data,A=matmul(a,T),b=[rhs-dot(row,v) for row,rhs in zip(a,b)])

def check_normalizations(stats: dict) -> tuple[dict,dict]:
    cases=[]
    for d in range(2,6):
        cases.append(orthant([[Q(1)]*d], '1/1000000'))
        R=eye(d)+[[Q(2,2*d-1)]*d]
        cases.append(orthant(R, '1/1000000'))
    cases.append(orthant([[Q(2),Q(-3)],[Q(-1),Q(2)]]))
    cases.append({'A':[[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],'b':[0,1,1,1,1],'simple_rows':[0,1,3],'eta':'1/1000000'})
    for m in (3,5,8):
        pp=polygon(m);cases.append({'A':[[-1,0],[0,-1]]+pp['cuts'],'b':[0,0]+pp['bounds'],'simple_rows':[0,1],'eta':'1/10000'})
    cases += [affine_input(p,t) for p in cases[:6] for t in (1,2)]
    fixture=None
    for p in cases:
        result=pn.certificate(p);cert=result['certificate'];pn.verify(p,jsonable(cert))
        a,b=matrix(p['A']),vector(p['b']);d=len(a[0]);vv=vertices(a,b);g=graph(a,vv)
        H=matrix(cert['packing_rows']);qa=[[-x for x in row] for row in eye(d)]+H;qb=[Q(0)]*d+[Q(1)]*len(H)
        qv=vertices(qa,qb);qg=graph(qa,qv)
        mapped={v:tuple(pn.forward(p,cert,list(v))) for v in vv}
        assert set(mapped.values())==set(qv)
        for v,y in mapped.items():
            assert pn.backward(p,cert,list(y))==list(v)
            assert sum(y)<1 and all(0<=z<1 for z in y)
            # Check the active-row correspondence, not just vertex counts.
            expected={j for j,i in enumerate(p['simple_rows']) if i in vv[v]}
            expected|={d+j for j,i in enumerate(cert['upper_rows']) if i in vv[v]}
            assert qv[y]==expected
            assert {mapped[z] for z in g[v]}==set(qg[y])
            dp,dq=graph_distances(g,v),graph_distances(qg,y)
            assert all(dp[z]==dq[mapped[z]] for z in vv)
        gs=graph_stats(g)
        stats['normalizations']+=1;stats['normalization_vertices']+=len(vv)
        stats['normalization_edges']+=gs['edges'];stats['normalization_ordered_distances']+=gs['ordered_distances']
        if result['search']['method']=='exact-dual-basis':stats['dual_search_cases']+=1
        if len(vv)!=2**d:stats['noncube_normalizations']+=1
        if d==4 and len(vv)>16 and p['eta']=='1/1000000':fixture=(p,result)
    assert fixture
    return fixture

def check_routes(stats: dict) -> tuple[dict,dict]:
    cases=[]
    for d in (2,3,4):
        B=[[Q(0) if i==j else Q(1,4*d) for j in range(d)] for i in range(d)]
        basic={'B':B,'b':[Q(1)]*d,'weights':[1]*d}
        cases.append(dict(basic,cuts=[],bounds=[]))
        cases.append(dict(basic,cuts=[[Q(1)]*d],bounds=[Q(3,2)]))
        # Many cut rows, exact cut rank at most two, including nonparallel cuts.
        cuts=[[Q(k+1),Q(5-k)]+[Q(0)]*(d-2) for k in range(5)]
        cases.append(dict(basic,cuts=cuts,bounds=[Q(4)+Q(k,3) for k in range(5)]))
    cases.append(dict(polygon(5,3)))
    # Degenerate cuts and duplicates, including a lower-dimensional Q.
    cases.append({'B':[[0,0],[0,0]],'b':[1,1],'weights':[1,1],
                  'cuts':[[1,0],[2,0],[0,0]],'bounds':[0,0,0]})
    cases.append({'B':[[0,0],[0,0]],'b':[1,1],'weights':[1,1],
                  'cuts':[[1,1],[2,2],[0,0]],'bounds':['3/2',3,0]})
    # Full-rank cuts with a genuine three-dimensional newly-created vertex.
    cases.append({'B':[[0,0,0],[0,0,0],[0,0,0]],'b':[10,10,10],'weights':[1,1,1],
                  'cuts':[[2,1,1],[1,2,1],[1,1,2]],'bounds':[4,4,4]})
    rng=random.Random(206)
    for data in cases:
        m=rr.model(data);vv=vertices(m['A'],m['rhs']);g=graph(m['A'],vv);gs=graph_stats(g)
        stats['routed_models']+=1;stats['route_models_vertices']+=len(vv)
        stats['route_models_edges']+=gs['edges'];stats['route_models_ordered_distances']+=gs['ordered_distances']
        pts=list(vv)
        pairs=[(x,y) for x in pts for y in pts] if len(pts)<=9 else [(rng.choice(pts),rng.choice(pts)) for _ in range(12)]
        for x,y in pairs:
            p=dict(data,start=list(x),target=list(y));out=rr.route(p)
            checked=rr.verify_route(p,jsonable(out['certificate']))
            assert checked['ordinary_edges']>=graph_distances(g,x)[y]
            stats['explicit_routes']+=1;stats['certified_route_edges']+=checked['ordinary_edges']
            stats['endpoint_face_dimensions_seen'].update(checked['endpoint_face_dimensions'])
    # Large dense feedback: local rank two, 30 distinct nonparallel monotone cuts.
    d,q=32,30
    data=polygon(q,d)
    data['B']=[[Q(0) if i==j else Q(1,10*d) for j in range(d)] for i in range(d)]
    data['b']=[Q(10000)]*d
    m=rr.model(data)
    def endpoint(k:int,upper:list[int])->Vector:
        free=[0,1];R=inverse([[Q(i==j)-m['B'][i][j] for j in upper]for i in upper]) if upper else []
        x=[Q(0)]*d;x[:2]=[Q(k),Q(q*q-k*k)]
        for a,i in enumerate(upper):x[i]=dot(R[a],[m['b'][j]+dot(m['B'][j][:2],x[:2]) for j in upper])
        verify_vertex(m['A'],m['rhs'],x);return x
    data['start']=endpoint(7,list(range(2,17)));data['target']=endpoint(23,list(range(17,32)))
    result=rr.route(data,max_local_bases=10000)
    assert result['verified']['endpoint_face_dimensions']==[2,2]
    assert result['verified']['global_cut_rank']==2 and result['verified']['middle_edges']==30
    stats['large_example']=result['verified']
    stats['large_example']['local_vertices_enumerated']=[result['certificate'][k]['local_vertices_enumerated']for k in ('left','right')]
    stats['explicit_routes']+=1;stats['certified_route_edges']+=result['verified']['ordinary_edges']
    return data,result

def check_polygons(stats:dict)->None:
    for m in (2,3,4,5,8,12,20,32):
        data=polygon(m);mod=rr.model(data);vv=vertices(mod['A'],mod['rhs']);g=graph(mod['A'],vv);gs=graph_stats(g)
        expected={(Q(0),Q(0))}|{(Q(k),Q(m*m-k*k)) for k in range(m+1)}
        assert set(vv)==expected and gs['diameter']==(m+2)//2
        assert all(len(v)==2 for v in g.values()) and mod['cut_rank']==2
        stats['polygon_counts'].append({'cuts':m,**gs})
    a=matrix([[-1,0],[0,-1],[2,1],[1,2]]);b=vector([0,0,3,3]);vv=vertices(a,b);g=graph(a,vv)
    x=(Q(1),Q(1));assert x in g
    assert all(any(y[i]>x[i] for i in range(2))for y in g[x])
    feasible=[Q(1),Q(0)];active=active_set(a,b,feasible);assert rank([a[i]for i in active])<2
    stats['coordinatewise_edge_descent_counterexample']={'vertex':x,'neighbors':g[x], 'feasible_nonvertex_coordinate_deletion':feasible}

def check_packing_support(stats:dict)->None:
    cases=[{'A':[[1,2,3],[2,4,6]],'b':[6,13]},
           {'A':[[2,1],[1,2]],'b':[3,3]},
           {'A':[[2,1,1],[1,2,1],[1,1,2]],'b':[4,4,4]},
           {'A':[[1,1],[1,0]],'b':[1,0]}]
    stats['packing_support_routes']=0;stats['packing_support_edges']=0
    for p in cases:
        m=ps.model(p);vv=vertices(m['full_A'],m['full_b'])
        for x in vv:
            for y in vv:
                data=dict(p,start=list(x),target=list(y));out=ps.route(data)
                ps.verify(data,jsonable(out['certificate']))
                stats['packing_support_routes']+=1;stats['packing_support_edges']+=out['verified']['ordinary_edges']
    d,q=64,30
    data={'A':[[2*k+1 if j%2==0 else 1 for j in range(d)]for k in range(q)],
          'b':[q*q+k*(k+1)for k in range(q)]}
    data['start']=[Q(0)]*d;data['start'][0]=Q(7);data['start'][1]=Q(q*q-49)
    data['target']=[Q(0)]*d;data['target'][32]=Q(23);data['target'][33]=Q(q*q-529)
    result=ps.route(data,max_local_bases=10000);ps.verify(data,jsonable(result['certificate']))
    assert result['verified']['cut_rank']==2 and result['verified']['global_rank_budget']==32
    stats['packing_support_large_example']=result['verified']
    stats['packing_support_large_example']['local_vertices_enumerated']=[result['certificate'][k]['local_vertices_enumerated']for k in ('left','right')]
    stats['packing_support_routes']+=1;stats['packing_support_edges']+=result['verified']['ordinary_edges']
    for name,val in [('rank_two_packing_64d_input.json',data),('rank_two_packing_64d_route.json',result)]:
        (ROOT/'research'/name).write_text(json.dumps(jsonable(val),indent=2)+'\n')


def check_todd(stats: dict) -> None:
    # Published data: Black--Borgwardt--Brugger, arXiv:2302.03977, Section 2.2.
    p={'A':[[-v for v in row] for row in eye(4)]+matrix([[7,4,1,0],[4,7,0,1],[43,53,2,5],[53,43,5,2]]),
       'b':[0,0,0,0,1,1,8,8], 'simple_rows':[0,1,2,3], 'eta':'1/100000000'}
    out=pn.certificate(p);c=out['certificate'];a,b=matrix(p['A']),vector(p['b'])
    vv=vertices(a,b);g=graph(a,vv);start=tuple(Q(k,19) for k in (1,1,8,8));target=(Q(0),)*4
    directed={v:[z for z in ng if sum(z)<sum(v)]for v,ng in g.items()}
    ordinary=len(shortest_path(g,start,target))-1;monotone=len(shortest_path(directed,start,target))-1
    assert ordinary==4 and monotone==5
    H=matrix(c['packing_rows']);qa=[[-v for v in row]for row in eye(4)]+H;qb=vector([0]*4+[1]*4)
    qv=vertices(qa,qb);qg=graph(qa,qv);mapping={v:tuple(pn.forward(p,c,list(v)))for v in vv}
    assert set(mapping.values())==set(qv)
    for v in vv:
        assert {mapping[z]for z in directed[v]}=={z for z in qg[mapping[v]] if sum(z)<sum(mapping[v])}
    assert len(shortest_path({v:[z for z in ng if sum(z)<sum(v)]for v,ng in qg.items()},mapping[start],mapping[target]))-1==5
    stats['published_todd_regression']={'source':'https://arxiv.org/html/2302.03977#S2.SS2',
        **graph_stats(g),'ordinary_start_to_origin':ordinary,'monotone_start_to_origin':monotone,
        'near_uniform_eta':p['eta'],'packing_exact_cut_rank':rank(H),'orientation_preserved':True}
    (ROOT/'research'/'near_uniform_todd_input.json').write_text(json.dumps(jsonable(p),indent=2)+'\n')
    (ROOT/'research'/'near_uniform_todd_certificate.json').write_text(json.dumps(jsonable(out),indent=2)+'\n')


def check_negatives(stats:dict, normfixture:tuple, routefixture:tuple)->None:
    def reject(fn):
        try:fn()
        except (ValueError,KeyError,TypeError,ZeroDivisionError):stats['negative_controls']+=1;return
        raise AssertionError('A corrupt/out-of-scope certificate was accepted')
    p,out=normfixture;c=out['certificate']
    for key,bad in [('scale',0),('scale',1),('origin',[99]*4),('upper_rows',c['upper_rows'][:-1]),
                    ('bounding_weights',[0]*len(c['bounding_weights'])),('uniform_inverse_margin',0),
                    ('target_denominator_weights',[0]*len(c['target_denominator_weights']))]:
        cc=deepcopy(c);cc[key]=bad;reject(lambda cc=cc:pn.verify(p,cc))
    for key,bad in [('eta',0),('eta',1),('eta',0.01),('simple_rows',[0,0,1,2]),('keep',[0])]:
        pp=deepcopy(p);pp[key]=bad;reject(lambda pp=pp:pn.certificate(pp))
    pp=orthant([[Q(2),Q(-3)],[Q(-1),Q(2)]]);reject(lambda:pn.certificate(pp,max_bases=0))
    pp=orthant([[Q(1),Q(-2)]]);reject(lambda:pn.certificate(pp))
    simple={'B':[[0,0],[0,0]],'b':[100,100],'weights':[1,1],
            'cuts':[[1,1],[3,1],[5,1],[7,1]],'bounds':[16,18,22,28],'start':[1,15],'target':[3,7]}
    good=rr.route(simple)['certificate']
    cc=deepcopy(good);cc['left']['face']['linear'][0][0]+=1;reject(lambda:rr.verify_route(simple,cc))
    cc=deepcopy(good);cc['vertices']=[vector(simple['start']),vector(simple['target'])];reject(lambda:rr.verify_route(simple,cc))
    cc=deepcopy(good);cc['left']['vertices']=[vector(simple['start']),[Q(0),Q(0)]];reject(lambda:rr.verify_route(simple,cc))
    pp=deepcopy(simple);pp['cuts'][0][0]=-1;reject(lambda:rr.route(pp))
    pp=deepcopy(simple);pp['B'][0][0]=1;reject(lambda:rr.route(pp))
    pp=deepcopy(simple);pp['bounds'][0]=-1;reject(lambda:rr.route(pp))
    pp=deepcopy(simple);pp['start']=[1,1];reject(lambda:rr.route(pp))
    reject(lambda:rr.route(simple,max_local_bases=1))
    pp=deepcopy(simple);pp['weights'][0]=1.0;reject(lambda:rr.route(pp))
    packed={'A':[[2,1],[1,2]],'b':[3,3],'start':[1,1],'target':[0,0]}
    pc=ps.route(packed)['certificate']
    wrong=deepcopy(pc);wrong['left']['support']=[0];reject(lambda:ps.verify(packed,wrong))
    wrong=deepcopy(pc);wrong['left']['vertices']=[[1,1],[1,0],[0,0]];reject(lambda:ps.verify(packed,wrong))
    wrong=deepcopy(packed);wrong['A'][0][0]=-2;reject(lambda:ps.route(wrong))
    wrong=deepcopy(packed);wrong['A']=[[1,0]];wrong['b']=[1];reject(lambda:ps.route(wrong))
    reject(lambda:ps.route(packed,max_local_bases=1))

def main()->None:
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--section',choices=['all','normalization','routes','polygons','support'],default='all');args=p.parse_args()
    stats={'normalizations':0,'normalization_vertices':0,'normalization_edges':0,'normalization_ordered_distances':0,
           'dual_search_cases':0,'noncube_normalizations':0,'routed_models':0,'route_models_vertices':0,
           'route_models_edges':0,'route_models_ordered_distances':0,'explicit_routes':0,'certified_route_edges':0,
           'endpoint_face_dimensions_seen':set(),'polygon_counts':[],'negative_controls':0}
    if args.section in ('all','normalization'):
        nf=check_normalizations(stats)
        for name,v in zip(('near_uniform_noncube_input.json','near_uniform_noncube_certificate.json'),nf):
            (ROOT/'research'/name).write_text(json.dumps(jsonable(v),indent=2)+'\n')
    if args.section in ('all','routes'):
        rf=check_routes(stats)
        for name,v in zip(('rank_two_dense_32d_input.json','rank_two_dense_32d_route.json'),rf):
            (ROOT/'research'/name).write_text(json.dumps(jsonable(v),indent=2)+'\n')
    if args.section in ('all','polygons'):check_polygons(stats)
    if args.section in ('all','support'):check_packing_support(stats)
    if args.section=='all':
        check_todd(stats)
        check_negatives(stats,nf,rf)
    stats['status']='PASS';stats['scope']='Executed exact rational regressions only; no Lean or platform verification.'
    stats['source_sha256']={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest()
                            for folder in ('scripts','Solutions') for f in sorted((ROOT/folder).glob('*')) if f.is_file()}
    text=json.dumps(jsonable(stats),indent=2,sort_keys=True)+'\n'
    (ROOT/'research'/f'PACKING_RANK_CHECK_{args.section}.json').write_text(text)
    print(text)

if __name__=='__main__':main()
