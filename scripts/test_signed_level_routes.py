#!/usr/bin/env python3
"""Exact independent vertex/edge references and signed-coordinate controls."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import argparse,hashlib,json,random
import sympy as sp
import signed_level_routes as alg


def dump(p,x):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(alg.lp.serial(x),sort_keys=True,indent=2)+'\n')


def reference(data):
    A,b,_,_,vals=alg.model(data);d=data['dimension'];V={};bases=0;components={'anchored_trees':0,'unbalanced_unicycles':0}
    alphabet,_=alg.alphabet(d,vals)
    for J in combinations(range(len(A)),d):
        bases+=1;M=sp.Matrix([A[i] for i in J]);det=M.det()
        if not det:continue
        x=tuple(Q(z) for z in M.inv()*sp.Matrix([b[i] for i in J]))
        if not all(alg.lp.dot(a,x)<=t for a,t in zip(A,b)):continue
        assert all(t in alphabet for t in x)
        graph=[set() for _ in range(d)];unary=[];edges=[]
        for i in J:
            supp=[j for j,t in enumerate(A[i]) if t]
            if len(supp)==1:unary.append(supp[0])
            else:
                u,v=supp;graph[u].add(v);graph[v].add(u);edges.append((u,v))
        todo=set(range(d))
        while todo:
            C={min(todo)};q=list(C)
            while q:
                for v in graph[q.pop()]:
                    if v not in C:C.add(v);q.append(v)
            todo-=C;n=len(C);U=sum(j in C for j in unary);E=sum(u in C for u,v in edges)
            assert E+U==n
            if U:assert U==1 and E==n-1;components['anchored_trees']+=1
            else:assert E==n;components['unbalanced_unicycles']+=1
        V[x]=set(alg.edge.active(A,b,x))
    V=dict(sorted(V.items()));G={x:set() for x in V}
    for x,y in combinations(V,2):
        common=sorted(V[x]&V[y]);r=sp.Matrix([A[i] for i in common]).rank() if common else 0
        if r==d-1:
            G[x].add(y);G[y].add(x)
            direction=[z-t for t,z in zip(x,y)];nonzero=[abs(v) for v in direction if v]
            assert len(set(nonzero))==1 # signed pair kernel structure, independently checked
    return V,G,{'active_bases':bases,'vertices':len(V),'graph_edges':sum(map(len,G.values()))//2,
                'basis_component_checks':components,'alphabet_levels':len(alphabet)}


def distances(G,s):
    D={s:0};q=deque([s])
    while q:
        x=q.popleft()
        for y in G[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    assert len(D)==len(G);return D


def path(out):
    c=out['certificate'];left=[tuple(map(Q,x['point'])) for x in c['left']['vertices']]
    right=[tuple(map(Q,x['point'])) for x in c['right']['vertices']]
    return left+list(reversed(right[:-1]))


def small(folder):
    cases=[]
    for d in [1,2,3]:cases.append(('box'+str(d),dict(dimension=d,cuts_A=[],cuts_b=[])))
    cases += [('triangle_half',dict(dimension=3,cuts_A=[[1,1,0],[0,1,1],[1,0,1]],cuts_b=['2/3']*3)),
      ('parallel_unbalanced',dict(dimension=2,cuts_A=[[1,1],[1,-1]],cuts_b=['2/3','1/3'])),
      ('signed_cycle',dict(dimension=3,cuts_A=[[1,-1,0],[0,1,-1],[1,0,1]],cuts_b=['1/5','1/5','3/5'])),
      ('embedded',dict(dimension=3,cuts_A=[[1,1,0],[-1,-1,0],[0,1,-1]],cuts_b=[1,-1,0])),
      ('zero_RHS',dict(dimension=3,cuts_A=[[1,-1,0],[0,1,-1],[1,0,-1]],cuts_b=[0,0,0])),
      ('redundant_scaled',dict(dimension=3,cuts_A=[[3,3,0],[6,6,0],[0,2,-2]],cuts_b=[2,4,'1/2']))]
    rng=random.Random(274)
    for d in [3,3,3,4,4]:
        C=[];h=[]
        for _ in range(d+1):
            i,j=rng.sample(range(d),2);r=[0]*d;r[i]=rng.choice([-1,1]);r[j]=rng.choice([-1,1])
            C.append(r);h.append(rng.choice([Q(1,3),Q(2,3)]))
        cases.append(('random'+str(len(cases)),dict(dimension=d,cuts_A=C,cuts_b=h)))
    counts={'models':0,'routes':0,'edges':0,'BFS_edges':0,'nonshortest':0,'row_reentries':0,'active_bases':0,'vertices':0,'graph_edges':0}
    records=[];saved=[]
    for name,data in cases:
        V,G,info=reference(data);assert V
        pairs=list(combinations(V,2));rng.shuffle(pairs);pairs=pairs[:20]+[(next(iter(V)),next(iter(V)))]
        row={'name':name,**info,'routes':len(pairs),'edges':0,'BFS_edges':0,'nonshortest':0}
        for u,v in pairs:
            inp=alg.lp.serial({**data,'start':u,'target':v});out=alg.construct(inp);p=path(out)
            assert all(y in G[x] for x,y in zip(p,p[1:]));D=distances(G,u)[v];L=len(p)-1
            assert D<=L;row['edges']+=L;row['BFS_edges']+=D;row['nonshortest']+=L>D
            counts['row_reentries']+=out['verified']['original_row_reentries']
            if len(saved)<6 or L>D and not any(s['name']=='adverse' for s in saved):
                saved.append({'name':'adverse' if L>D else name,'input':inp,'result':out,'reference_distance':D})
        counts['models']+=1
        for k in ['routes','edges','BFS_edges','nonshortest','active_bases','vertices','graph_edges']:counts[k]+=row[k]
        records.append(row);print(name,row,flush=True)
    dump(folder/'small_saved.json',saved)
    return {'status':'PASS','counts':counts,'models':records}


def chain(d,tau):
    return dict(dimension=d,cuts_A=[[int(j==i)-int(j==i+1) for j in range(d)] for i in range(d-1)],
      cuts_b=[tau]*(d-1),start=[1]*d,target=[(d-1-i)*tau for i in range(d)])


def wheel(d,tau):
    E=sorted({tuple(sorted((0,i))) for i in range(1,d)}|{tuple(sorted((i,1+i%(d-1)))) for i in range(1,d)})
    return dict(dimension=d,cuts_A=[[int(i in e) for i in range(d)] for e in E],cuts_b=[tau]*len(E),
        start=[0]*d,target=[tau/2]*d)


def mixed(d,tau,sigma):
    r=d//2+1
    E=[(i,(i+1)%r) for i in range(r)]
    if r%2==0:E.append((0,2))
    C=[[int(j in e) for j in range(d)] for e in E];h=[sigma]*len(C)
    for i in range(r,d):
        for j in [i%r,(i+1)%r]:C.append([int(k==i)-int(k==j) for k in range(d)]);h.append(tau)
    return dict(dimension=d,cuts_A=C,cuts_b=h,start=[0]*d,target=[sigma/2]*r+[sigma/2+tau]*(d-r))


def large(folder,kind):
    records=[]
    cases=[('chain16_tiny',chain(16,Q(1,2**160))),('chain32_tiny',chain(32,Q(1,2**160))),
           ('wheel16',wheel(16,Q(2,3))),('wheel32',wheel(32,Q(2,3))),
           ('mixed16',mixed(16,Q(1,17),Q(5,7))),('mixed32',mixed(32,Q(1,17),Q(5,7)))]
    for name,data in cases:
        if not name.startswith(kind):continue
        out=alg.construct(data);p=path(out);d=data['dimension'];A,b,_,_,_=alg.model(data)
        t=tuple(map(Q,data['target']));overlap=sum(alg.lp.dot(a,t)==z for a,z in zip(A[2*d:],b[2*d:]))
        record={'name':name,**out['verified'],**out['discovery'],'simultaneously_active_cut_rows_at_target':overlap}
        if name.startswith('chain'):
            assert len(p)-1==d and out['verified']['common_rows_preserved']==0
            tau=data['cuts_b'][0];anchors=[]
            for j in range(d):
                x=[tau/2]*d;x[j]=0;anchors.append(x)
            for j in range(d):
                x=[1-tau/2]*d;x[j]=1;anchors.append(x)
            for j in range(d-1):
                x=[Q(1,2)]*d;x[j]+=tau/2;x[j+1]-=tau/2;anchors.append(x)
            for i,x in enumerate(anchors):assert all(alg.lp.dot(a,x)==z if i==j else alg.lp.dot(a,x)<z for j,(a,z) in enumerate(zip(A,b)))
            record['genuine_original_facets']=len(A);record['shortest_by_simple_target_facet_bound']=d
            record['integer_grid_bound_after_scaling']=d*2**160
        elif name.startswith('wheel'):
            # All upper box rows are redundant; lower and graph rows are genuine.
            tau=data['cuts_b'][0];anchors=[]
            for i in range(d):
                x=[tau/8]*d;x[i]=0;anchors.append((i,x))
            for j,a in enumerate(A[2*d:]):
                x=[tau/2 if z else tau/8 for z in a];anchors.append((2*d+j,x))
            for i,x in anchors:assert all(alg.lp.dot(a,x)==z if i==j else alg.lp.dot(a,x)<z for j,(a,z) in enumerate(zip(A,b)))
            record['genuine_original_facets']=d+len(data['cuts_A']);record['redundant_box_upper_rows']=d
            # center singleton tau*e0 to all-half is one edge; 0 to tau*e0 is one.
            mid=(tau,)+(Q(0),)*(d-1);short=[(Q(0),)*d,mid,tuple([tau/2]*d)]
            cert=alg.path_packet(A,b,short);alg.edge.verify_path(alg.raw_input(A,b,short[0],short[-1]),cert)
            record['separate_shortest_comparison']=2;out['two_edge_comparison']=cert
        dump(folder/(name+'.json'),{'input':data,'result':out,'class_geometry':record})
        records.append(record);print(name,record,flush=True)
    # Complete-graph examples realize exponentially many DISTINCT edge lines.
    realized=[]
    for d in ([4,8,16,32] if kind=='directions' else []):
        tau=Q(2,3);C=[[int(i in e) for i in range(d)] for e in combinations(range(d),2)]
        data=dict(dimension=d,cuts_A=C,cuts_b=[tau]*len(C),start=[0]*d,target=[tau/2]*d)
        A,b,_,_,_=alg.model(data);examples=[]
        subsets=list(combinations(range(1,d),2))[:5]+[tuple(range(1,d))]
        for T in subsets:
            x=(tau,)+(Q(0),)*(d-1);y=tuple(tau/2 if j==0 or j in T else Q(0) for j in range(d))
            cert=alg.path_packet(A,b,[x,y]);alg.edge.verify_path(alg.raw_input(A,b,x,y),cert);examples.append(cert)
        levels,_=alg.alphabet(d,(tau,))
        realized.append({'dimension':d,'genuine_facets':d+len(C),'distinct_edge_lines_lower_bound':2**(d-1)-d,
            'all_pairs_level_bound':d*(len(levels)-1),'explicit_sample_edges_checked':len(examples),
            'scope':'The exponential count is a proved family formula, not enumerated. Classical stable-set bounds are stronger.'})
    return {'status':'PASS','routes':records,'exponential_direction_family':realized}


def negative(folder):
    inp=wheel(5,Q(2,3));out=alg.construct(inp);bad=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):bad.append(name);return
        raise AssertionError('accepted '+name)
    def mutate(name,fun):
        c=deepcopy(out['certificate']);fun(c);reject(name,lambda:alg.verify(inp,c))
    mutate('input_hash',lambda c:c.update(input_sha256='wrong'))
    mutate('omit_level',lambda c:c['levels'].pop())
    mutate('RHS_magnitude',lambda c:c.update(RHS_values=['1']))
    mutate('rank_bound',lambda c:c.update(bound=0))
    mutate('common_rows',lambda c:c.update(common_rows=[0]))
    mutate('phase_direction',lambda c:c['phases'][0].update(sign=-c['phases'][0]['sign']))
    mutate('missing_phase',lambda c:c['phases'].pop())
    mutate('missing_dual',lambda c:c['phases'][0].update(left_dual=[]))
    mutate('optimum_value',lambda c:c['phases'][0].update(value='999'))
    mutate('phase_range',lambda c:c['phases'][0]['left_range'].__setitem__(0,1))
    mutate('vertex_inverse',lambda c:c['left']['vertices'][0]['inverse'][0].__setitem__(0,'999'))
    mutate('fractional_phase_index',lambda c:c['phases'][0].update(coordinate='0'))
    reject('unequal_pair_coefficients',lambda:alg.construct({**inp,'cuts_A':[[1,2,0,0,0]],'cuts_b':[1]}))
    reject('three_coordinate_row',lambda:alg.model({**inp,'cuts_A':[[1,1,1,0,0]],'cuts_b':[1]}))
    reject('float_rhs',lambda:alg.model({**inp,'cuts_b':[0.66]*len(inp['cuts_b'])}))
    reject('false_original_rows',lambda:alg.model({**inp,'A':[[1]*5],'b':[1]}))
    reject('alphabet_cap',lambda:alg.construct(inp,alphabet_cap=1))
    reject('pivot_cap',lambda:alg.construct(inp,pivot_cap=1))
    reject('edge_cap',lambda:alg.construct(inp,edge_cap=0))
    # Equal number of RHS values does not control unbalanced coefficient gains.
    levels={Q(0),Q(1)};growth=[]
    for d in range(1,13):
        assert len(levels)==2**d
        growth.append({'dimension':d,'distinct_last_coordinate_values':len(levels)})
        levels={z/4 for z in levels}|{1-z/4 for z in levels}
    # Pure finite cap state, perturbation size and precision are separate.
    return {'status':'PASS','rejected_controls':bad,'unequal_gain_cube':growth,
            'scope':'Exponential coordinate levels obstruct this method, not short paths: the deformed cube still has diameter d.'}


def replay(folder):
    saved=[]
    for f in sorted(folder.glob('*.json')):
        data=json.loads(f.read_text())
        if f.name=='small_saved.json':saved.extend(data)
        elif isinstance(data,dict) and 'input' in data and 'result' in data:saved.append(data)
    old={n:getattr(alg.edge,n) for n in ('inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses')}
    oldc=alg.construct;oldmax=alg.lp.ExactLP.maximize;oldlex=alg.lex_objective
    def kill(*a,**k):raise AssertionError('discovery invoked in verification')
    comparisons=0
    try:
        for n in old:setattr(alg.edge,n,kill)
        alg.construct=alg.lp.ExactLP.maximize=alg.lex_objective=kill
        for item in saved:
            data=item['input'];out=item['result'];assert alg.verify(data,out['certificate'])==out['verified']
            if 'two_edge_comparison' in out:
                A,b,_,_,_=alg.model(data);c=out['two_edge_comparison'];u=tuple(map(Q,data['start']));v=tuple(map(Q,data['target']))
                alg.edge.verify_path(alg.raw_input(A,b,u,v),c);comparisons+=1
    finally:
        for n,f in old.items():setattr(alg.edge,n,f)
        alg.construct=oldc;alg.lp.ExactLP.maximize=oldmax;alg.lex_objective=oldlex
    return {'status':'PASS','saved_routes':len(saved),'comparison_routes':comparisons,
            'LP_inverse_elimination_and_route_producers_disabled':True}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','chain','wheel','mixed','directions','negative','audit'],required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args();a.fixtures.mkdir(parents=True,exist_ok=True)
    if a.stage in ['chain','wheel','mixed','directions']:out=large(a.fixtures,a.stage)
    else:out={'small':small,'negative':negative,'audit':replay}[a.stage](a.fixtures)
    out['source_sha256']={n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in
        ['signed_level_routes.py','test_signed_level_routes.py','exact_farkas_lp.py','original_route_exclusion.py']}
    dump(a.out,out)
if __name__=='__main__':main()
