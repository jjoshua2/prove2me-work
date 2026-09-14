#!/usr/bin/env python3
"""Capped Klee--Minty: exponential normalized-gain routes on a FULL common face.

The classical lower-bound mechanism is attributed, not claimed new. The cap
and strict target expose the relevant gap in a normalized tangent interface.
This is an exact research regression, not a Lean proof of Polynomial Hirsch.
"""
from fractions import Fraction as Q
from copy import deepcopy
from collections import deque
from itertools import combinations
from pathlib import Path
import argparse, hashlib, json, time
import simple_tangent_policy_audit as audit
from simple_tangent_policy_audit import (require, dot, serial, basis_packet, audit_basis,
    make_step, audit_step, audit_target, audit_route, construct, active_rows, feasible)

ROOT=Path(__file__).resolve().parents[1]


def upper_rows(d):
    return [[2**(i-j+1) if j<i else int(j==i) for j in range(d)] for i in range(d)]


def cube_vertex(bits):
    U=upper_rows(len(bits)); x=[]
    for i,bit in enumerate(bits): x.append(bit*(5**(i+1)-dot(U[i][:i],x)))
    return x


def cube_directions(bits):
    U=upper_rows(len(bits)); out=[];d=len(bits)
    for i,bit in enumerate(bits):
        r=[0]*d;r[i]=1-2*bit
        for j in range(i+1,d):r[j]=-bits[j]*dot(U[j][:j],r[:j])
        out.append(r)
    return out


def gray_bits(t,d):
    g=t^(t>>1);return [(g>>i)&1 for i in range(d)]


def instance(d):
    require(type(d)is int and d>=2,'dimension must be at least two')
    U=upper_rows(d);c=[2**(d-1-i) for i in range(d)];N=2**(d+1)//3
    one=[1]*d;next_bits=gray_bits(N+1,d);ell=next(i for i in range(d) if next_bits[i]!=1)
    target_point=[Q(x+y,2) for x,y in zip(cube_vertex(one),cube_vertex(next_bits))]
    gamma=dot(c,target_point);delta=Q(1,2**(d+4))
    q=[sum(U[j][i] for j in range(d) if j!=ell) for i in range(d)]
    f=[cc+delta*qq for cc,qq in zip(c,q)]
    A=[[-int(i==j) for j in range(d)] for i in range(d)]+U+[c]
    b=[0]*d+[5**(i+1) for i in range(d)]+[gamma]
    target=basis_packet(A,b,target_point);target['weights']=[Q(1) if j==2*d else delta for j in target['active']]
    audit_target(A,b,f,target)
    return {'A':A,'b':b,'objective':f,'start':[0]*d,'target':target,
      'gray_index':N,'deleted_upper':ell,'cap':gamma,'perturbation':delta}


def old_basis(A,b,bits):
    d=len(bits);x=cube_vertex(bits);J=active_rows(A,b,x);D=cube_directions(bits)
    require(len(J)==d and 2*d not in J,'not a pre-cap cube vertex')
    return {'point':x,'active':J,'directions':[D[j%d] for j in J]}


def facet_witnesses(data):
    A,b,f=data['A'],data['b'],data['objective'];d=len(f);out=[]
    base0=basis_packet(A,b,[0]*d);base1=old_basis(A,b,[1]*d)
    for j in range(2*d+1):
        base=base0 if j<d else base1 if j<2*d else data['target']
        x,J,D=audit_basis(A,b,base);loc=J.index(j)
        r=[sum(v[k] for i,v in enumerate(D) if i!=loc) for k in range(d)]
        limits=[Q(bb-dot(a,x),dot(a,r)) for a,bb in zip(A,b) if dot(a,r)>0]
        step=min([Q(1)]+[v/2 for v in limits]);require(step>0,'no facet-relative interior')
        z=[xx+step*rr for xx,rr in zip(x,r)]
        require(feasible(A,b,z) and active_rows(A,b,z)==[j] and any(A[j]),'row is not a genuine facet')
        out.append(z)
    inside=[Q(x,2) for x in cube_vertex([1]*d)]
    require(all(dot(a,inside)<bb for a,bb in zip(A,b)),'polytope not full-dimensional')
    require(not(set(active_rows(A,b,data['start']))&set(data['target']['active'])),'endpoints share a facet')
    require(all(x>0 for x in data['target']['point']),'target retained a start lower facet')
    return out


def independent_graph(data):
    """Independent all-active-subsets enumeration, for dimensions <=4 ONLY."""
    import sympy as sp
    A,b=data['A'],data['b'];d=len(A[0]);points=set();checks=0
    for ids in combinations(range(len(A)),d):
        checks+=1;M=sp.Matrix([A[i] for i in ids]);rhs=sp.Matrix([b[i] for i in ids])
        if M.det()==0:continue
        x=tuple(Q(str(z)) for z in M.inv()*rhs)
        if feasible(A,b,x):points.add(x)
    J={x:set(active_rows(A,b,x)) for x in points};require(all(len(j)==d for j in J.values()),'reference not simple')
    adj={x:[] for x in points}
    for x,y in combinations(points,2):
        common=J[x]&J[y]
        if len(common)==d-1:
            require(sp.Matrix([A[i] for i in common]).rank()==d-1,'bad reference edge rank')
            adj[x].append(y);adj[y].append(x)
    src=tuple(data['start']);tar=tuple(data['target']['point']);dist={src:0};Q0=deque([src])
    while Q0:
        x=Q0.popleft()
        for y in adj[x]:
            if y not in dist:dist[y]=dist[x]+1;Q0.append(y)
    require(len(dist)==len(points),'reference graph disconnected')
    return {'vertices':len(points),'edges':sum(map(len,adj.values()))//2,'endpoint_distance':dist[tar],
      'active_subsets':checks},adj


def main(max_dimension):
    require(5<=max_dimension<=12,'max dimension must be between 5 and 12')
    started=time.monotonic();results=[];total=long_edges=fast_edges=facet_checks=0;reference=[];fixtures={}
    for d in range(2,max_dimension+1):
        data=instance(d);A,b,f=data['A'],data['b'],data['objective'];N=data['gray_index']
        facets=facet_witnesses(data);facet_checks+=len(facets);steps=[];x=data['start'];min_margin=None
        for t in range(N+1):
            bits=gray_bits(t,d);require(cube_vertex(bits)==x,'Gray trace differs from actual pivot recurrence')
            basis=old_basis(A,b,bits);s=make_step(A,b,f,basis,'normalized')
            next_point=audit_step(A,b,f,s,'normalized')
            gains=sorted([dot(f,r) for r in basis['directions']],reverse=True)
            margin=gains[0]-gains[1];require(margin>0,'tie could explain long path')
            min_margin=margin if min_margin is None else min(min_margin,margin)
            expect=data['target']['point'] if t==N else cube_vertex(gray_bits(t+1,d))
            require(next_point==expect,'wrong capped path');x=next_point;steps.append(s)
        long={'policy':'normalized','steps':steps}
        long_report=audit_route(A,b,f,data['start'],data['target'],long)
        require(long_report['edges']==N+1,'wrong exact exponential length')
        # Positive comparison: identical H-input, objective, source and target.
        fast=construct(A,b,f,data['start'],data['target'],'full_gain',edge_cap=4*d)
        fast_report=audit_route(A,b,f,data['start'],data['target'],fast)
        require(fast_report['edges']==d,'short route count changed')
        # Every simple path must drop the d initial lower facets, at most one
        # per edge; all target coordinates are positive. Thus d is a lower bound.
        removed=[]
        for s in fast['steps']:
            before=set(s['basis']['active']);after=set(active_rows(A,b,s['to']))
            require(len(before-after)==1 and len(after-before)==1,'not a simple edge transition')
            removed.extend((before-after)&set(range(d)))
        require(sorted(removed)==list(range(d)),'shortestness facet charge failed')
        # Uniform all-d short construction: low-to-high upper choices then cap.
        prefix=[cube_vertex([1]*j+[0]*(d-j)) for j in range(d+1)]+[data['target']['point']]
        for a,z in zip(prefix,prefix[1:]):
            require(feasible(A,b,a) and feasible(A,b,z),'prefix leaves cap')
            require(len(set(active_rows(A,b,a))&set(active_rows(A,b,z)))==d-1,'prefix pair not an original edge')
        # Avoid trusting the local inverse producer during replay.
        old=audit.invert
        def unavailable(*args):raise AssertionError('auditor invoked inverse search')
        audit.invert=unavailable
        audit_route(A,b,f,data['start'],data['target'],fast)
        audit.invert=old
        if d<=4:
            ref,adj=independent_graph(data);reference.append({'dimension':d,**ref})
            require(ref['endpoint_distance']==d,'independent BFS disagrees with shortestness')
            for route in (long,fast):
                for s in route['steps']:require(tuple(s['to']) in adj[tuple(s['basis']['point'])],'not a reference original edge')
        if d<=5:
            fixtures[d]={'input':data,'normalized':long,'full_gain':fast,'facet_anchors':facets}
        results.append({'dimension':d,'original_facets':2*d+1,'minimal_common_face_dimension':d,
          'normalized_policy_edges':len(steps),'full_gain_policy_edges':len(fast['steps']),
          'certified_graph_distance':d,'all_dimension_constructed_upper_bound':d+1,
          'minimum_normalized_score_margin':str(min_margin),'cap':str(data['cap']),
          'positive_target_perturbation':str(data['perturbation']),
          'default_pr248_discovery_replayed':False})
        total+=1;long_edges+=len(steps);fast_edges+=len(fast['steps'])
    # Changes to H-row scaling leave full-step gains invariant, not generally
    # normalized gains. The target objective is held fixed.
    data=instance(5);A,b,f=data['A'],data['b'],data['objective'];scale=[Q(2**(i%5)) for i in range(len(A))]
    As=[[s*x for x in row] for s,row in zip(scale,A)];bs=[s*x for s,x in zip(scale,b)]
    target=basis_packet(As,bs,data['target']['point']);target['weights']=[w/scale[j] for j,w in zip(data['target']['active'],data['target']['weights'])]
    scaled=construct(As,bs,f,data['start'],target,'full_gain');audit_route(As,bs,f,data['start'],target,scaled)
    orig=fixtures[5]['full_gain']
    require([s['to'] for s in scaled['steps']]==[s['to'] for s in orig['steps']],'row-scale invariance failed')
    rejected=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,KeyError,TypeError,IndexError):rejected.append(name)
        else:raise AssertionError('accepted forged data: '+name)
    good=fixtures[4];A,b,f=good['input']['A'],good['input']['b'],good['input']['objective'];target=good['input']['target']
    for name,mutation in [
      ('false_inverse',lambda s:s['basis']['directions'][0].__setitem__(0,Q(999))),
      ('wrong_selected_ray',lambda s:s.update(selected=(s['selected']+1)%4)),
      ('interior_step',lambda s:s.update(length=s['length']/2)),
      ('wrong_blocker',lambda s:s.update(blocker=0)),
      ('nonedge_endpoint',lambda s:s['to'].__setitem__(0,s['to'][0]+1)),
      ('omitted_active_row',lambda s:s['basis']['active'].pop()),
      ('floating_step',lambda s:s.update(length=float(s['length']))),
      ('boolean_blocker',lambda s:s.update(blocker=False)),
    ]:
        bad=deepcopy(good['normalized']['steps'][0]);mutation(bad)
        reject(name,lambda bad=bad:audit_step(A,b,f,bad,'normalized'))
    fake=deepcopy(target);fake['weights'][0]=0;reject('non_strict_target',lambda:audit_target(A,b,f,fake))
    fake=deepcopy(good['normalized']);fake['steps'].pop();reject('unfinished_route',lambda:audit_route(A,b,f,[0]*4,target,fake))
    reject('normalized_step_claimed_full_gain',lambda:audit_step(A,b,f,good['normalized']['steps'][0],'full_gain'))
    reject('exceeded_route_cap',lambda:construct(A,b,f,[0]*4,target,'normalized',2))
    large=[]
    for d in (16,32,64):
        data=instance(d);A,b,f=data['A'],data['b'],data['objective'];N=data['gray_index']
        for t in (0,1,N-1,N):
            s=make_step(A,b,f,old_basis(A,b,gray_bits(t,d)),'normalized');audit_step(A,b,f,s,'normalized')
        large.append({'dimension':d,'original_facets':2*d+1,'individual_steps_checked':4,
          'all_dimension_formula_not_full_enumeration':N+1,'short_constructed_bound':d+1})
    (ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True)
    for d,c in fixtures.items():
        (ROOT/f'fixtures/capped_klee_minty_{d}.json').write_text(json.dumps(serial(c),indent=2)+'\n')
        (ROOT/f'fixtures/capped_klee_minty_{d}_input.json').write_text(json.dumps(serial(c['input']),indent=2)+'\n')
    report={'status':'PASS','scope':'Exact research evidence; no Lean compilation or new Prove2Me verdict.',
      'primary_classical_references':['https://arxiv.org/abs/1404.0605','https://arxiv.org/html/1910.10097'],
      'fully_executed_dimensions':total,'normalized_edges_checked':long_edges,'full_gain_edges_checked':fast_edges,
      'genuine_facet_anchors':facet_checks,'normalized_route_length_formula':'floor(2^(d+1)/3)+1',
      'same_problem_shortest_full_gain_instances':results,'independent_graphs':reference,
      'scaled_full_gain_route_unchanged':True,'search_disabled_audit':'PASS',
      'large_partial_checks':large,'negative_controls':rejected,'negative_count':len(rejected),
      'seconds':round(time.monotonic()-started,3),
      'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (ROOT/'scripts/simple_tangent_policy_audit.py', ROOT/'scripts/test_normalized_gain_barrier.py')}}
    (ROOT/'research/NORMALIZED_GAIN_BARRIER_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--max-dimension',type=int,default=12);a=p.parse_args();main(a.max_dimension)
