#!/usr/bin/env python3
"""Exact independent phase-routing tests, not a polynomial-length or Lean claim.
Reference graphs exist only in this test harness, never in selector inputs.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random,time,argparse
import sympy as sp
import simple_tangent_policy_audit as simple
import target_slack_pivot as previous
import image_tangent_pivot as original
import target_phase_pivot as new
from test_normalized_gain_barrier import instance, facet_witnesses
ROOT=Path(__file__).resolve().parents[1]
POLICIES=('facet_first1','facet_first2','reset_gain','reset_slack')
def dump(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(simple.serial(data),indent=2,sort_keys=True)+'\n')
def run(A,b,u,v,name):
    policy='facet_first' if name.startswith('facet_first') else name
    c=new.construct(A,b,u,v,policy,lookahead=2 if name=='facet_first2' else 1)
    return c,new.verify(A,b,u,v,c)

def identity(n):return tuple(tuple(Q(i==j) for j in range(n)) for i in range(n))

def moment(d,n):
    V=[tuple(Q(i)**j for j in range(1,d+1)) for i in range(n)]
    mean=[sum(v[j] for v in V)/n for j in range(d)]
    return [[v[j]-mean[j] for j in range(d)] for v in V],[Q(1)]*n

def clipped_box():
    A=[[Q(s)*int(i==j) for j in range(3)] for i in range(3) for s in (-1,1)]
    return A+[[Q(1),Q(1),Q(1)],[Q(-1),Q(2),Q(1)],[Q(2),Q(-1),Q(1)]],\
        [Q(1)]*6+[Q(17,10),Q(21,10),Q(23,10)]

def reference_graph(A,b):
    n=len(A[0]);V={};subsets=0
    for J in combinations(range(len(A)),n):
        T=sp.Matrix([A[j] for j in J]);subsets+=1
        if T.det()==0:continue
        x=tuple(Q(str(z)) for z in T.inv()*sp.Matrix([b[j] for j in J]))
        if simple.feasible(A,b,x):V[x]=set(simple.active_rows(A,b,x))
    simple.require(all(len(J)==n for J in V.values()),'reference is not simple')
    adjacency={x:[] for x in V}
    for x,y in combinations(V,2):
        common=V[x]&V[y]
        if len(common)==n-1:
            simple.require(sp.Matrix([A[j] for j in common]).rank()==n-1,'false independent edge rank')
            adjacency[x].append(y);adjacency[y].append(x)
    simple.require(all(len(row)==n for row in adjacency.values()),'incorrect bounded simple graph degree')
    # Every original inequality is a genuine facet, not a redundant row count.
    facet_anchors=[]
    for j in range(len(A)):
        incident=[x for x,J in V.items() if j in J]
        simple.require(len(incident)>=n,'row lacks a facet')
        anchor=tuple(sum(x[k] for x in incident)/len(incident) for k in range(n))
        simple.require(simple.active_rows(A,b,anchor)==[j],'facet relative-interior check failed')
        simple.require(sp.Matrix([[x[k]-incident[0][k] for k in range(n)] for x in incident[1:]]).rank()==n-1,'facet rank failed')
        facet_anchors.append(anchor)
    # Independent exact finite LP certificates of coordinate boundedness.
    G=identity(n);bounds=original.compact_image(tuple(map(tuple,A)),tuple(b),G,next(iter(V)),20000)
    original.verify_compact(tuple(map(tuple,A)),tuple(b),G,bounds)
    return V,adjacency,{'vertices':len(V),'edges':sum(map(len,adjacency.values()))//2,
        'original_facets':len(A),'active_subsets':subsets,'facet_anchors':facet_anchors,'coordinate_bounds':bounds}

def distances(adjacency,u):
    D={u:0};queue=deque([u])
    while queue:
        x=queue.popleft()
        for y in adjacency[x]:
            if y not in D:D[y]=D[x]+1;queue.append(y)
    simple.require(len(D)==len(adjacency),'disconnected reference graph')
    return D

def first_hit(adj,active,x,target,locked):
    T=active[target];seen={x};todo=deque([(x,0)])
    while todo:
        u,d=todo.popleft()
        if (active[u]&T)-locked:return d
        for v in adj[u]:
            if v not in seen and locked<=active[v]:seen.add(v);todo.append((v,d+1))
    raise AssertionError('no target boundary')

def affine(A,b,u,v,seed):
    rng=random.Random(seed);n=len(u);M=sp.eye(n)
    for i in range(n):
        M[i,i]=(-1 if (i+seed)%2 else 1)*(i+1)
        for j in range(i+1,n):M[i,j]=sp.Rational(rng.randrange(-3,4),rng.randrange(1,4))
    inv=M.inv();shift=[Q(rng.randrange(-3,4),2) for _ in range(n)]
    AA=[[sum(Q(str(inv[k,j]))*row[k] for k in range(n)) for j in range(n)] for row in A]
    bb=[b[i]+simple.dot(row,shift) for i,row in enumerate(AA)]
    def image(x):return [sum(Q(str(M[i,j]))*x[j] for j in range(n))+shift[i] for i in range(n)]
    return AA,bb,image(u),image(v),image

def parabolic(N,h=0):
    ts=[Q(j,h+1) for j in range(h+2)]+[Q(1)+Q(3*j,2*N) for j in range(1,N+1)]+[Q(3)]
    A=[[x+y,-Q(1)] for x,y in zip(ts,ts[1:])]+[[-Q(3),Q(1)]]
    b=[x*y for x,y in zip(ts,ts[1:])]+[Q(0)];points=[[t,t*t] for t in ts]
    for j in range(len(A)):
        a,c=points[j],points[(j+1)%len(points)];mid=[(x+y)/2 for x,y in zip(a,c)]
        simple.require(simple.active_rows(A,b,mid)==[j] and simple.feasible(A,b,mid),'false parabolic facet')
    simple.require(not set(simple.active_rows(A,b,[1,1]))&set(simple.active_rows(A,b,[3,9])),'common facet control')
    return A,b,[Q(1),Q(1)],[Q(3),Q(9)],points

def graphs():
    start=time.monotonic();rng=random.Random(250251);samples=[];failures=[];pairdata=[];rows=[];excluded=[]
    first_checks=affine_checks=scale_checks=old_losses=0
    families=[('moment_2_5',*moment(2,5)),('moment_2_7',*moment(2,7)),('moment_3_6',*moment(3,6)),
      ('moment_3_8',*moment(3,8)),('moment_4_7',*moment(4,7)),('clipped_cube_3',*clipped_box())]
    initial={x[0] for x in families}
    families += [('holdout_moment_2_11',*moment(2,11)),('holdout_moment_3_10',*moment(3,10)),
      ('holdout_moment_4_9',*moment(4,9)),('holdout_moment_5_9',*moment(5,9))]
    for trial in range(3):
        A=[[Q(t)*int(i==j) for j in range(3)] for i in range(3) for t in (-1,1)]
        extra=[[Q(rng.randrange(-4,5)) for _ in range(3)] for k in range(3)]
        extra=[r if any(r) else [Q(1),Q(1),Q(1)] for r in extra]
        families.append((f'holdout_cut_cube_{trial}',A+extra,[Q(1)]*6+[sum(abs(z) for z in r)-Q(1,3) for r in extra]))
    for name,A,b in families:
        try:V,adj,meta=reference_graph(A,b)
        except ValueError as e:
            simple.require(name=='holdout_cut_cube_1' and 'not simple'in str(e),'unexpected graph failure')
            excluded.append({'model':name,'reason':str(e),'scope':'Unsupported nonsimple case, not a negative geometric verdict.'});continue
        pairs=[(u,v) for u in V for v in V if u!=v]
        if name not in initial:rng.shuffle(pairs);pairs=pairs[:100]
        dcache={};tcache={};tot={p:0 for p in POLICIES};bad={p:0 for p in POLICIES};maxphase={p:0 for p in POLICIES}
        cand={p:0 for p in POLICIES};look={p:0 for p in POLICIES};negative={p:0 for p in POLICIES};oldsum=oldbad=shortsum=0
        comparison={'shorter':0,'equal':0,'longer':0}
        for pi,(u,v) in enumerate(pairs):
            if u not in dcache:dcache[u]=distances(adj,u)
            dist=dcache[u][v];shortsum+=dist
            if v not in tcache:
                raw=original.discover_vertex(tuple(map(tuple,A)),tuple(b),identity(len(u)),v)
                original.verify_vertex(tuple(map(tuple,A)),tuple(b),identity(len(u)),v,raw)
                f=list(map(Q,raw['normal']));tc=simple.basis_packet(A,b,list(v));tc['weights']=list(map(Q,raw['weights']))
                simple.audit_target(A,b,f,tc);tcache[v]=(f,tc)
            f,tc=tcache[v];old=previous.construct(A,b,f,u,tc);previous.verify(A,b,f,u,tc,old)
            oldlen=len(old['steps']);oldsum+=oldlen;oldbad+=oldlen>dist;lengths={}
            for policy in POLICIES:
                c,r=run(A,b,u,v,policy);lengths[policy]=r['edges'];tot[policy]+=r['edges'];bad[policy]+=r['edges']>dist
                cand[policy]+=r['incident_candidates_audited'];look[policy]+=r['lookahead_candidates_audited']
                maxphase[policy]=max(maxphase[policy],r['max_constant_face_edges'])
                negative[policy]+=sum(p['old_phase_decreasing_edges'] for p in r['phases'])
                x=u
                for y in r['path'][1:]:y=tuple(y);simple.require(y in adj[x],'nonedge in reference');x=y
                if policy=='facet_first2':
                    for phase in c['phases']:
                        for block in phase['blocks']:
                            x=tuple(block['basis']['point']);distance=first_hit(adj,V,x,v,V[x]&V[v])
                            seq,rep=new.audit_block(A,b,phase['objective'],c['target_basis'],block,c['policy'],c['lookahead'])
                            simple.require(rep['ends_phase']==(distance<=2),'false local boundary verdict')
                            if distance<=2:simple.require(len(seq)==distance,'not shortest local first-hit block')
                            first_checks+=1
                    old_losses+=sum(simple.dot(f,y)<simple.dot(f,x) for x,y in zip(r['path'],r['path'][1:]))
                    if pi in (0,7):
                        samples.append((A,b,u,v,c));AA,bb,uu,vv,image=affine(A,b,u,v,pi+17)
                        _,rr=run(AA,bb,uu,vv,policy);simple.require(rr['path']==[image(x) for x in r['path']],'affine equivariance');affine_checks+=1
                        ss=[Q(2)**((j*3+pi)%11-5) for j in range(len(A))];AA=[[s*x for x in row] for s,row in zip(ss,A)];bb=[s*x for s,x in zip(ss,b)]
                        _,rr=run(AA,bb,u,v,policy);simple.require(rr['path']==r['path'],'row scale equivariance');scale_checks+=1
                    if r['edges']>dist and not any(w['family']==name for w in failures):
                        failures.append({'family':name,'input':{'A':A,'b':b,'start':u,'target':v},'distance':dist,
                            'previous_target_slack_edges':oldlen,'certificate':c,'verified':r})
            comparison['shorter' if lengths['facet_first2']<oldlen else 'longer' if lengths['facet_first2']>oldlen else 'equal']+=1
            pairdata.append({'family':name,'u':u,'v':v,'distance':dist,'previous_target_slack':oldlen,**lengths})
        row={'family':name,'suite':'original' if name in initial else 'additional','pairs':len(pairs),
          'dimension':len(A[0]),'facets':len(A),'vertices':len(V),'edges':sum(map(len,adj.values()))//2,
          'shortest_total':shortsum,'totals':tot,'nonshortest':bad,'max_constant_face_edges':maxphase,
          'incident_candidates':cand,'lookahead_candidates':look,'old_phase_decreasing_edges':negative,
          'previous_target_slack_total':oldsum,'previous_target_slack_nonshortest':oldbad,'pairwise_vs_previous':comparison}
        print(json.dumps(row),flush=True);rows.append(row)
    oldfun=(new.basis_packet,simple.invert,original.ExactLP.maximize,original.discover_vertex)
    def no(*args,**kwargs):raise AssertionError('auditor called discovery')
    new.basis_packet=simple.invert=original.ExactLP.maximize=original.discover_vertex=no
    try:
        for A,b,u,v,c in samples:new.verify(A,b,u,v,new.decode_certificate(json.loads(json.dumps(simple.serial(c)))))
    finally:new.basis_packet,simple.invert,original.ExactLP.maximize,original.discover_vertex=oldfun
    negatives=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):negatives.append(name)
        else:raise AssertionError('invalid certificate passed '+name)
    A,b,u,v,c=next(a for a in samples if any(bl['lookahead_bases'] for p in a[4]['phases'] for bl in p['blocks']))
    controls=[('changed_input',lambda z:z.update(problem_sha256='0'*64)),('missing_phase',lambda z:z['phases'].pop()),
      ('changed_objective',lambda z:z['phases'][0]['objective'].__setitem__(0,Q(123))),('boolean_depth',lambda z:z.update(lookahead=True)),
      ('false_locked_face',lambda z:z['phases'][0].update(locked=[999])),
      ('false_inverse',lambda z:z['phases'][0]['blocks'][0]['basis']['directions'][0].__setitem__(0,Q(123))),
      ('floating_anchor',lambda z:z['phases'][0]['blocks'][0]['basis']['point'].__setitem__(0,0.0)),
      ('false_selected_block',lambda z:z['phases'][0]['blocks'][0].update(selected_block=[True]))]
    for name,mut in controls:
        bad=deepcopy(c);mut(bad);reject(name,lambda bad=bad:new.verify(A,b,u,v,bad))
    bad=deepcopy(c);bl=next(bl for p in bad['phases'] for bl in p['blocks'] if bl['lookahead_bases']);bl['lookahead_bases'].pop()
    reject('missing_lookahead_branch',lambda:new.verify(A,b,u,v,bad))
    bad=deepcopy(c);bl=next(bl for p in bad['phases'] for bl in p['blocks'] if bl['lookahead_bases']);bl['lookahead_bases'][0]['first']=True
    reject('boolean_branch_index',lambda:new.verify(A,b,u,v,bad))
    reject('route_cap',lambda:new.construct(A,b,u,v,edge_cap=0));reject('unsupported_depth',lambda:new.construct(A,b,u,v,lookahead=3))
    bad=deepcopy(c)
    if len(bad['phases'])>1:
        bad['phases'][0]['blocks']+=bad['phases'][1]['blocks'];bad['phases'].pop(1)
        reject('ignore_first_acquisition',lambda:new.verify(A,b,u,v,bad))
    reject('unbounded_neighbor',lambda:new.construct([[-Q(1),0],[0,-Q(1)],[Q(1),-Q(1)],[-Q(1),Q(1)]],[0,0,1,1],[1,0],[0,1]))
    A0=[[-Q(1),0],[0,-Q(1)],[Q(1),0],[0,Q(1)]];b0=[0,0,1,1]
    c0=new.construct(A0,b0,[0,0],[0,0]);simple.require(new.verify(A0,b0,[0,0],[0,0],c0)['edges']==0,'stationary case')
    report={'status':'PASS','scope':'Exact research tests, not Lean verification.','families':rows,'excluded':excluded,
      'first_hit_radius_checks':first_checks,'affine_checks':affine_checks,'positive_row_scale_checks':scale_checks,
      'decreases_of_previous_fixed_objective':old_losses,'search_disabled_audits':len(samples),'negative_controls':negatives,'seconds':time.monotonic()-start}
    for suite in ('original','additional'):
        rs=[r for r in rows if r['suite']==suite]
        report[suite]={'pairs':sum(r['pairs'] for r in rs),'shortest_sum':sum(r['shortest_total'] for r in rs),
          'totals':{p:sum(r['totals'][p] for r in rs) for p in POLICIES},'nonshortest':{p:sum(r['nonshortest'][p] for r in rs) for p in POLICIES},
          'previous_target_slack_total':sum(r['previous_target_slack_total'] for r in rs),'previous_target_slack_nonshortest':sum(r['previous_target_slack_nonshortest'] for r in rs),
          'pairwise_vs_previous':{k:sum(r['pairwise_vs_previous'][k] for r in rs) for k in ('shorter','equal','longer')}}
    dump(ROOT/'research/TARGET_PHASE_GRAPH_TESTS.json',report);dump(ROOT/'fixtures/target_phase_nonshortest.json',failures)
    dump(ROOT/'fixtures/target_phase_all_pairs.json',pairdata)
    for i,(A,b,u,v,c) in enumerate(samples[:4]):dump(ROOT/f'fixtures/target_phase_sample_{i}.json',{'input':{'A':A,'b':b,'start':u,'target':v},'certificate':c})
    return report

def family_tests():
    start=time.monotonic();examples=[];barriers=[];caps=[];products=[]
    for N in (2,4,8,16,32,64):
        A,b,u,v,points=parabolic(N,0);entries={}
        for pol in POLICIES:
            c,r=run(A,b,u,v,pol);entries[pol]={'edges':r['edges'],'max_constant_face_edges':r['max_constant_face_edges'],
               'phase_decreasing_edges':sum(p['old_phase_decreasing_edges'] for p in r['phases'])}
            if pol.startswith('facet_first'):
                simple.require(r['edges']==2 and entries[pol]['phase_decreasing_edges']==1,'negative-gain acquisition escape')
                simple.require(c['phases'][0]['objective']==[Q(1,3),Q(1,6)],'phase objective formula')
            else:simple.require(r['edges']==N+1,'monotone long phase')
            if N==8 and pol=='facet_first2':dump(ROOT/'fixtures/target_phase_negative_gain_escape.json',{'input':{'A':A,'b':b,'start':u,'target':v},'certificate':c,'verified':r})
        examples.append({'N':N,'facets':len(A),'distance':2,'policies':entries})
    for depth in (1,2):
        for N in (4,8,16,32,64):
            A,b,u,v,points=parabolic(N,depth);c,r=run(A,b,u,v,'facet_first2' if depth==2 else 'facet_first1')
            simple.require(r['edges']==N+1 and r['max_constant_face_edges']==N-1,'finite horizon formula')
            barriers.append({'lookahead':depth,'N':N,'dimension':2,'facets':len(A),'route_edges':r['edges'],
              'shortest_distance':min(N+1,depth+2),'first_phase_edges':r['phases'][0]['edges']})
            if N==16:dump(ROOT/f'fixtures/target_phase_horizon_{depth}.json',{'input':{'A':A,'b':b,'start':u,'target':v},'certificate':c,'verified':r,'shortest_distance':depth+2})
    for d in range(2,13):
        q=instance(d);facet_witnesses(q);A,b,u,v=q['A'],q['b'],q['start'],q['target']['point'];row={'dimension':d,'facets':len(A)}
        for pol in POLICIES:
            c,r=run(A,b,u,v,pol);simple.require(r['edges']==d,'capped shortest observation');row[pol]=r['edges']
        caps.append(row)
    for copies in (1,2,4,8):
        aa,bb,uu,vv,_=parabolic(4,0);n=2*copies;A=[];b=[]
        for j in range(copies):
            for row,rhs in zip(aa,bb):A.append([Q(0)]*(2*j)+row+[Q(0)]*(n-2*j-2));b.append(rhs)
        u=uu*copies;v=vv*copies;c,r=run(A,b,u,v,'facet_first2');simple.require(r['edges']==n and len(r['phases'])==n,'product facet-drop optimality')
        products.append({'dimension':n,'facets':len(A),'route_edges':r['edges'],'lower_bound':n,'full_graph_enumerated':False,
          'candidate_checks':r['incident_candidates_audited']+r['lookahead_candidates_audited']})
    report={'status':'PASS','scope':'Exact tests plus separate written family proofs, not Lean.',
      'negative_gain_escapes':examples,'finite_lookahead_barriers':barriers,'capped_tests':caps,'product_tests':products,'seconds':time.monotonic()-start}
    dump(ROOT/'research/TARGET_PHASE_FAMILY_TESTS.json',report);return report

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--part',choices=['all','graphs','families'],default='all');args=p.parse_args()
    if args.part in ('all','graphs'):graphs()
    if args.part in ('all','families'):family_tests()
    files=['target_phase_pivot.py','test_target_phase_pivot.py','target_slack_pivot.py','simple_tangent_policy_audit.py',
      'test_normalized_gain_barrier.py','image_tangent_pivot.py','exact_farkas_lp.py']
    dump(ROOT/'research/TARGET_PHASE_SOURCE_HASHES.json',{f:hashlib.sha256((ROOT/'scripts'/f).read_bytes()).hexdigest() for f in files})
    print('PASS '+args.part,flush=True)
if __name__=='__main__':main()
