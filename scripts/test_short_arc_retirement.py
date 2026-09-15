#!/usr/bin/env python3
"""Exact same-anchor shortening and all-proper-face visibility tests.

Reference vertex graphs are reconstructed only in this TEST harness. The route
producer consumes A,b,start,target and calls unchanged #253 face discovery.
Written family/bound arguments are not Lean verification or a Hirsch proof.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from collections import deque
from copy import deepcopy
from pathlib import Path
import argparse,hashlib,json,random,time
import sympy as sp
import short_arc_retirement as new
import two_face_acquisition as old

base=old.base;require=base.require;dot=base.dot;serial=base.serial
ROOT=Path(__file__).resolve().parents[1]


def dump(name,data):
    path=ROOT/name;path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(serial(data),indent=2,sort_keys=True)+'\n')


def hidden_target(d):
    require(type(d)is int and d>=2,'family needs dimension at least two')
    alpha=[Q(1,2)+Q(i+1,10*d*d) for i in range(d)];c=[d+a for a in alpha]
    A=[[Q(s)*int(i==j) for j in range(d)] for i in range(d) for s in (-1,1)]
    b=[Q(k%2) for k in range(2*d)]
    A += [[Q(1+int(i==j)) for j in range(d)] for i in range(d)];b+=c
    total=sum(c)/Q(d+1);v=[ci-total for ci in c];u=[Q(0)]*d
    require(all(0<vi<1 for vi in v),'target outside old cube interior')
    anchors=[]
    for j in range(2*d):
        x=[Q(1,10*d)]*d;x[j//2]=Q(j%2)
        require(base.feasible(A,b,x) and base.active_rows(A,b,x)==[j],'old row not a genuine facet')
        anchors.append(x)
    eta=Q(1,100*d*d)
    for i in range(d):
        x=[v[j]-eta*(Q(j!=i)-Q(d-1,d+1)) for j in range(d)]
        require(base.feasible(A,b,x) and base.active_rows(A,b,x)==[2*d+i],'new row not a genuine facet')
        anchors.append(x)
    require(all(ci>d for ci in c),'proper-face strict separation lost')
    # For every xi=0, every new row has maximum at most d on that cube face.
    for zero in range(d):
        for row,rhs in zip(A[2*d:],c):
            bound=sum(row[j] for j in range(d) if j!=zero)
            require(bound<rhs,'target facet meets an initial coordinate facet')
    return A,b,u,v,anchors


def hidden_path(A,b,u,v):
    d=len(u);x=u;path=[u]
    releases=[2*j for j in range(1,d)]+[0]+[2*j+1 for j in range(1,d)]
    for row in releases:
        bs=base.basis_packet(A,b,x);choices=old.neighbors(A,b,bs,[])
        selected=next(o for o in choices if o['released']==row)
        x=selected['to'];path.append(x)
    require(x==v and len(path)-1==2*d-1,'explicit all-dimensional route failed')
    target_rows=set(base.active_rows(A,b,v))
    first=next(j for j,x in enumerate(path) if set(base.active_rows(A,b,x))&target_rows)
    require(first==d,'wrong first target acquisition')
    return path


def clipped_prism(N,h):
    """Only the old top target vertex is removed by three local cuts."""
    require(type(N)is int and type(h)is int and N>=8 and 1<=h<=N-2,'family parameters')
    ts=[Q(j,h+1) for j in range(h+2)]+[Q(1)+Q(3*j,2*N) for j in range(1,N+1)]+[Q(3)]
    A=[[a+b,-Q(1),Q(0)] for a,b in zip(ts,ts[1:])]+[[-Q(3),Q(1),Q(0)],
        [Q(0),Q(0),-Q(1)],[Q(0),Q(0),Q(1)]]
    b=[a*b for a,b in zip(ts,ts[1:])]+[Q(0),Q(0),Q(1)]
    u=[Q(1),Q(1),Q(0)];old_target=[Q(3),Q(9),Q(1)]
    T=base.active_rows(A,b,old_target)
    gaps=[b[j]-dot(A[j],u) for j in T]
    rows=[[x/gap for x in A[j]] for j,gap in zip(T,gaps)]
    D=[[sum(row[k] for row in rows)+rows[i][k] for k in range(3)] for i in range(3)]
    eps=[Q(1,100)+Q(i,10000) for i in range(3)]
    rhs=[dot(row,old_target)-e for row,e in zip(D,eps)]
    v=[Q(str(t)) for t in sp.Matrix(D).inv()*sp.Matrix(rhs)]
    for z in (0,1):
        for t in ts:
            x=[t,t*t,Q(z)]
            if x!=old_target:
                require(all(dot(row,x)<bound for row,bound in zip(D,rhs)), 'a non-target old vertex was cut')
    AA,bb=A+D,b+rhs
    require(base.active_rows(AA,bb,v)==list(range(len(A),len(A)+3)),'target not the three-cut vertex')
    target=base.basis_packet(AA,bb,v);phase,_=old.phase_objective(AA,bb,u,target)
    require(phase[0]>0 and phase[1]>0,'phase objective not increasing along parabola')
    # Old rows remain genuine: their face average excluding the deleted tip
    # has positive slack on every other old row and every new row.
    vertices=[[t,t*t,Q(z)] for z in (0,1) for t in ts]
    for i,row in enumerate(A):
        incidence=[x for x in vertices if dot(row,x)==b[i] and x!=old_target]
        x=[sum(p[k] for p in incidence)/len(incidence) for k in range(3)]
        require(base.feasible(AA,bb,x) and base.active_rows(AA,bb,x)==[i],'original prism row lost its facet')
    # New facet anchors near the new vertex, solving selected cut = rhs,
    # every other new row = rhs-small, and staying inside the original prism.
    inverse=sp.Matrix(D).inv()
    for i in range(3):
        r=[rhs[j]-(Q(0) if j==i else Q(1,10**7)) for j in range(3)]
        x=[Q(str(z)) for z in inverse*sp.Matrix(r)]
        require(base.feasible(AA,bb,x) and base.active_rows(AA,bb,x)==[len(A)+i], 'new cut not a facet')
    return AA,bb,u,v,{'old_target':old_target,'old_vertices':vertices,'local_cut_thresholds':eps}


def graph(A,b):
    """Independent exact all-active-subset enumeration; never given to router."""
    d=len(A[0]);V={};subsets=0
    for ids in combinations(range(len(A)),d):
        M=sp.Matrix([A[i] for i in ids]);subsets+=1
        if M.det()==0:continue
        x=tuple(Q(str(z)) for z in M.inv()*sp.Matrix([b[i] for i in ids]))
        if base.feasible(A,b,x):V[x]=set(base.active_rows(A,b,x))
    require(V and all(len(I)==d for I in V.values()),'unsupported non-simple reference')
    adj={x:[] for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    require(all(len(a)==d for a in adj.values()),'reference graph degree')
    return V,adj,subsets


def distances(adj,u):
    D={u:0};q=deque([u])
    while q:
        x=q.popleft()
        for y in adj[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    require(len(D)==len(adj),'reference disconnected')
    return D


def moment(d,n):
    V=[[Q(i)**j for j in range(1,d+1)] for i in range(n)]
    mean=[sum(v[j] for v in V)/n for j in range(d)]
    return [[v[j]-mean[j] for j in range(d)] for v in V],[Q(1)]*n


def affine(A,b,u,v,seed):
    rng=random.Random(seed);d=len(u);M=sp.eye(d)
    for i in range(d):
        M[i,i]=(-1 if (seed+i)%2 else 1)*(i+1)
        for j in range(i+1,d):M[i,j]=sp.Rational(rng.randrange(-3,4),rng.randrange(1,4))
    inv=M.inv();t=[Q(rng.randrange(-3,4),2) for _ in range(d)]
    AA=[[sum(Q(str(inv[k,j]))*row[k] for k in range(d)) for j in range(d)] for row in A]
    bb=[rhs+dot(row,t) for rhs,row in zip(b,AA)]
    def transform(x):return [sum(Q(str(M[i,j]))*x[j] for j in range(d))+t[i] for i in range(d)]
    return AA,bb,transform(u),transform(v),transform


def family_tests():
    start=time.monotonic();prisms=[];hidden=[];fixtures=[];reference_counts=[]
    for N,h in ((8,1),(8,2),(16,2),(32,2),(64,2),(32,8),(64,8),(64,16)):
        A,b,u,v,info=clipped_prism(N,h)
        out=new.construct(A,b,u,v);r=out['verified'];ref=out['certificate']['reference']
        require(r['reference_committed_edges']==N+4 and r['committed_edges']==h+5,'prism route formula')
        require(r['fallback_decisions']==1 and r['backward_fallback_edges']==h+1,'prism fallback classification')
        require(r['same_decision_endpoints'] and r['saved_raw_edges']==N-h-1,'prism endpoint preservation')
        require(not any(set(base.active_rows(A,b,bs['point']))&set(ref['target_basis']['active'])
            for face in ref['phases'][0]['decisions'][0]['faces'] for bs in face['corners']), 'early face acquisition')
        if N==8:
            V,adj,num=graph(A,b);dist=distances(adj,tuple(u))[tuple(v)]
            require(dist==h+5,'independent prism distance mismatch')
            for x,y in zip(r['path'],r['path'][1:]):require(tuple(y)in adj[tuple(x)],'projected chord in original path')
            reference_counts.append({'family':'prism','N':N,'h':h,'vertices':len(V),'edges':sum(map(len,adj.values()))//2,'subsets':num,'distance':dist})
        prisms.append({'N':N,'hidden_backward_vertices':h,'dimension':3,'original_facets':len(A),
            'reference_edges':r['reference_committed_edges'],'shortened_edges':r['committed_edges'],
            'shortest_from_written_family_proof':h+5,'saved_edges':r['saved_raw_edges'],
            'backward_fallback_edges':r['backward_fallback_edges'],'audited_face_edges':r['audited_face_edge_occurrences'],
            'same_anchors':r['same_decision_endpoints'],'old_bound':r['reference_facet_subset_bound'],
            'new_bound':r['improved_facet_subset_bound']})
        if (N,h)==(16,2):fixtures.append(('short_arc_prism.json',{'input':{'A':A,'b':b,'start':u,'target':v},**out}))
    for d in (2,3,4,5,6,8,12,24,48):
        A,b,u,v,anchors=hidden_target(d);path=hidden_path(A,b,u,v)
        decisions=None;retired=None
        if d<=6:
            out=new.construct(A,b,u,v);r=out['verified']
            require(r['committed_edges']==2*d-1,'tested hidden family selector is not shortest')
            decisions=r['fallback_decisions'];retired=r['retired_improving_faces']
            require(r['phase_edges'][0]==d and r['phase_fallback_bounds'][0]['fallback_decisions']==(d-1)//2, 'hidden first-phase formula')
            first=out['certificate']['reference']['phases'][0]['decisions'][0]
            if d>=3:
                require(all(not(set(base.active_rows(A,b,bs['point']))&set(range(2*d,3*d)))
                    for face in first['faces'] for bs in face['corners']), 'target visible in a proper initial two-face')
            if d==4:fixtures.append(('hidden_target_4.json',{'input':{'A':A,'b':b,'start':u,'target':v},'facet_anchors':anchors,**out}))
        if d<=4:
            V,adj,num=graph(A,b);D=distances(adj,tuple(u));require(D[tuple(v)]==2*d-1,'hidden shortest lower bound disagrees')
            first=min(D[x] for x in V if V[x]&set(range(2*d,3*d)));require(first==d,'hidden first acquisition mismatch')
            reference_counts.append({'family':'hidden_target','dimension':d,'vertices':len(V),'edges':sum(map(len,adj.values()))//2,'subsets':num,'distance':D[tuple(v)],'first_target_distance':first})
        hidden.append({'dimension':d,'original_facets':len(A),'genuine_facet_anchors_checked':len(anchors),
          'explicit_original_edges_checked':len(path)-1,'exact_distance_from_written_proof':2*d-1,
          'first_target_distance_from_written_proof':d,'source_proper_face_separation_identities':d*d,
          'router_fallback_decisions':decisions,'router_retired_faces':retired,'full_graph_enumerated':d<=4,
          'full_selector_run':d<=6,'all_initial_proper_faces_enumerated':False})
    for name,data in fixtures:dump('fixtures/'+name,data)
    report={'status':'PASS','scope':'Exact rational tests and written family formulas, not Lean or platform acceptance.',
            'clipped_prisms':prisms,'hidden_target_family':hidden,'independent_graphs':reference_counts,
            'source_sha256':hashes(),'seconds':round(time.monotonic()-start,3)}
    dump('research/SHORT_ARC_FAMILY_TESTS.json',report);print(json.dumps(report),flush=True)
    return fixtures


def graph_tests():
    start=time.monotonic();rng=random.Random(253254)
    A=[[Q(s)*int(i==j) for j in range(3)] for i in range(3) for s in (-1,1)]
    box=(A+[[Q(1),Q(1),Q(1)],[Q(-1),Q(2),Q(1)],[Q(2),Q(-1),Q(1)]],[Q(1)]*6+[Q(17,10),Q(21,10),Q(23,10)])
    families=[('moment_2_5',*moment(2,5)),('moment_2_7',*moment(2,7)),('moment_3_6',*moment(3,6)),
      ('moment_3_8',*moment(3,8)),('moment_4_7',*moment(4,7)),('clipped_cube',*box)]
    extraA,extrab,_,_,_=clipped_prism(8,2)
    families += [('cut_prism',extraA,extrab),('moment_4_9',*moment(4,9)),('hidden_4',*hidden_target(4)[:2])]
    rows=[];pairdata=[];saved_cases=[];audits=[];affine_count=scale_count=0
    for fi,(name,A,b) in enumerate(families):
        V,adj,num=graph(A,b);pairs=[(x,y) for x in V for y in V if x!=y]
        if fi>=6:rng.shuffle(pairs);pairs=pairs[:60]
        totalold=totalnew=totaldist=badold=badnew=saved=fallbacks=backward=0;improved=0;D={}
        for pi,(u,v) in enumerate(pairs):
            if u not in D:D[u]=distances(adj,u)
            dist=D[u][v];out=new.construct(A,b,u,v);r=out['verified'];c=out['certificate']
            require(r['committed_edges']<=r['reference_committed_edges'],'raw route became longer')
            for x,y in zip(r['path'],r['path'][1:]):require(tuple(y)in adj[tuple(x)],'nonedge in independent graph')
            totalold+=r['reference_committed_edges'];totalnew+=r['committed_edges'];totaldist+=dist
            badold+=r['reference_loop_erased_edges']>dist;badnew+=r['loop_erased_edges']>dist
            saved+=r['saved_raw_edges'];fallbacks+=r['fallback_decisions'];backward+=r['backward_fallback_edges'];improved+=r['saved_raw_edges']>0
            pairdata.append({'model':name,'u':u,'v':v,'distance':dist,'old_raw':r['reference_committed_edges'],
               'new_raw':r['committed_edges'],'old_loop_erased':r['reference_loop_erased_edges'],'new_loop_erased':r['loop_erased_edges']})
            if r['saved_raw_edges']>0 and not any(z['model']==name for z in saved_cases):saved_cases.append({'model':name,'input':{'A':A,'b':b,'start':u,'target':v},**out})
            if pi in (0,3):
                audits.append((A,b,u,v,c))
                AA,bb,uu,vv,tr=affine(A,b,u,v,17+pi);rr=new.construct(AA,bb,uu,vv)['verified']
                require(rr['path']==[tr(x) for x in r['path']],'affine route changed');affine_count+=1
                scalars=[Q(2)**((3*j+pi)%9-4) for j in range(len(A))]
                AA=[[s*z for z in row] for s,row in zip(scalars,A)];bb=[s*z for s,z in zip(scalars,b)]
                require(new.construct(AA,bb,u,v)['verified']['path']==r['path'],'row scaling changed route');scale_count+=1
        rows.append({'model':name,'pairs':len(pairs),'dimension':len(A[0]),'facets':len(A),'reference_vertices':len(V),
          'reference_edges':sum(map(len,adj.values()))//2,'old_raw_edges':totalold,'new_raw_edges':totalnew,
          'shortest_total':totaldist,'old_nonshortest':badold,'new_nonshortest':badnew,'saved_raw_edges':saved,
          'improved_pairs':improved,'fallback_decisions':fallbacks,'backward_fallback_edges':backward})
        print(name,rows[-1],flush=True)
    A,b,u,v,_=clipped_prism(16,2);c=new.construct(A,b,u,v)['certificate'];audits.append((A,b,u,v,c))
    bads=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):bads.append(name)
        else:raise AssertionError('accepted corruption: '+name)
    for name,edit in [
      ('wrong_format',lambda z:z.update(format='unverified')),
      ('missing_phase_choices',lambda z:z['choices'].pop()),
      ('missing_decision',lambda z:z['choices'][0].pop()),
      ('changed_shortcut_length',lambda z:z['choices'][0][0].update(count=1)),
      ('boolean_shortcut_orientation',lambda z:z['choices'][0][0].update(sign=True)),
      ('wrong_face',lambda z:z['choices'][0][0].update(fixed_rows=[999])),
      ('missing_reference_face',lambda z:z['reference']['phases'][0]['decisions'][0]['faces'].pop()),
      ('corrupt_reference_inverse',lambda z:z['reference']['phases'][0]['decisions'][0]['basis']['directions'][0].__setitem__(0,Q(99))),
      ('wrong_phase_objective',lambda z:z['reference']['phases'][0]['objective'].__setitem__(0,Q(99))),
      ('forged_anchor',lambda z:z['reference']['phases'][0]['anchor'].__setitem__(0,Q(99)))]:
        z=deepcopy(c);edit(z);reject(name,lambda z=z:new.verify(A,b,u,v,z))
    reject('changed_original_inequality',lambda:new.verify(A,[b[0]+1]+b[1:],u,v,c))
    reject('route_cap',lambda:new.construct(A,b,u,v,edge_cap=1))
    # Disable every discovery route. Pure finite witness validation must still work.
    orig=(old.trace_face,old.produce_decision,old.construct,base.basis_packet,base.invert)
    def no(*args,**kwargs):raise AssertionError('auditor called a discovery/solver function')
    old.trace_face=old.produce_decision=old.construct=base.basis_packet=base.invert=no
    try:
        for A,b,u,v,c in audits:new.verify(A,b,u,v,new.decode(json.loads(json.dumps(serial(c)))))
    finally:old.trace_face,old.produce_decision,old.construct,base.basis_packet,base.invert=orig
    report={'status':'PASS','scope':'Independent small graphs; original #253 unchanged, no Lean verification.',
       'models':rows,'total_pairs':len(pairdata),'affine_route_checks':affine_count,'positive_row_scaling_checks':scale_count,
       'search_disabled_audits':len(audits),'rejected':bads,'source_sha256':hashes(),'seconds':round(time.monotonic()-start,3)}
    dump('research/SHORT_ARC_GRAPH_TESTS.json',report);dump('fixtures/short_arc_pair_comparisons.json',pairdata)
    dump('fixtures/short_arc_improvements.json',saved_cases);print(json.dumps(report),flush=True)


def hashes():
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
       [Path(__file__),ROOT/'scripts/short_arc_retirement.py',ROOT/'scripts/two_face_acquisition.py',ROOT/'scripts/simple_tangent_policy_audit.py']}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--part',choices=['all','graphs','families'],default='all');args=parser.parse_args()
    if args.part in ('all','graphs'):graph_tests()
    if args.part in ('all','families'):family_tests()
