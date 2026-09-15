#!/usr/bin/env python3
"""Independent graph, complete-face and fixed-horizon obstruction comparisons.

Graphs only occur in this test harness. The new and unchanged depth-two
producers receive original A,b and endpoints, never a graph or factor chart.
All counts below describe executed computations, not Lean verification.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import argparse,hashlib,json,random,time
import sympy as sp
import two_face_acquisition as new
import target_phase_pivot as previous
import simple_tangent_policy_audit as base
import target_roof_phase_barrier as roof

ROOT=Path(__file__).resolve().parents[1]
require,dot,serial=base.require,base.dot,base.serial
DEPENDENCIES={'simple_tangent_policy_audit.py':'73dc32b9753d7d0fe5e67ca1f4fad0534b6b1976',
              'target_phase_pivot.py':'4b6be3e8f7fc304c87474205898d85f71e39a15d',
              'target_roof_phase_barrier.py':'87c82480b19b3c699d2c9bcf1919d3bb8ea16058'}


def source_hashes():
    names=['two_face_acquisition.py','test_two_face_acquisition.py']+list(DEPENDENCIES)
    return {f'scripts/{n}':hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in names}


def dump(path,data):
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(serial(data),indent=2,sort_keys=True)+'\n')


def moment(d,n):
    V=[tuple(Q(i)**j for j in range(1,d+1)) for i in range(n)]
    mid=[sum(v[j] for v in V)/n for j in range(d)]
    return [[v[j]-mid[j] for j in range(d)] for v in V],[Q(1)]*n


def models():
    box=[[Q(s)*int(i==j) for j in range(3)] for i in range(3) for s in(-1,1)]
    ts=[Q(j,4) for j in range(5)]+[1+Q(3*j,16) for j in range(1,9)]+[Q(3)]
    pa=[[x+y,-Q(1),Q(0)] for x,y in zip(ts,ts[1:])]+[[-Q(3),Q(1),Q(0)]]
    pb=[x*y for x,y in zip(ts,ts[1:])]+[Q(0)]
    prism=(pa+[[Q(0),Q(0),-Q(1)],[-Q(1,3),Q(0),Q(1)],[-Q(1),-Q(1),-Q(1)]],pb+[Q(0),Q(1),-Q(1,5)])
    return {
      'moment_2_5':moment(2,5),'moment_2_7':moment(2,7),'holdout_moment_2_11':moment(2,11),
      'moment_3_6':moment(3,6),'moment_3_8':moment(3,8),'moment_4_7':moment(4,7),
      'clipped_cube_3':(box+[[Q(1),Q(1),Q(1)],[Q(-1),Q(2),Q(1)],[Q(2),Q(-1),Q(1)]],
              [Q(1)]*6+[Q(17,10),Q(21,10),Q(23,10)]),
      'truncated_octahedron':(box+[list(map(Q,s)) for s in product((-1,1),repeat=3)],[Q(2)]*6+[Q(3)]*8),
      'holdout_clipped_slanted_prism':prism,'holdout_moment_4_9':moment(4,9),'holdout_moment_5_9':moment(5,9)}


def reference(A,b):
    d=len(A[0]);V={}
    for I in combinations(range(len(A)),d):
        M=sp.Matrix([A[i] for i in I])
        if not M.det():continue
        p=tuple(Q(z) for z in M.inv()*sp.Matrix([b[i] for i in I]))
        if base.feasible(A,b,p):V[p]=set(base.active_rows(A,b,p))
    require(V and all(len(I)==d for I in V.values()),'not a simple reference model')
    adj={p:[] for p in V}
    for p,q in combinations(V,2):
        shared=V[p]&V[q]
        if len(shared)==d-1:
            require(sp.Matrix([A[i] for i in shared]).rank()==d-1,'incorrect reference adjacency')
            adj[p].append(q);adj[q].append(p)
    require(all(len(ns)==d for ns in adj.values()),'reference graph is not bounded d-regular')
    anchors=[]
    for i in range(len(A)):
        pts=[p for p,I in V.items() if i in I]
        require(pts,'redundant reference input row')
        x=[sum(p[k] for p in pts)/len(pts) for k in range(d)]
        require(base.active_rows(A,b,x)==[i] and base.feasible(A,b,x),'false genuine facet witness')
        require(sp.Matrix([[p[k]-pts[0][k] for k in range(d)] for p in pts[1:]]).rank()==d-1,
                'reference facet has wrong dimension')
        anchors.append(x)
    return V,adj,anchors


def distances(adj,x,allowed=None):
    D={x:0};todo=deque([x])
    while todo:
        p=todo.popleft()
        for q in adj[p]:
            if (allowed is None or q in allowed) and q not in D:D[q]=D[p]+1;todo.append(q)
    return D


def check_faces(A,b,u,v,c,V,adj):
    faces=decisions=0;T=V[v]
    for phase in c['phases']:
        for dc in phase['decisions']:
            root=tuple(dc['basis']['point']);J=V[root]&T
            acq=[q for q in adj[root] if J<=V[q] and (V[q]&T)-J]
            lengths=[1] if acq else []
            for f in dc['faces']:
                fixed=set(f['fixed_rows']);allowed={q for q in V if fixed<=V[q]}
                supplied={tuple(bs['point']) for bs in f['corners']}
                require(allowed==supplied,'face certificate misses an original vertex')
                require(len(allowed)<=len(A)-len(u)+2,'independent face size bound')
                D=distances(adj,root,allowed)
                require(set(D)==allowed,'two-face reference is disconnected')
                exits=[D[q] for q in D if (V[q]&T)-J]
                if exits:lengths.append(min(exits))
                faces+=1
            arc,r=new.audit_decision(A,b,phase['objective'],c['target_basis'],dc)
            require(bool(r['acquired'])==bool(lengths),'wrong whole-face target-accessibility verdict')
            if lengths:require(len(arc)==min(lengths),'not a shortest first-hit arc in its face collection')
            # Every non-backtracking two-edge path of a simple polytope lies
            # on one original two-face. Check containment of old horizon2 exits.
            radius2=False
            for q in adj[root]:
                if not J<=V[q]:continue
                if (V[q]&T)-J:radius2=True
                for z in adj[q]:
                    if J<=V[z] and (V[z]&T)-J:radius2=True
            require(not radius2 or (bool(lengths) and min(lengths)<=2),'missed a radius-two acquisition')
            decisions+=1
    return faces,decisions


def graph_stage(name):
    A,b=models()[name];begin=time.monotonic();V,adj,anchors=reference(A,b)
    pairs=[(u,v) for u in V for v in V if u!=v]
    complete=not(name.startswith('holdout') or name=='truncated_octahedron')
    if not complete:
        random.Random(253+len(A)).shuffle(pairs);pairs=pairs[:80]
    if name=='truncated_octahedron':
        special=(tuple(map(Q,[2,1,0])),tuple(map(Q,[-2,-1,0])))
        if special not in pairs:pairs.append(special)
    if name=='holdout_clipped_slanted_prism':
        special=(tuple(map(Q,[1,1,0])),tuple(map(Q,[3,9,2])))
        if special not in pairs:pairs.append(special)
    totals={'pairs':0,'previous_edges':0,'new_edges':0,'loop_erased_edges':0,'shortest_total':0,
      'previous_nonshortest':0,'new_nonshortest':0,'shorter_than_previous':0,'same_as_previous':0,'longer_than_previous':0,
      'face_coverage_checks':0,'decision_checks':0,'faces':0,'traced_face_edges':0,'fallback_decisions':0,
      'decreasing_edges':0,'loop_erased_cycles':0,'retired_improving_faces':0}
    details=[];saved_bad=None;saved_gain=None;data_cache={}
    for idx,(u,v) in enumerate(pairs):
        if u not in data_cache:data_cache[u]=distances(adj,u)
        optimum=data_cache[u][v]
        cprev=previous.construct(A,b,u,v,lookahead=2)
        rprev=previous.verify(A,b,u,v,cprev)
        out=new.construct(A,b,u,v);r=out['verified'];c=out['certificate']
        path=[tuple(p) for p in r['path']]
        require(path[0]==u and path[-1]==v and all(q in adj[p] for p,q in zip(path,path[1:])),
                'new route not in independent ORIGINAL graph')
        short=[tuple(p) for p in r['loop_erased_path']]
        require(all(q in adj[p] for p,q in zip(short,short[1:])) and len(set(short))==len(short),
                'loop erasure did not preserve original edges')
        require(optimum<=r['loop_erased_edges']<=r['committed_edges'],'invalid route length comparison')
        nf,nd=check_faces(A,b,u,v,c,V,adj)
        totals['pairs']+=1;totals['previous_edges']+=rprev['edges'];totals['new_edges']+=r['committed_edges']
        totals['loop_erased_edges']+=r['loop_erased_edges'];totals['shortest_total']+=optimum
        totals['previous_nonshortest']+=rprev['edges']>optimum;totals['new_nonshortest']+=r['committed_edges']>optimum
        totals['shorter_than_previous' if r['committed_edges']<rprev['edges'] else
               'longer_than_previous' if r['committed_edges']>rprev['edges'] else 'same_as_previous']+=1
        totals['face_coverage_checks']+=nf;totals['decision_checks']+=nd
        for key in ['faces','traced_face_edges','fallback_decisions']:totals[key]+=r[key]
        totals['retired_improving_faces']+=r['retired_improving_faces']
        totals['decreasing_edges']+=r['old_phase_decreasing_steps']
        totals['loop_erased_cycles']+=r['committed_edges']-r['loop_erased_edges']
        details.append({'start':u,'target':v,'shortest':optimum,'previous_depth2':rprev['edges'],
             'two_face_edges':r['committed_edges'],'fallback_decisions':r['fallback_decisions']})
        if r['committed_edges']>optimum and saved_bad is None:
            saved_bad={'input':{'A':A,'b':b,'start':u,'target':v},**out,'shortest':optimum,'old_edges':rprev['edges']}
        if r['committed_edges']<rprev['edges'] and saved_gain is None:
            saved_gain={'input':{'A':A,'b':b,'start':u,'target':v},**out,'shortest':optimum,'old_edges':rprev['edges']}
    if saved_bad:dump(ROOT/f'fixtures/two_face_{name}_nonshortest.json',saved_bad)
    if saved_gain:dump(ROOT/f'fixtures/two_face_{name}_improved.json',saved_gain)
    dump(ROOT/f'research/TWO_FACE_PAIRS_{name}.json',details)
    return {'name':name,'complete_ordered_pair_comparison':complete,'dimension':len(A[0]),'facets':len(A),
        'vertices':len(V),'graph_edges':sum(map(len,adj.values()))//2,'facet_anchors':anchors,
        'totals':totals,'seconds':round(time.monotonic()-begin,3)}


def parabolic(N,h):
    ts=[Q(j,h+1) for j in range(h+2)]+[1+Q(3*j,2*N) for j in range(1,N+1)]+[Q(3)]
    A=[[x+y,-Q(1)] for x,y in zip(ts,ts[1:])]+[[-Q(3),Q(1)]]
    b=[x*y for x,y in zip(ts,ts[1:])]+[Q(0)]
    return A,b,[Q(1),Q(1)],[Q(3),Q(9)],[[x,x*x] for x in ts]


def affine(A,b,start,target,seed):
    rng=random.Random(seed);d=len(start);M=sp.eye(d)
    for i in range(d):
        M[i,i]=(-1 if (i+seed)%2 else 1)*(i+1)
        for j in range(i+1,d):M[i,j]=sp.Rational(rng.randrange(-3,4),rng.randrange(1,4))
    inv=M.inv();shift=[Q(rng.randrange(-3,4),7) for _ in range(d)]
    AA=[[sum(Q(inv[k,j])*a[k] for k in range(d)) for j in range(d)] for a in A]
    bb=[v+dot(a,shift) for a,v in zip(AA,b)]
    image=lambda x:[sum(Q(M[i,j])*x[j] for j in range(d))+shift[i] for i in range(d)]
    return AA,bb,image(start),image(target),image


def product_model(factors):
    p=len(factors);A=[];b=[];u=[];v=[]
    for j,(N,h,start_index,target_index) in enumerate(factors):
        aa,bb,_,_,pts=parabolic(N,h)
        A.extend([[Q(0)]*(2*j)+row+[Q(0)]*(2*(p-j-1)) for row in aa]);b+=bb
        u+=pts[start_index];v+=pts[target_index]
    return A,b,u,v


def family_stage(which, selected_case=None):
    examples=[]
    if which=='delays':
        for N,h in [(8,2),(16,2),(32,2),(64,2),(64,8),(64,16)]:
            A,b,u,v,pts=parabolic(N,h)
            out=new.construct(A,b,u,v);r=out['verified']
            c=previous.construct(A,b,u,v,lookahead=2);old=previous.verify(A,b,u,v,c)
            optimum=min(N+1,h+2)
            require(r['committed_edges']==optimum and r['fallback_decisions']==0,'whole polygon failed shortestness')
            require(old['edges']==N+1,'fixed-horizon baseline changed')
            require(r['largest_face']==N+h+3 and r['faces']==1,'full polygon was not certified')
            info={'N':N,'hidden_backward_vertices':h,'facets':len(A),'new_edges':r['committed_edges'],
              'previous_depth2_edges':old['edges'],'independent_cycle_distance':optimum,
              'full_face_edges_traced':r['traced_face_edges'],'first_acquisition_edges':r['phase_edges'][0]}
            examples.append(info)
            if (N,h) in [(64,2),(64,16)]:dump(ROOT/f'fixtures/two_face_delay_{h}.json',{'input':{'A':A,'b':b,'start':u,'target':v},**out})
    elif which=='products':
        configs=[[(8,4,5,14)]*p for p in (2,3,4,6)]
        # Independent endpoints, not always the special delayed source/target.
        configs+=[[(6,3,2,9),(8,2,6,11),(5,1,0,6)]]
        for idx,fac in enumerate(configs):
            if selected_case is not None and idx!=selected_case:continue
            A,b,u,v=product_model(fac)
            if idx==len(configs)-1:
                A,b,u,v,image=affine(A,b,u,v,871)
            out=new.construct(A,b,u,v);r=out['verified']
            old_r=None
            if len(u)<=8:
                old_c=previous.construct(A,b,u,v,lookahead=2)
                old_r=previous.verify(A,b,u,v,old_c)
            expected=sum(min(abs(i-j),N+h+3-abs(i-j)) for N,h,i,j in fac)
            require(r['committed_edges']==expected and r['fallback_decisions']==0,'product shortestness theorem failed')
            examples.append({'dimension':len(u),'genuine_facets':len(A),'known_vertex_count':
                __import__('math').prod(N+h+3 for N,h,_,_ in fac),
                'unknown_affine_chart':idx==len(configs)-1,'previous_depth2_edges':None if old_r is None else old_r['edges'],
                'previous_depth2_replayed':old_r is not None,'edges':r['committed_edges'],'independent_product_distance':expected,
                'faces':r['faces'],'traced_face_edges':r['traced_face_edges'],'decisions':r['decisions'],
                'full_product_graph_enumerated':False})
            if idx==3:dump(ROOT/'fixtures/two_face_product12d.json',{'input':{'A':A,'b':b,'start':u,'target':v},**out})
    elif which=='roof':
        for d in (3,4,6,8):
            data=roof.roof_input(d);A,b,u,v=data['A'],data['b'],data['start'],data['target']['point']
            out=new.construct(A,b,u,v);r=out['verified']
            prev=previous.construct(A,b,u,v,lookahead=2);rp=previous.verify(A,b,u,v,prev)
            examples.append({'dimension':d,'facets':len(A),'new_edges':r['committed_edges'],
                'previous_depth2_edges':rp['edges'],'canonical_normalized_formula':2**d+d-2,
                'canonical_exponential_trajectory_replayed':False,'faces':r['faces'],'fallback_decisions':r['fallback_decisions']})
    return {'kind':which,'examples':examples}


def auxiliary_stage():
    A,b=models()['truncated_octahedron'];u=list(map(Q,[2,1,0]));v=list(map(Q,[-2,-1,0]))
    out=new.construct(A,b,u,v);c=out['certificate'];first=c['phases'][0]['decisions'][0]
    require(first['selection']['kind']=='face_gain' and out['verified']['fallback_decisions']>0,
            'missing genuine no-two-face-acquisition example')
    V,adj,_=reference(A,b)
    for f in first['faces']:
        require(all(not (V[tuple(bs['point'])]&V[tuple(v)]) for bs in f['corners']),
                'claimed inaccessible target face is present')
    dump(ROOT/'fixtures/two_face_no_acquisition.json',{'input':{'A':A,'b':b,'start':u,'target':v},**out})
    rng=random.Random(881);samples=[];affine_n=scale_n=disabled=0
    for name in ['moment_3_8','moment_4_7','clipped_cube_3']:
        AA,bb=models()[name];VV,_,_=reference(AA,bb);vertices=list(VV)
        for k in range(3):
            x,y=rng.sample(vertices,2);rr=new.construct(AA,bb,x,y)
            Ap,bp,xp,yp,image=affine(AA,bb,x,y,10+k)
            got=new.construct(Ap,bp,xp,yp)['verified']
            require(got['path']==[image(z) for z in rr['verified']['path']],'affine trajectory mismatch');affine_n+=1
            s=[Q(2)**(i%13-6) for i in range(len(AA))]
            got=new.construct([[t*z for z in a] for a,t in zip(AA,s)],[t*z for t,z in zip(s,bb)],x,y)['verified']
            require(got['path']==rr['verified']['path'],'positive row-rescaling mismatch');scale_n+=1
            samples.append((AA,bb,x,y,rr['certificate'],rr['verified']))
    original=(base.invert,base.basis_packet,new.trace_face,new.produce_decision)
    def forbidden(*args,**kwargs):raise AssertionError('verifier called discovery')
    base.invert=base.basis_packet=new.trace_face=new.produce_decision=forbidden
    try:
        for AA,bb,x,y,cc,expected in samples:
            require(new.verify(AA,bb,x,y,cc)==expected,'search-disabled replay mismatch');disabled+=1
    finally:base.invert,base.basis_packet,new.trace_face,new.produce_decision=original
    names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forged/unsupported '+name)
    def mutation(name,edit):
        cc=deepcopy(c);edit(cc);require(json.dumps(serial(cc),sort_keys=True)!=json.dumps(serial(c),sort_keys=True),'negative test made no mutation');reject(name,lambda:new.verify(A,b,u,v,cc))
    get=lambda cc:cc['phases'][0]['decisions'][0]
    mutation('omitted_two_face',lambda cc:get(cc)['faces'].pop())
    mutation('extra_two_face',lambda cc:get(cc)['faces'].append(get(cc)['faces'][0]))
    mutation('missing_polygon_vertex',lambda cc:get(cc)['faces'][0]['corners'].pop())
    mutation('reversed_polygon_orientation',lambda cc:get(cc)['faces'][0]['corners'].reverse())
    mutation('repeated_polygon_vertex',lambda cc:get(cc)['faces'][0]['corners'].append(get(cc)['faces'][0]['corners'][0]))
    mutation('wrong_fixed_row',lambda cc:get(cc)['faces'][0]['fixed_rows'].__setitem__(0,0))
    mutation('false_inverse',lambda cc:get(cc)['faces'][0]['corners'][1]['directions'][0].__setitem__(0,Q(99)))
    mutation('false_polygon_point',lambda cc:get(cc)['faces'][0]['corners'][1]['point'].__setitem__(0,Q(99)))
    mutation('false_phase_objective',lambda cc:cc['phases'][0]['objective'].__setitem__(0,Q(99)))
    mutation('omitted_phase_end',lambda cc:cc['phases'].pop())
    mutation('false_target_point',lambda cc:cc['target_basis']['point'].__setitem__(0,Q(99)))
    mutation('false_selection',lambda cc:get(cc)['selection'].update(count=999))
    mutation('bool_selection',lambda cc:get(cc)['selection'].update(sign=True))
    mutation('wrong_problem',lambda cc:cc.update(problem_sha256='bad'))
    reject('nonsimple_source',lambda:new.construct([[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],
                    [0,1,1,1,1],[0,0,1],[1,1,0]))
    reject('nonvertex_target',lambda:new.construct([[-1,0],[0,-1],[1,1]],[0,0,1],[0,0],[Q(1,2),Q(1,2)]))
    reject('edge_cap',lambda:new.construct(A,b,u,v,edge_cap=1))
    reject('float_input',lambda:new.construct([[1.0,0],[-1,0],[0,1],[0,-1]],[1,0,1,0],[0,0],[1,1]))
    # A deliberately unbounded simple polygon: tracing cannot falsely close its face.
    UA=[[-1,0],[0,-1],[-1,-1]];Ub=[0,0,-1]
    reject('unbounded_face_trace',lambda:new.trace_face(UA,Ub,[Q(1),Q(0)],[],{}))
    # Zero steps and a one-dimensional retained face remain valid.
    for x,y in [([0],[0]),([0],[1])]:new.construct([[-1],[1]],[0,1],x,y)
    return {'affine_checks':affine_n,'row_scaling_checks':scale_n,'search_disabled_checks':disabled,
            'rejected':names,'no_face_acquisition_first_decision':first['selection']['kind'],
            'no_face_acquisition_model_facets':len(A),'no_face_acquisition_route_edges':out['verified']['committed_edges'],
            'no_face_acquisition_shortest':distances(adj,tuple(u))[tuple(v)]}


def main():
    p=argparse.ArgumentParser();p.add_argument('--graph',choices=list(models()));p.add_argument('--family',choices=['delays','products','roof'])
    p.add_argument('--product-case',type=int,choices=range(5));p.add_argument('--aux',action='store_true');p.add_argument('--assemble',action='store_true');a=p.parse_args()
    for n,sha in DEPENDENCIES.items():
        data=(ROOT/'scripts'/n).read_bytes();require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==sha,
                                                   'changed frozen dependency '+n)
    jobs=[]
    if a.product_case is not None:jobs=[('product_case_'+str(a.product_case),lambda:family_stage('products',a.product_case))]
    elif a.graph:jobs=[('graph_'+a.graph,lambda:graph_stage(a.graph))]
    elif a.family:jobs=[('family_'+a.family,lambda:family_stage(a.family))]
    elif a.aux:jobs=[('aux',auxiliary_stage)]
    elif not a.assemble:
        jobs=[('graph_'+n,lambda n=n:graph_stage(n)) for n in models()]
        jobs += [('family_'+n,lambda n=n:family_stage(n)) for n in ['delays','products','roof']]+[('aux',auxiliary_stage)]
    for name,fn in jobs:
        begin=time.monotonic();result=fn();dump(ROOT/f'research/TWO_FACE_STAGE_{name}.json',
            {'status':'PASS','source_sha256':source_hashes(),'result':result,'seconds':round(time.monotonic()-begin,3)})
        print(name,'PASS',round(time.monotonic()-begin,3),flush=True)
    if a.assemble or (a.product_case is None and not any([a.graph,a.family,a.aux])):
        parts=[ROOT/f'research/TWO_FACE_STAGE_product_case_{j}.json' for j in range(5)]
        if all(p.exists() for p in parts):
            loaded=[json.loads(p.read_text()) for p in parts]
            if all(x['status']=='PASS' and x['source_sha256']==source_hashes() for x in loaded):
                dump(ROOT/'research/TWO_FACE_STAGE_family_products.json',{'status':'PASS','source_sha256':source_hashes(),
                    'seconds':sum(x['seconds'] for x in loaded),'result':{'kind':'products',
                    'examples':[e for x in loaded for e in x['result']['examples']]}})
        keys=['graph_'+n for n in models()]+['family_'+n for n in ['delays','products','roof']]+['aux']
        stages={k:json.loads((ROOT/f'research/TWO_FACE_STAGE_{k}.json').read_text()) for k in keys}
        require(all(s['status']=='PASS' and s['source_sha256']==source_hashes() for s in stages.values()),'stale stage')
        graphs=[stages['graph_'+n]['result'] for n in models()]
        totals={k:sum(g['totals'][k] for g in graphs) for k in graphs[0]['totals']}
        out={'status':'PASS','scope':'Research/ exact original-H routes and two-face audits; no Lean or universal polynomial phase bound.',
             'source_sha256':source_hashes(),'graph_totals':totals,'graphs':graphs,
             'families':{n:stages['family_'+n]['result'] for n in ['delays','products','roof']},'auxiliary':stages['aux']['result']}
        dump(ROOT/'research/TWO_FACE_ACQUISITION_CHECK.json',out);print(json.dumps(totals,indent=2))
if __name__=='__main__':main()
