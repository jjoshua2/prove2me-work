#!/usr/bin/env python3
"""Sharp-order phase accounting for the unchanged complete-two-face selector.
Exact rational constructions and independent graph checks; no Lean claim.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random,time
import sympy as sp
import two_face_acquisition as route
import three_dimensional_face_accounting as ledger
import simple_tangent_policy_audit as base
ROOT=Path(__file__).resolve().parents[1]

def cross(a,b):return(a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])

def normal(vertices,face):
    u,v,w=[vertices[i]for i in face]
    n=cross([x-y for x,y in zip(v,u)],[x-y for x,y in zip(w,u)])
    t=base.dot(n,u);base.require(t!=0,'face plane through origin')
    return tuple(x/t for x in n)

def construct_input(m):
    base.require(type(m)is int and 8<=m<=40,'explicit arithmetic experiment cap')
    V=[(-Q(1),-Q(1),-Q(1)),(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1))]
    faces={F:normal(V,F)for F in combinations(range(4),3)};front=(1,2,3);steps=[]
    for j in range(4,m):
        c=tuple(sum(V[i][k]for i in front)/3 for k in range(3));delta=Q(1)
        for F,a in faces.items():
            val=base.dot(a,c)
            if F!=front and val>0:delta=min(delta,1/val-1)
        delta/=2;y=tuple((1+delta)*x for x in c)
        base.require(delta>0 and base.dot(faces[front],y)>1,'not beyond selected front')
        base.require(all(base.dot(a,y)<1 for F,a in faces.items()if F!=front),'stack point beyond another facet')
        steps.append({'front':front,'new_vertex':y,'radial_step':delta})
        V.append(y);faces.pop(front)
        for pair in combinations(front,2):F=(*pair,j);faces[F]=normal(V,F)
        front=(j-2,j-1,j)
    # This explicitly validates the complete stacked boundary and dual vertices.
    base.require(len(faces)==2*m-4,'wrong stacked facet count')
    for F,a in faces.items():
        base.require(max(F)-min(F)<=3,'label corridor width exceeded')
        base.require(all(base.dot(a,v)<=1 and(base.dot(a,v)==1)==(i in F)for i,v in enumerate(V)),'bad primal facet/dual vertex')
    A=[list(v)for v in V];b=[Q(1)]*m
    for i in range(m):
        incident=[x for F,x in faces.items()if i in F]
        anchor=[sum(x[k]for x in incident)/len(incident)for k in range(3)]
        base.require(base.active_rows(A,b,anchor)==[i],'dual row is not an irredundant facet')
        base.require(3<=len(incident)<=6,'polygon degree bound failed')
    return A,b,list(faces[(0,1,2)]),list(faces[front]),faces,steps

def reference_distance(faces):
    first=(0,1,2);last=max(faces,key=lambda f:min(f));q=deque([first]);D={first:0};adj={f:[]for f in faces}
    for f,g in combinations(faces,2):
        if len(set(f)&set(g))==2:adj[f].append(g);adj[g].append(f)
    base.require(all(len(a)==3 for a in adj.values()),'wrong dual graph degree')
    while q:
        f=q.popleft()
        for g in adj[f]:
            if g not in D:D[g]=D[f]+1;q.append(g)
    base.require(len(D)==len(faces),'stacked dual disconnected')
    return D[last],adj


def explicit_graph(A,b):
    """Independent all-active-subset graph; used only on small 3D inputs."""
    V={};n=len(A[0]);count=0
    for ids in combinations(range(len(A)),n):
        M=sp.Matrix([A[i]for i in ids]);count+=1
        if M.det()==0:continue
        x=tuple(Q(str(z))for z in M.inv()*sp.Matrix([b[i]for i in ids]))
        if base.feasible(A,b,x):V[x]=set(base.active_rows(A,b,x))
    base.require(V and all(len(j)==n for j in V.values()),'nonsimple reference graph')
    adj={x:[]for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==n-1:adj[x].append(y);adj[y].append(x)
    base.require(all(len(a)==n for a in adj.values()),'wrong full graph degree')
    return V,adj,count


def distance(adj,u,v):
    D={u:0};q=deque([u])
    while q:
        x=q.popleft()
        if x==v:return D[x]
        for y in adj[x]:
            if y not in D:D[y]=D[x]+1;q.append(y)
    raise ValueError('disconnected reference')


def dodecahedron():
    A=[]
    for a,b in product((-Q(1),Q(1)),repeat=2):
        A.extend([[Q(0),a,Q(8,5)*b],[a,Q(8,5)*b,Q(0)],[Q(8,5)*b,Q(0),a]])
    return A,[Q(1)]*12


def moment3(n):
    V=[[Q(i)**j for j in(1,2,3)]for i in range(n)]
    mean=[sum(v[j]for v in V)/n for j in range(3)]
    return [[v[j]-mean[j]for j in range(3)]for v in V],[Q(1)]*n


def check_full_graph(A,b,V,adj):
    # Strict original-row facet anchors plus original primal/dual vertex facts
    # distinguish input rows from a possibly smaller irredundant facet count.
    for i in range(len(A)):
        X=[x for x,J in V.items()if i in J]
        base.require(len(X)>=3,'not a genuine facet')
        mean=[sum(x[j]for x in X)/len(X)for j in range(3)]
        base.require(base.active_rows(A,b,mean)==[i],'non-strict facet anchor')
    edges=sum(map(len,adj.values()))//2
    base.require(len(V)-edges+len(A)==2 and 2*edges==3*len(V),'polyhedral Euler incidence')
    dual=[set()for _ in A]
    for x in V:
        for y in adj[x]:
            if x<y:
                common=V[x]&V[y];base.require(len(common)==2,'not ordinary original edge')
                i,j=common;dual[i].add(j);dual[j].add(i)
    base.require(all(len(dual[i])==sum(i in J for J in V.values())for i in range(len(A))),
                 'dual degree differs from primal facet size')
    return dual


def main():
    start=time.monotonic();corridors=[];examples=[];small=[];saved=[];counters={'pairs':0,'edges':0,'fallback_macros':0,'fallback_edges':0,
        'selected_facets':0,'independent_original_edges':0,'negative_controls':[],'macro_span_checks':0}
    for m in(8,12,16,24,32):
        A,b,u,v,F,stack=construct_input(m);dist,adjlabels=reference_distance(F)
        o=route.construct(A,b,u,v);c=o['certificate'];r=o['verified'];acc=ledger.account(A,b,u,v,c)
        lower=max(0,(m-8+2)//3);fb=r['phase_fallback_bounds'][0]['fallback_decisions']
        base.require(fb>=lower,'all-size lower bound for actual #253 macros failed')
        for phase in c['phases']:
            for dc in phase['decisions']:
                arc,info=route.audit_decision(A,b,phase['objective'],c['target_basis'],dc)
                if not info['acquired']:
                    before=max(dc['basis']['active']);after=max(base.active_rows(A,b,arc[-1]))
                    base.require(after<=before+3,'macro jumps outside the label corridor')
                    counters['macro_span_checks']+=1
        for x,y in zip(r['path'],r['path'][1:]):
            base.require(tuple(base.active_rows(A,b,y))in adjlabels[tuple(base.active_rows(A,b,x))],
                         'route is not in independently constructed stacking graph')
        exact=None
        if m<=12:
            VV,AA,n=explicit_graph(A,b);exact=distance(AA,tuple(u),tuple(v))
            base.require(exact==dist and set(VV)==set(F.values()),'independent subset reconstruction mismatch')
        corridors.append({'original_facets':m,'dimension':3,'vertices':2*m-4,'largest_polygon':max(sum(i in f for f in F)for i in range(m)),
            'shortest_distance':dist,'independent_subset_distance':exact,'actual_253_edges':r['committed_edges'],
            'actual_253_fallback_macros':fb,'lower_bound':lower,'retired_face_count':r['retired_improving_faces'],
            'weighted_fallback_charge':acc['weighted_fallback_charge'],'fallback_edges':acc['fallback_edges'],
            'new_linear_tail_bound':acc['linear_tail_bound'],'old_binomial_bound':r['original_facet_binomial_route_bound'],
            'input_entry_max_num_plus_den_bits':max(x.numerator.bit_length()+x.denominator.bit_length()for a in A for x in a)})
        saved.append((A,b,u,v,c))
        if m==12:examples.append({'name':'stacked_corridor_12','input':{'A':A,'b':b,'start':u,'target':v},
            'stacking':stack,'certificate':c,'account':acc})
    models=[('moment3_6',*moment3(6)),('moment3_8',*moment3(8)),('moment3_10',*moment3(10)),('dodecahedron',*dodecahedron())]
    for name,A,b in models:
        V,adj,subsets=explicit_graph(A,b);dual=check_full_graph(A,b,V,adj)
        totals={'model':name,'facets':len(A),'vertices':len(V),'edges':sum(map(len,adj.values()))//2,'pairs':0,
            'route_edges':0,'shortest_total':0,'fallback_macros':0,'weighted_charge':0,'nonshortest':0}
        for u in V:
            for v in V:
                if u==v:continue
                o=route.construct(A,b,u,v);c=o['certificate'];r=o['verified'];acc=ledger.account(A,b,u,v,c)
                dist=distance(adj,u,v);T=V[v];N=set(range(len(A)))-T
                induced=sum(len(dual[i]&N)for i in N)
                base.require(induced<=max(0,6*len(N)-12),'independent planar induced incidence failed')
                labels=[x['original_row']for x in acc['selected_facets']]
                base.require(all(not(dual[i]&T)for i in labels),'retired facet adjacent to target')
                base.require(acc['weighted_fallback_charge']+len(labels)<=induced,'weighted charge not backed by actual induced graph')
                for x,y in zip(r['path'],r['path'][1:]):base.require(tuple(y)in adj[tuple(x)],'nonedge route')
                totals['pairs']+=1;totals['route_edges']+=r['committed_edges'];totals['shortest_total']+=dist
                totals['fallback_macros']+=r['fallback_decisions'];totals['weighted_charge']+=acc['weighted_fallback_charge'];totals['nonshortest']+=r['committed_edges']>dist
                counters['pairs']+=1;counters['edges']+=r['committed_edges'];counters['fallback_macros']+=r['fallback_decisions']
                counters['fallback_edges']+=acc['fallback_edges'];counters['selected_facets']+=len(labels)
                counters['independent_original_edges']+=len(r['path'])-1
                if r['fallback_decisions']and not any(w['name']==name for w in examples):
                    examples.append({'name':name,'input':{'A':A,'b':b,'start':u,'target':v},'certificate':c,'account':acc})
                    saved.append((A,b,u,v,c))
        small.append(totals)
    # Original three-face embedded in arbitrarily many locked coordinate rows.
    # No global high-dimensional graph is enumerated or passed to the selector.
    tails=[];A,b=dodecahedron();u=[-Q(5,13)]*3;v=[Q(5,13)]*3
    for ambient in(4,8,16):
        AA=[a+[Q(0)]*(ambient-3)for a in A];bb=list(b)
        for i in range(3,ambient):
            AA.extend([[Q(s)*int(i==j)for j in range(ambient)]for s in(-1,1)]);bb.extend([Q(0),Q(1)])
        uu=u+[Q(0)]*(ambient-3);vv=v+[Q(0)]*(ambient-3)
        o=route.construct(AA,bb,uu,vv);acc=ledger.account(AA,bb,uu,vv,o['certificate'])
        base.require(acc['missing_target_facets']==3 and acc['committed_edges']==5,'intrinsic three-face transport failed')
        tails.append({'ambient_dimension':ambient,'retained_dimension':3,'original_facets':len(AA),'original_edges':5,
                      'linear_bound_from_original_excess':acc['linear_tail_bound'],'global_graph_enumerated':False})
        saved.append((AA,bb,uu,vv,o['certificate']))
    # The proof-consumer ledger and original route auditor must remain search-free.
    old=(base.invert,base.basis_packet,route.trace_face)
    def no(*a,**kw):raise AssertionError('audit called a search routine')
    base.invert=base.basis_packet=route.trace_face=no
    try:
        for A,b,u,v,c in saved:ledger.account(A,b,u,v,route.decode(json.loads(json.dumps(base.serial(c)))))
    finally:base.invert,base.basis_packet,route.trace_face=old
    def reject(name,fn):
        try:fn()
        except(ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):counters['negative_controls'].append(name)
        else:raise AssertionError('accepted false accounting input: '+name)
    A,b,u,v,c=saved[0]
    for name,mut in [('false_objective',lambda z:z['phases'][0]['objective'].__setitem__(0,Q(99))),
        ('missing_face',lambda z:z['phases'][0]['decisions'][0]['faces'].pop()),
        ('false_inverse',lambda z:z['phases'][0]['decisions'][0]['basis']['directions'][0].__setitem__(0,Q(123))),
        ('changed_input_hash',lambda z:z.update(problem_sha256='00')),
        ('missing_phase',lambda z:z['phases'].pop()),
        ('false_cycle',lambda z:z['phases'][0]['decisions'][0]['faces'][0]['corners'].pop())]:
        bad=deepcopy(c);mut(bad);reject(name,lambda bad=bad:ledger.account(A,b,u,v,bad))
    AA=[[Q(s)*int(i==j)for j in range(4)]for i in range(4)for s in(-1,1)];bb=[Q(1)]*8
    cc=route.construct(AA,bb,[-Q(1)]*4,[Q(1)]*4)['certificate']
    reject('four_dimensional_tail_mislabeled',lambda:ledger.account(AA,bb,[-Q(1)]*4,[Q(1)]*4,cc))
    report={'status':'PASS','scope':'New written weighted-retirement proof and exact tests of unchanged #253; no Lean/platform verdict.',
        'unchanged_selector_git_blob':'aa562f02dd492ecc47479381d637c6292757ebd3','small_graphs':small,'corridors':corridors,
        'intrinsic_three_faces':tails,'search_disabled_audits':len(saved),**counters,
        'uniform_corridor_lower':'B3 >= max(0,ceil((m-8)/3)), all polygon sizes <=6; applies to entire face macros',
        'linear_tail_bound':'for r=3 and e=m-d, L<=6e-12+2*floor((e+2)/2); r=2: L<=floor((e+2)/2); r<=1: L<=r',
        'seconds':round(time.monotonic()-start,3),
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/'research/WEIGHTED_FACE_RETIREMENT_TESTS.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    (ROOT/'fixtures/weighted_face_retirement_examples.json').write_text(json.dumps(base.serial(examples),sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
