#!/usr/bin/env python3
"""Exact tests of target-deleted phase/cap accounting, not new path selection.

Original #253 and #254 dependencies are unchanged. Explicit all-active-subset
reference enumeration is restricted to small inputs and labeled separately
from finite per-route certificates. No generic Lean verification is claimed.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from math import comb
from pathlib import Path
import argparse,hashlib,json,random,time
import simple_tangent_policy_audit as base
import two_face_acquisition as route
import target_deleted_phase_accounting as ledger
import test_weighted_face_retirement as old
ROOT=Path(__file__).resolve().parents[1]


def vertices(A,b):
    d=len(A[0]);out={};tested=0
    for ids in combinations(range(len(A)),d):
        tested+=1
        try:R=base.invert([A[i]for i in ids])
        except ValueError:continue
        x=tuple(base.dot(r,[b[i]for i in ids])for r in R)
        if base.feasible(A,b,x):out[x]=set(base.active_rows(A,b,x))
    return out,tested


def graph(A,b):
    V,tested=vertices(A,b);d=len(A[0]);base.require(V and all(len(J)==d for J in V.values()),'nonsimple original model')
    adj={x:[]for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    base.require(all(len(a)==d for a in adj.values()),'reference graph not d-regular')
    for i in range(len(A)):
        pts=[x for x,J in V.items()if i in J];base.require(pts,'redundant original row')
        mean=[sum(x[j]for x in pts)/len(pts)for j in range(d)]
        base.require(base.active_rows(A,b,mean)==[i],'facet anchor not strict')
    return V,adj,tested


def distances(adj,u):
    D={u:0};queue=deque([u])
    while queue:
        x=queue.popleft()
        for y in adj[x]:
            if y not in D:D[y]=D[x]+1;queue.append(y)
    base.require(len(D)==len(adj),'reference disconnected')
    return D


def moment(d,m):
    pts=[[Q(i)**j for j in range(1,d+1)]for i in range(m)]
    mean=[sum(v[j]for v in pts)/m for j in range(d)]
    return [[v[j]-mean[j]for j in range(d)]for v in pts],[Q(1)]*m


def hidden(d):
    # #255's already-authored family is reused as a boundary control, not a
    # newly claimed construction: delete its target rows and obtain the cube.
    A=[[-Q(i==j)for j in range(d)]for i in range(d)]
    A += [[Q(i==j)for j in range(d)]for i in range(d)]
    a=[Q(1,2)+Q(i+1,10*d*d)for i in range(d)]
    A += [[Q(1)+Q(i==j)for j in range(d)]for i in range(d)]
    b=[Q(0)]*d+[Q(1)]*d+[d+x for x in a]
    total=sum(b[-d:])/(d+1);v=[z-total for z in b[-d:]]
    base.require(base.active_rows(A,b,v)==list(range(2*d,3*d)),'hidden-family target changed')
    return A,b,[Q(0)]*d,v


def clipped_moment(d,m):
    A,b=moment(d,m);V,_=vertices(A,b);x=max(V);T=sorted(V[x]);delta=Q(1)
    for y in V:
        if y==x:continue
        slack=[b[i]-base.dot(A[i],y)for i in T]
        for s in slack:delta=min(delta,(sum(slack)+s)/4)
    cut=[delta*(1+Q(i+1,10*d*d))for i in range(d)]
    rows=[[sum(A[i][j]for i in T)+A[k][j]for j in range(d)]for k in T]
    rhs=[sum(b[i]for i in T)+b[k]-cut[q]for q,k in enumerate(T)]
    R=base.invert(rows);target=[base.dot(r,rhs)for r in R]
    AA=A+rows;bb=b+rhs
    base.require(base.feasible(AA,bb,target) and base.active_rows(AA,bb,target)==list(range(m,m+d)), 'new clipped target')
    return AA,bb,target


def main(stage='all'):
    rng=random.Random(254256);start=time.monotonic()
    totals={'routes':0,'original_edges':0,'loop_erased_edges':0,'erased_edges':0,'phase_cells':0,
      'restricted_inverse_identities':0,'cap_vertex_enumerations':0,'cap_active_subsets':0,
      'cap_vertices':0,'nonsimple_capped_models':0,'cap_vertices_outside_original_target_cuts':0,
      'maximum_retained_dimension':0,'fallback_macros':0,'search_disabled_audits':0}
    results=[];saved=[];fixtures=[];max_caps=24
    def test(A,b,u,v,name,reference=None,enumerate_caps=False):
        nonlocal max_caps
        made=route.construct(A,b,u,v);c=made['certificate'];acc=ledger.produce(A,b,u,v,c)
        audit=ledger.audit(A,b,u,v,c,acc);raw=made['verified'];totals['routes']+=1
        totals['original_edges']+=audit['original_raw_edges'];totals['loop_erased_edges']+=audit['certified_loop_erased_edges']
        totals['erased_edges']+=audit['original_raw_edges']-audit['certified_loop_erased_edges']
        totals['phase_cells']+=len(acc['cells']);totals['restricted_inverse_identities']+=audit['restricted_inverse_identities']
        totals['fallback_macros']+=raw['fallback_decisions']
        totals['maximum_retained_dimension']=max(totals['maximum_retained_dimension'],audit['missing_target_facets'])
        if reference is not None:
            V,adj=reference
            for x,y in zip(raw['loop_erased_path'],raw['loop_erased_path'][1:]):
                base.require(tuple(y)in adj[tuple(x)],'not a genuine original graph edge')
            shortest=distances(adj,tuple(u))[tuple(v)]
        else:shortest=None
        capchecks=[]
        if enumerate_caps:
            for phase,cell in zip(c['phases'],acc['cells']):
                h=len(cell['free_origin_rows'])
                if max_caps<=0 or h<3 or comb(len(cell['rhs'])+1,h)>1000:continue
                max_caps-=1
                C=cell['inequalities']+[cell['cap_row']];rhs=cell['rhs']+[cell['cap']]
                W,n=vertices(C,rhs);base.require(len(W)<=ledger.cyclic_vertices(len(rhs),h),'independent cap count violates UBT')
                base.require(all(tuple(z)in W for z in cell['coordinates']),'counting cap lost original prefix vertex')
                deg=any(len(J)>h for J in W.values());outside=0
                for z in W:
                    x=[phase['anchor'][j]+sum(z[i]*cell['columns'][i][j]for i in range(h))for j in range(len(u))]
                    outside+=not base.feasible(A,b,x)
                totals['cap_vertex_enumerations']+=1;totals['cap_active_subsets']+=n;totals['cap_vertices']+=len(W)
                totals['nonsimple_capped_models']+=deg;totals['cap_vertices_outside_original_target_cuts']+=outside
                capchecks.append({'dimension':h,'vertices':len(W),'active_subsets':n,'has_degeneracy':deg,'outside_original':outside})
        record={'name':name,'dimension':len(u),'original_facets':len(A),'missing':audit['missing_target_facets'],
            'raw':audit['original_raw_edges'],'loop_erased':audit['certified_loop_erased_edges'],'shortest':shortest,
            'fallback_macros':raw['fallback_decisions'],'old_bound':audit['old_subset_bound'],
            'new_bound':audit['new_cyclic_phase_bound'],'cap_checks':capchecks}
        results.append(record)
        if len(saved)<10 or audit['missing_target_facets']>=4 or raw['committed_edges']>raw['loop_erased_edges']:
            saved.append((A,b,u,v,c,acc))
        if audit['missing_target_facets']>=4 and len(fixtures)<8:
            fixtures.append({'name':name,'input':{'A':A,'b':b,'start':u,'target':v},'route':c,'account':acc,'report':audit})
        return record
    if stage in ('all','low'):
        for m in (8,12,16,24,32):
            A,b,u,v,F,steps=old.construct_input(m)
            record=test(A,b,u,v,'corridor_'+str(m),enumerate_caps=m<=12)
            record['stacking_graph_distance']=old.reference_distance(F)[0]
        for name,A,b in [('moment3_6',*old.moment3(6)),('moment3_8',*old.moment3(8)),('dodecahedron',*old.dodecahedron())]:
            V,adj,subsets=graph(A,b)
            for u in V:
                for v in V:
                    if u!=v:test(A,b,list(u),list(v),name,(V,adj),enumerate_caps=max_caps>16)
    if stage in ('all','high'):
        # The high-dimensional original graphs are independently reconstructed.
        for d,m in ((4,8),(4,10),(5,10),(5,12)):
            A,b=moment(d,m);V,adj,subsets=graph(A,b)
            pairs=[(u,v)for u in V for v in V if u!=v]
            rng.shuffle(pairs);pairs.sort(key=lambda uv:len(V[uv[0]]&V[uv[1]]))
            for index,(u,v) in enumerate(pairs[:12]):test(A,b,list(u),list(v),f'moment{d}_{m}',(V,adj),enumerate_caps=index<2)
        for d in (3,4,5,6):
            A,b,u,v=hidden(d)
            ref=None
            if d<=4:VV,GG,_=graph(A,b);ref=(VV,GG)
            test(A,b,u,v,f'hidden_{d}',ref,enumerate_caps=True)
        for d,m in ((4,8),(5,7)):
            A,b,target=clipped_moment(d,m);V,adj,subsets=graph(A,b)
            candidates=[x for x in V if x!=tuple(target)]
            candidates.sort(key=lambda x:distances(adj,x)[tuple(target)],reverse=True)
            for index,u in enumerate(candidates[:8]):test(A,b,list(u),list(target),f'clipped_moment{d}_{m}',(V,adj),enumerate_caps=index<2)
        # Three-dimensional tail in high ambient dimension; no product graph enumeration.
        A,b=old.dodecahedron()
        for ambient in (4,8,12):
            AA=[a+[Q(0)]*(ambient-3)for a in A];bb=list(b)
            for i in range(3,ambient):
                AA.extend([[Q(s)*int(i==j)for j in range(ambient)]for s in(-1,1)]);bb.extend([Q(0),Q(1)])
            test(AA,bb,[-Q(5,13)]*3+[Q(0)]*(ambient-3),[Q(5,13)]*3+[Q(0)]*(ambient-3),f'embedded_{ambient}')
    # Search-free consumer and falsifiable binding controls.
    original=(base.invert,base.basis_packet,route.trace_face)
    def disabled(*a,**k):raise AssertionError('account auditor called search')
    base.invert=base.basis_packet=route.trace_face=disabled
    try:
        for A,b,u,v,c,acc in saved[:16]:ledger.audit(A,b,u,v,c,acc);totals['search_disabled_audits']+=1
    finally:base.invert,base.basis_packet,route.trace_face=original
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('accepted invalid certificate '+name)
    A,b,u,v,c,acc=saved[0]
    for name,mut in [('omitted_non_target_row',lambda a:a['cells'][0]['non_target_rows'].pop()),
       ('non_strict_cap',lambda a:a['cells'][0].update(cap=0)),
       ('altered_chart',lambda a:a['cells'][0]['columns'][0].__setitem__(0,Q(123))),
       ('altered_original_vertex',lambda a:a['cells'][0]['vertices'][0].__setitem__(0,Q(123))),
       ('missing_phase',lambda a:a['cells'].pop()),
       ('forged_original_hash',lambda a:a.update(problem_sha256='x')),
       ('changed_cap_inequality',lambda a:a['cells'][0]['cap_row'].__setitem__(0,Q(2))),
       ('wrong_target_deletion',lambda a:a['cells'][0]['locked'].append(c['target_basis']['active'][0])),
       ('repeated_prefix_vertex',lambda a:a['cells'][0]['vertices'].append(a['cells'][0]['vertices'][0]))]:
        bad=deepcopy(acc);mut(bad);reject(name,lambda bad=bad:ledger.audit(A,b,u,v,c,bad))
    # Symbolic combinatorial identities are independently checked over a broad
    # finite parameter range; the note proves them for ALL e.
    for e in range(1,101):
        base.require(sum(ledger.cyclic_vertices(e+1,h)for h in range(1,e+1))==ledger.fib(e+4)-3,'Fibonacci sum identity')
        for r in range(2,e+1):
            oldb=r*((e+2)//2)+sum(comb(e+1,j)for j in range(2,r))
            base.require(ledger.global_bound(e,r)<=oldb,'new bound worsens old subset bound')
    square_controls=[]
    for d in range(3,9):
        AA,bb,uu,vv=hidden(d);count=0
        for free in combinations(range(d),2):
            fixed=[j for j in range(d)if j not in free]
            for bits in product((0,1),repeat=len(fixed)):
                if all(bits):continue
                for vals in product((0,1),repeat=2):
                    x=[Q(0)]*d
                    for i,a in zip(fixed,bits):x[i]=Q(a)
                    for i,a in zip(free,vals):x[i]=Q(a)
                    base.require(base.feasible(AA,bb,x) and all(base.dot(a,x)<t for a,t in zip(AA[2*d:],bb[2*d:])), 'target-free square not retained')
                count+=1
        base.require(count==comb(d,2)*(2**(d-2)-1),'exponential face inventory count')
        square_controls.append({'dimension':d,'original_facets':3*d,'relaxed_facets':2*d,
            'relaxed_cube_vertices':2**d,'target_free_squares':count,'all_square_q_minus_one':3*count})
    bounds=[{'e':e,'r':r,'new':ledger.global_bound(e,r),
             'old':r*((e+2)//2)+sum(comb(e+1,j)for j in range(2,r))}
             for e,r in ((12,4),(12,5),(12,12),(20,20),(29,3),(29,4),(29,5))]
    report={'status':'PASS','scope':'Written UBT-based target-deletion bound; exact Python only, no Lean/platform verdict.',
        'stage':stage,'totals':totals,'routes':results,'negative_controls':rejected,
        'bounds':bounds,'inventory_boundary':square_controls,'binomial_identity_excesses_checked':100,
        'seconds':round(time.monotonic()-start,3),
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/f'research/TARGET_DELETED_PHASE_{stage.upper()}_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/f'fixtures/target_deleted_{stage}_examples.json').write_text(json.dumps(base.serial(fixtures),indent=2)+'\n')
    print(json.dumps({'status':'PASS','stage':stage,'totals':totals,'bounds':bounds,'negative':len(rejected),'seconds':report['seconds']},indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['all','low','high'],default='all');a=p.parse_args();main(a.stage)
