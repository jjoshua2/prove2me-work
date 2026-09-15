#!/usr/bin/env python3
"""Exact original-H segment tests with independently reconstructed small graphs.

Flagness is established independently for the listed small models, not inferred
from a lucky route. Large cases have an explicit invertible cube presentation.
The production router receives ONLY A,b,start,target. No graph is passed to it.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations,product
from collections import deque
from copy import deepcopy
from pathlib import Path
import argparse,hashlib,json,random,time
import sympy as sp
import original_facet_segments as seg
import facet_reentry_repair as repair
import simple_tangent_policy_audit as base
import two_face_acquisition as old
ROOT=Path(__file__).resolve().parents[1]


def cube(d):
    return [[Q(s*(i==j))for j in range(d)]for i in range(d)for s in(-1,1)],[Q(1)]*(2*d)


def moment(d,n):
    V=[[Q(i)**j for j in range(1,d+1)]for i in range(n)]
    c=[sum(v[j]for v in V)/n for j in range(d)]
    return [[v[j]-c[j]for j in range(d)]for v in V],[Q(1)]*n


def dodecahedron():
    A=[]
    for a,b in product((-Q(1),Q(1)),repeat=2):
        A.extend([[Q(0),a,Q(8,5)*b],[a,Q(8,5)*b,Q(0)],[Q(8,5)*b,Q(0),a]])
    return A,[Q(1)]*12


def reference(A,b):
    """ALL active-subsets using independent SymPy elimination, only small inputs."""
    d=len(A[0]);m=len(A);V={};subsets=0
    for I in combinations(range(m),d):
        M=sp.Matrix([A[i]for i in I]);subsets+=1
        if M.det()==0:continue
        x=tuple(Q(str(z))for z in M.inv()*sp.Matrix([b[i]for i in I]))
        if base.feasible(A,b,x):V[x]=frozenset(base.active_rows(A,b,x))
    seg.require(V and all(len(F)==d for F in V.values()),'not a simple bounded reference')
    # Independent strict facet witnesses; counts are genuine original facets.
    facet_anchors=[]
    for i in range(m):
        pts=[x for x,F in V.items()if i in F]
        seg.require(pts,'empty claimed facet')
        mean=tuple(sum(x[j]for x in pts)/len(pts)for j in range(d))
        seg.require(base.active_rows(A,b,mean)==[i],'row is not a genuine distinct facet')
        seg.require(sp.Matrix([[x[j]-pts[0][j]for j in range(d)]for x in pts[1:]]).rank()==d-1,
                    'reference facet has wrong affine dimension')
        facet_anchors.append(mean)
    adj={x:[]for x in V}
    for x,y in combinations(V,2):
        if len(V[x]&V[y])==d-1:adj[x].append(y);adj[y].append(x)
    seg.require(all(len(ns)==d for ns in adj.values()),'incorrect original reference degree')
    D={}
    for u in V:
        dd={u:0};q=deque([u])
        while q:
            x=q.popleft()
            for y in adj[x]:
                if y not in dd:dd[y]=dd[x]+1;q.append(y)
        seg.require(len(dd)==len(V),'disconnected small reference')
        D[u]=dd
    # Explicit finite global flagness test via ALL cliques through size d+1.
    # Larger cliques contain a forbidden d+1 clique, so this is complete.
    Fs=list(V.values());pairs={p for p in combinations(range(m),2)if any(set(p)<=F for F in Fs)}
    missing=[];cliques=0
    for size in range(3,min(d+1,m)+1):
        for S in combinations(range(m),size):
            if all(p in pairs for p in combinations(S,2)):
                cliques+=1
                if not any(set(S)<=F for F in Fs):missing.append(S)
    return V,adj,D,{'active_subsets':subsets,'vertices':len(V),'edges':sum(map(len,adj.values()))//2,
             'genuine_facet_anchors':m,'global_flag':not missing,'cliques_checked':cliques,
             'first_missing_clique':list(missing[0])if missing else None}


def truncated_cube(d,cuts):
    A,b=cube(d);history=[]
    for pair in cuts:
        V,_,_,_=reference(A,b)
        seg.require(any(set(pair)<=F for F in V.values()),'chosen codimension-two face absent')
        f=[sum(A[i][j]for i in pair)for j in range(d)];bb=sum(b[i]for i in pair)
        delta=min(bb-seg.dot(f,x)for x in V if bb-seg.dot(f,x)>0)/3
        history.append({'rows':list(pair),'cut_depth':str(delta)})
        A.append(f);b.append(bb-delta)
    return A,b,history


def decoded(raw):return old.decode(raw)


def audit_output(data,out):
    c=out['certificate'];r=seg.verify(data,c)
    seg.require(r==out['verified'],'report not exactly derived from certificate')
    if out['obstruction']['status']=='witness':
        A,b,_,_=seg.parse(data);seg.verify_obstruction(A,b,c['intersections'],out['obstruction'])
        seg.require(out['obstruction']['reentered_facet']==r['reentries'][0]['facet'],'obstruction is not linked to first actual reentry')
    return r


def model_run(name,A,b,pair_limit,expected_flag,fixtures):
    V,adj,D,info=reference(A,b);d=len(A[0]);m=len(A)
    seg.require(info['global_flag']==expected_flag,'wrong independent flag classification')
    pairs=[(u,v)for u in V for v in V if u!=v]
    all_count=len(pairs)
    if pair_limit and len(pairs)>pair_limit:
        random.Random(815+m+d).shuffle(pairs);pairs=pairs[:pair_limit]
    totals={'model':name,'dimension':d,'original_facets':m,**info,'all_ordered_pairs':all_count,
       'executed_pairs':0,'new_original_edges':0,'reference_253_edges':0,'shortest_edges':0,
       'new_nonshortest':0,'old_nonshortest':0,'new_wins':0,'new_losses':0,
       'revisiting_routes':0,'reentry_debt':0,'over_m_minus_d_routes':0,
       'diagnostic_missing_triangles':0,'diagnostic_caps_or_absence':0,
       'lp_maximizations':0,'simplex_pivots':0,'intersection_queries':0,'visited_link_graphs':0,
       'max_route_edges':0,'max_recursive_calls':0,'repaired_edges':0,'accepted_repairs':0,
       'repair_trials':0,'repaired_nonshortest':0,'remaining_reentry_debt':0}
    saved_nonshort=saved_bad=saved_over=False;saved=[]
    for n,(u,v)in enumerate(pairs):
        data={'A':A,'b':b,'start':u,'target':v};o=seg.construct(data);r=audit_output(data,o)
        cert=o['certificate'];P=[tuple(map(Q,p['point']))for p in cert['vertices']]
        byfacet={tuple(p['active']):tuple(map(Q,p['point']))for p in cert['vertices']}
        path=[byfacet[tuple(f)]for f in cert['path']]
        seg.require(all(y in adj[x]for x,y in zip(path,path[1:])), 'not an independent original edge')
        dist=D[u][v];ref=old.construct(A,b,list(u),list(v))['verified']['loop_erased_edges']
        L=r['original_edges'];R=r['reentry_debt']
        rr=repair.construct(data,o);vr=repair.verify(data,rr['certificate'])
        seg.require(vr==rr['verified'],'repair report mismatch')
        rp=[tuple(map(seg.rat,x))for x in vr['path']]
        seg.require(all(y in adj[x]for x,y in zip(rp,rp[1:])), 'repaired edge not in independent graph')
        totals['repaired_edges']+=vr['original_edges'];totals['accepted_repairs']+=vr['accepted_repairs']
        totals['repair_trials']+=len(rr['trials']);totals['repaired_nonshortest']+=vr['original_edges']>dist
        totals['remaining_reentry_debt']+=vr['reentry_debt']
        if expected_flag:seg.require(R==0 and L<=m-d,'classical flag nonrevisiting guarantee failed')
        totals['executed_pairs']+=1;totals['new_original_edges']+=L;totals['reference_253_edges']+=ref;totals['shortest_edges']+=dist
        totals['new_nonshortest']+=L>dist;totals['old_nonshortest']+=ref>dist
        totals['new_wins']+=L<ref;totals['new_losses']+=L>ref
        totals['revisiting_routes']+=R>0;totals['reentry_debt']+=R;totals['over_m_minus_d_routes']+=L>m-d
        totals['diagnostic_missing_triangles']+=o['obstruction']['status']=='witness'
        totals['diagnostic_caps_or_absence']+=R>0 and o['obstruction']['status']!='witness'
        for f in('lp_maximizations','simplex_pivots'):totals[f]+=o['discovery_work'][f]
        for f in('intersection_queries','visited_link_graphs'):totals[f]+=r[f]
        totals['max_route_edges']=max(totals['max_route_edges'],L);totals['max_recursive_calls']=max(totals['max_recursive_calls'],r['recursive_calls'])
        save=(n==0 or (L>dist and not saved_nonshort)or(R>0 and not saved_bad)or(L>m-d and not saved_over))
        if save:
            record={'model':name,'input':seg.serial(data),'output':o,'repair':rr,'bfs_distance':dist,'reference_253_edges':ref}
            fixtures.append(record);saved.append((data,o))
        saved_nonshort|=L>dist;saved_bad|=R>0;saved_over|=L>m-d
    return totals,saved


def stage_small(stage):
    fixtures=[];saved=[];reports=[];start=time.monotonic()
    if stage=='flag':
        A,b=cube(3);models=[('cube3',A,b,0,True)]
        A,b,h=truncated_cube(3,[(0,2),(2,4),(0,4),(6,7)]);models.append(('overlapping_edge_truncations3',A,b,0,True))
        A,b=dodecahedron();models.append(('rational_dodecahedron',A,b,0,True))
        A,b,h=truncated_cube(4,[(0,2),(2,4),(0,4)]);models.append(('overlapping_ridge_truncations4',A,b,80,True))
    else:
        models=[]
        for d,n,cap in[(3,6,0),(3,8,0),(4,8,0),(5,9,100)]:
            A,b=moment(d,n);models.append((f'moment_polar_{d}_{n}',A,b,cap,False))
    for name,A,b,cap,flag in models:
        r,s=model_run(name,A,b,cap,flag,fixtures);reports.append(r);saved+=s
        print('finished',name,r,flush=True)
    out={'status':'PASS','scope':'Exact original H discovery and independent small reference graphs; not Lean verification',
       'stage':stage,'models':reports,'seconds':round(time.monotonic()-start,3)}
    return out,fixtures,saved


def stage_large():
    start=time.monotonic();reports=[];fixtures=[];saved=[]
    for d in(6,8,12,16):
        A,b=cube(d);data={'A':A,'b':b,'start':[-Q(1)]*d,'target':[Q(1)]*d}
        o=seg.construct(data);r=audit_output(data,o);seg.require(r['original_edges']==d and r['nonrevisiting'],'cube endpoint count')
        reports.append({'class':'cube','dimension':d,'known_vertices':2**d,'full_graph_enumerated':False,**r,**o['discovery_work']})
        if d in(6,16):fixtures.append({'model':f'cube{d}','input':seg.serial(data),'output':o});saved.append((data,o))
        print('large cube',d,r['original_edges'],r['intersection_queries'],flush=True)
    # Known corridor constructors from #254: unchanged source imports, not new families.
    from test_weighted_face_retirement import construct_input,reference_distance
    for m in(8,12,16,24):
        A,b,u,v,F,_=construct_input(m);data={'A':A,'b':b,'start':u,'target':v}
        o=seg.construct(data);r=audit_output(data,o);dist,adj=reference_distance(F)
        seg.require(all(tuple(y)in adj[tuple(x)]for x,y in zip(o['certificate']['path'],o['certificate']['path'][1:])),
                    'corridor edge outside exact stacking incidence')
        other=old.construct(A,b,u,v)['verified']['loop_erased_edges']
        reports.append({'class':'attributed_stacked_polar','original_facets':m,'bfs_distance':dist,
                        'reference_253_edges':other,**r,**o['discovery_work']})
        fixtures.append({'model':f'corridor{m}','input':seg.serial(data),'output':o});saved.append((data,o))
        print('corridor',m,r['original_edges'],r['reentry_debt'],dist,flush=True)
    # Invertible dense affine coordinate chart plus independent positive row scaling.
    A,b,h=truncated_cube(3,[(0,2),(2,4),(0,4)])
    V,adj,D,info=reference(A,b);us=list(V);pairs=[(us[i],us[-1-i])for i in range(6)]
    matrix=sp.Matrix([[1,2,1],[0,1,1],[1,0,1]]);inv=matrix.inv();det=matrix.det();seg.require(det!=0,'singular affine control')
    tr=(Q(2),Q(-1),Q(3));affines=0;scalings=0
    for idx,(u,v)in enumerate(pairs):
        data={'A':A,'b':b,'start':u,'target':v};o=seg.construct(data)
        newA=[[sum(a[k]*Q(str(inv[k,j]))for k in range(3))for j in range(3)]for a in A]
        newb=[bb+seg.dot(a,tr)for a,bb in zip(newA,b)]
        def tf(x):return [sum(Q(int(matrix[j,k]))*x[k]for k in range(3))+tr[j]for j in range(3)]
        dd={'A':newA,'b':newb,'start':tf(u),'target':tf(v)};oo=seg.construct(dd)
        seg.require(oo['certificate']['path']==o['certificate']['path'],'affine chart changed label-only route');affines+=1
        for t in range(2):
            scales=[Q((i+2)**(t+1),i+1)for i in range(len(A))]
            qd={'A':[[s*z for z in a]for s,a in zip(scales,A)],'b':[s*z for s,z in zip(scales,b)],'start':u,'target':v}
            qo=seg.construct(qd);seg.require(qo['certificate']['path']==o['certificate']['path'],'positive row scaling changed route');scalings+=1
        saved.append((dd,oo))
    out={'status':'PASS','stage':'large','scope':'Explicit families and original-row certificates; no large graph enumeration or Lean claim',
         'models':reports,'affine_label_path_comparisons':affines,'positive_row_scaling_comparisons':scalings,
         'seconds':round(time.monotonic()-start,3)}
    return out,fixtures,saved


def controls(saved):
    count=0;oldvalues=(seg.lp.ExactLP,base.invert,base.basis_packet)
    def forbidden(*a,**kw):raise AssertionError('route audit invoked LP or inverse production')
    seg.lp.ExactLP=base.invert=base.basis_packet=forbidden
    try:
        for data,o in saved:audit_output(data,json.loads(json.dumps(o)));count+=1
    finally:seg.lp.ExactLP,base.invert,base.basis_packet=oldvalues
    A,b=cube(3);data={'A':A,'b':b,'start':[-1]*3,'target':[1]*3};out=seg.construct(data);c=out['certificate'];badnames=[]
    present=next(i for i,x in enumerate(c['intersections'])if x['kind']=='present')
    absent=next(i for i,x in enumerate(c['intersections'])if x['kind']=='absent')
    def reject(name,func):
        try:func()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):badnames.append(name)
        else:raise AssertionError('forged or capped work passed: '+name)
    edits=[('missing_intersection',lambda x:x['intersections'].clear()),
        ('false_present_point',lambda x:x['intersections'][present].update(point=[99,99,99])),
        ('false_exclusion_bound',lambda x:x['intersections'][absent].update(bound='-999')),
        ('false_exclusion_dual',lambda x:x['intersections'][absent].update(dual=[[0,'999']])),
        ('missing_coordinate_bound',lambda x:x['boundedness'].pop()),
        ('wrong_path',lambda x:x['path'].pop()),
        ('wrong_recursion_record',lambda x:x['events'][0].update(kind='fake')),
        ('wrong_inverse',lambda x:x['vertices'][0]['directions'][0].__setitem__(0,99)),
        ('input_binding',lambda x:x.update(problem_sha256='00')),
        ('repeated_query',lambda x:x['intersections'].append(deepcopy(x['intersections'][0]))),
        ('noninteger_label',lambda x:x['path'][0].__setitem__(0,True))]
    for name,f in edits:
        cc=deepcopy(c);f(cc);reject(name,lambda cc=cc:seg.verify(data,cc))
    reject('edge_cap',lambda:seg.construct(data,edge_cap=1))
    reject('node_cap',lambda:seg.construct(data,node_cap=1))
    reject('query_cap',lambda:seg.construct(data,query_cap=1))
    # A true reentry from the nonflag reference also gives a checked missing triangle.
    A,b=moment(3,8);V,_,_,_=reference(A,b);u=next(x for x,F in V.items()if F=={0,1,2});v=next(x for x,F in V.items()if F=={3,4,7})
    data={'A':A,'b':b,'start':u,'target':v};o=seg.construct(data);seg.require(o['verified']['reentry_debt']>0 and o['obstruction']['status']=='witness','negative control lacks actual defect')
    obs=deepcopy(o['obstruction']);obs['triangle']=[0,1,2]
    reject('filled_triangle_as_obstruction',lambda:seg.verify_obstruction(A,b,o['certificate']['intersections'],obs))
    rr=repair.construct(data,o);saved_values=(seg.lp.ExactLP,base.invert,base.basis_packet,old.construct)
    seg.lp.ExactLP=base.invert=base.basis_packet=old.construct=forbidden
    try:repair.verify(data,rr['certificate'])
    finally:seg.lp.ExactLP,base.invert,base.basis_packet,old.construct=saved_values
    bad=deepcopy(rr['certificate']);bad['repairs'][0]['facet']=99
    reject('wrong_repair_facet',lambda:repair.verify(data,bad))
    bad2=deepcopy(rr['certificate']);bad2['repairs'][0]['end_index']=1
    reject('non_excursion_splice',lambda:repair.verify(data,bad2))
    return {'search_disabled_route_audits':count,'search_disabled_repair_audits':1,'negative_controls':badnames,'negative_count':len(badnames)}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--stage',choices=['flag','nonflag','large'],required=True);a=p.parse_args()
    result,fixtures,saved=stage_large()if a.stage=='large'else stage_small(a.stage)
    result.update(controls(saved));result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted((ROOT/'scripts').glob('*.py'))if not p.name.startswith('_')}
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    (ROOT/f'research/ORIGINAL_FACET_SEGMENTS_{a.stage.upper()}_TESTS.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    (ROOT/f'fixtures/original_facet_segments_{a.stage}.json').write_text(json.dumps(seg.serial(fixtures),sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
