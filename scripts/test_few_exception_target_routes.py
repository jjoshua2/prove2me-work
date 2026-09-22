#!/usr/bin/env python3
"""Exact tests of original-row codes and target-locking routes, not Lean verification.

Small references enumerate finite hulls independently. The route producer calls
unchanged #322 geometry, never its edge table. The consumer uses that independent
reference to verify entire support slices, code rank and original edges. Large
multi-roof instances use explicit sparse right inverses, without graph discovery.
"""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path
import sympy as sp
import test_geometric_coordinate_routes as g
import test_target_two_level_routes as old


def bad_rows(model, rows, v):
    return {i for i in old.active(rows, model['vertices'][v])
            if len({g.dot(rows[i][:-1], x) for x in model['vertices']}) > 2}


def check_B(model, rows, v, B):
    if len(set(B)) != len(B): raise ValueError('duplicate exception label')
    if not set(B) <= set(range(len(rows))):
        raise ValueError('exception label outside original rows')
    if not bad_rows(model, rows, v) <= set(B):
        raise ValueError('a good target row has more than two levels')


def residual_code(model, rows, v, B):
    """Select original active labels; no catalogue-size/rank certificate is input."""
    check_B(model, rows, v, B)
    V=model['vertices']; d=len(V[0]); target=old.active(rows, V[v]); G=target-set(B)
    D=[i for i,x in enumerate(V) if G <= old.active(rows,x)]
    base=[rows[i][:-1] for i in sorted(G)]; rankG=g.rank(base); r=d-rankG
    if r>len(B): raise AssertionError('derived residual rank bound failed')
    codes=[]
    for x in D:
        selected=[]; current=list(base); rk=rankG
        for i in sorted(old.active(rows,V[x])):
            nr=g.rank(current+[rows[i][:-1]])
            if nr>rk:
                selected.append(i);current.append(rows[i][:-1]);rk=nr
        if rk!=d or len(selected)!=r: raise AssertionError('active-row selection failed')
        codes.append(dict(vertex=x,selected=selected,slots=selected+[None]*(len(B)-len(selected))))
    return dict(target=v,exceptions=sorted(B),good=sorted(G),vertices=D,
                direction_dimension=r,codes=codes,bound=(len(rows)+1)**len(B))


def check_code(model,rows,c):
    V=model['vertices'];d=len(V[0]);m=len(rows);v=c['target'];B=c['exceptions']
    check_B(model,rows,v,B)
    G=old.active(rows,V[v])-set(B)
    D=[i for i,x in enumerate(V) if G<=old.active(rows,x)]
    if c['good']!=sorted(G) or c['vertices']!=D: raise ValueError('incomplete residual face')
    base=[rows[i][:-1] for i in sorted(G)];r=d-g.rank(base)
    if c['direction_dimension']!=r or r>len(B): raise ValueError('wrong derived dimension')
    if c['bound']!=(m+1)**len(B): raise ValueError('wrong original-label bound')
    if [z['vertex'] for z in c['codes']]!=D: raise ValueError('missing residual vertex code')
    seen=set()
    for z in c['codes']:
        x=z['vertex'];S=z['selected'];slots=z['slots']
        if S!=sorted(set(S)) or len(S)>r or not set(S)<=old.active(rows,V[x]):
            raise ValueError('invalid selected active labels')
        if g.rank(base+[rows[i][:-1] for i in S])!=d: raise ValueError('selected rows fail separation')
        if len(slots)!=len(B) or slots!=S+[None]*(len(B)-len(S)):
            raise ValueError('invalid original-label slots')
        if tuple(slots) in seen: raise ValueError('duplicate vertex code')
        seen.add(tuple(slots))
    if len(D)>c['bound']: raise ValueError('code count exceeded')
    return True


def produce(model,rows,u,v,c):
    V=model['vertices'];T=old.active(rows,V[v]);G=set(c['good'])
    path=[u];records=[];prefix=0
    score=tuple(sum((rows[i][j] for i in T),Q(0)) for j in range(len(V[0])))
    while path[-1]!=v:
        x=path[-1];before=old.active(rows,V[x])&T;missing=G-before
        chosen=min(missing) if missing else None
        f=rows[chosen][:-1] if chosen is not None else score
        F=frozenset(i for i,z in enumerate(V) if before<=old.active(rows,z))
        y,edge=g.improving_edge(model,F,x,f)
        after=old.active(rows,V[y])&T
        if not before<=after: raise AssertionError('lost target lock')
        if chosen is not None:
            if chosen not in after: raise AssertionError('two-level acquisition failed')
            prefix+=1
        records.append(dict(edge=edge,chosen_good=chosen,before=sorted(before),after=sorted(after)))
        path.append(y)
        if len(path)>len(V)+len(G)+1: raise AssertionError('finite progress failed')
    return dict(u=u,v=v,path=path,records=records,prefix_length=prefix,
                displayed_rows=len(rows),ambient_dimension=len(V[0]))


def consume(model,rows,c,cert):
    V=model['vertices'];d=len(V[0]);m=len(rows);u=cert['u'];v=cert['v'];p=cert['path']
    if v!=c['target'] or not 0<=u<len(V): raise ValueError('wrong endpoint')
    if cert['displayed_rows']!=m or cert['ambient_dimension']!=d: raise ValueError('wrong original size')
    if not p or p[0]!=u or p[-1]!=v or any(i not in range(len(V)) for i in p):
        raise ValueError('wrong path endpoints')
    if len(cert['records'])!=len(p)-1: raise ValueError('wrong record count')
    T=old.active(rows,V[v]);G=set(c['good']);D=set(c['vertices'])
    score=tuple(sum((rows[i][j] for i in T),Q(0)) for j in range(d))
    prefix=0;entered=False;terminal=[]
    for a,rec in enumerate(cert['records']):
        x,y=p[a:a+2];before=old.active(rows,V[x])&T;after=old.active(rows,V[y])&T
        if not before<=after: raise ValueError('lost target row')
        if rec['before']!=sorted(before) or rec['after']!=sorted(after): raise ValueError('false tight labels')
        goodMissing=G-before;j=rec['chosen_good']
        if goodMissing:
            if entered or j not in goodMissing or j not in after: raise ValueError('good acquisition failure')
            f=rows[j][:-1];prefix+=1
        else:
            entered=True
            if j is not None or x not in D or y not in D: raise ValueError('residual phase failure')
            f=score;terminal.append(x)
        edge=rec['edge'];F={i for i,z in enumerate(V) if before<=old.active(rows,z)}
        if edge['u']!=x or edge['v']!=y or set(edge['face'])!=F: raise ValueError('incomplete retained face')
        if tuple(Q(z) for z in edge['objective'])!=f: raise ValueError('wrong objective')
        g.verify_record(model,edge)
    terminal.append(v)
    if len(terminal)!=len(set(terminal)): raise ValueError('residual ascent repeated a vertex')
    if prefix!=cert['prefix_length'] or prefix>len(G-old.active(rows,V[u])) or prefix>m-d:
        raise ValueError('prefix count failed')
    if len(p)-1-prefix>len(D)-1: raise ValueError('residual count failed')
    if len(p)-1>m-d+c['bound']-1: raise ValueError('original-input bound failed')
    return True


def roof_points(n,k):
    return [tuple(map(Q,x))+tuple(Q(s)*(1+sum((Q((a+1)*x[j],2**(j+1)) for j in range(n)),Q(0)))
            for a,s in enumerate(flags))
            for x in product(range(2),repeat=n) for flags in product(range(2),repeat=k)]


def small(out,only='all'):
    cases=old.cases()+[(f'multi_roof_{n}_{k}',roof_points(n,k),False)
                        for n,k in [(1,2),(2,2),(1,3)]]
    cases += [('dense_multi_roof',old.transform(roof_points(1,2)),False),
              ('two_exception_hexagon',[(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)],False)]
    reports=[];fixtures=[]
    for name,points,extra in cases:
        if only!='all' and name!=only: continue
        model=g.reference(points);rows=old.h_rows(model);V=model['vertices'];d=len(V[0])
        if extra: rows=list(reversed(rows))+[rows[0],tuple([Q(0)]*d+[Q(1)])]
        old.validate_h(model,rows)
        allcodes=[];routes=[];edges=shortest=nonshortest=no_acquisition=residual_edges=0
        new_targets=0;maxk=0;code_vertices=0
        for v in range(len(V)):
            B=bad_rows(model,rows,v);new_targets+=len(B)>1;maxk=max(maxk,len(B))
            c=residual_code(model,rows,v,B);check_code(model,rows,c);allcodes.append(c)
            code_vertices+=len(c['vertices'])
            for u in range(len(V)):
                cert=produce(model,rows,u,v,c);consume(model,rows,c,cert);routes.append(cert)
                L=len(cert['path'])-1;dist=old.distances(model,u)[v]
                edges+=L;shortest+=dist;nonshortest+=L>dist;residual_edges+=L-cert['prefix_length']
                no_acquisition+=sum(r['before']==r['after'] for r in cert['records'])
        # Replay all stored consumers without allowing route or edge production.
        maker=globals()['produce'];edge_maker=g.improving_edge
        def disabled(*args,**kwargs): raise RuntimeError('producer disabled')
        globals()['produce']=disabled;g.improving_edge=disabled
        try:
            for c in allcodes: check_code(model,rows,c)
            for cert in routes: consume(model,rows,allcodes[cert['v']],cert)
        finally: globals()['produce']=maker;g.improving_edge=edge_maker
        controls=[]
        if V:
            allB=set(range(len(rows)))
            c=residual_code(model,rows,0,allB);check_code(model,rows,c)
            cert=produce(model,rows,len(V)-1,0,c);consume(model,rows,c,cert)
            controls.append(dict(kind='all_original_rows_exceptional',code=c,route=cert))
        result=dict(name=name,ambient_dimension=d,generators=len(model['points']),vertices=len(V),
                    rows=len(rows),targets=len(V),new_targets_beyond_one_exception=new_targets,
                    maximum_exceptions=maxk,certified_residual_vertex_codes=code_vertices,
                    routes=len(routes),edges=edges,shortest_edges=shortest,nonshortest_routes=nonshortest,
                    residual_edges=residual_edges,steps_without_new_target_row=no_acquisition)
        if name=='two_exception_hexagon':
            u=V.index((Q(0),Q(0)));v=V.index((Q(2),Q(2)))
            result['explicit_countercontrol']=dict(distance=old.distances(model,u)[v],
                initially_missing_target_rows=len(old.active(rows,V[v])-old.active(rows,V[u])),
                acquiring_source_neighbors=[j for i,j in sorted(model['edges']) if i==u
                    and (old.active(rows,V[j])&old.active(rows,V[v]))-old.active(rows,V[u])]
                                +[i for i,j in sorted(model['edges']) if j==u
                    and (old.active(rows,V[i])&old.active(rows,V[v]))-old.active(rows,V[u])])
            assert result['explicit_countercontrol']==dict(distance=3,initially_missing_target_rows=2,acquiring_source_neighbors=[])
        reports.append(result);fixtures.append(dict(name=name,points=model['points'],rows=rows,
                                    residual_codes=allcodes,routes=routes,boundary_controls=controls))
        print(json.dumps(result),flush=True)
    out.mkdir(parents=True,exist_ok=True)
    (out/'small-report.json').write_text(json.dumps(dict(kind='exact_supporting_tests_not_Lean',models=reports),indent=2)+'\n')
    (out/'small-fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')


def roof_rows(n,k):
    d=n+k;rows=[]
    for i in range(n):
        e=tuple(Q(int(i==j)) for j in range(d));rows += [tuple(-z for z in e)+(Q(0),),e+(Q(1),)]
    for a in range(k):
        lo=tuple(Q(-int(j==n+a)) for j in range(d))+(Q(0),)
        hi=tuple(-Q(a+1,2**(j+1)) for j in range(n))+tuple(Q(int(b==a)) for b in range(k))+(Q(1),)
        rows += [lo,hi]
    return rows


def roof_vertex(bits,flags):
    n=len(bits)
    return tuple(map(Q,bits))+tuple(Q(s)*(1+sum((Q((a+1)*bits[j],2**(j+1)) for j in range(n)),Q(0)))
                                  for a,s in enumerate(flags))


def explicit_inverse(bits,flags):
    n=len(bits);k=len(flags);d=n+k
    R=[[Q(0) for _ in range(d)] for _ in range(d)]
    for i,b in enumerate(bits): R[i][i]=Q(2*b-1)
    for a,s in enumerate(flags):
        R[n+a][n+a]=Q(2*s-1)
        if s:
            for i,b in enumerate(bits): R[n+a][i]=Q((a+1)*(2*b-1),2**(i+1))
    return R


def check_identity(A,R):
    n=len(A);d=len(R)
    if any(len(row)!=d for row in A) or any(len(row)!=n for row in R): raise ValueError('inverse shape')
    for i,row in enumerate(A):
        sparse=[(j,a) for j,a in enumerate(row) if a]
        for k in range(n):
            if sum((a*R[j][k] for j,a in sparse),Q(0))!=int(i==k):
                raise ValueError('right-inverse identity failed')
    return n*n


def make_large(n,k):
    bits=[1]*n;flags=[1]*k;states=[dict(bits=list(bits),flags=list(flags),point=roof_vertex(bits,flags))]
    for i in range(n):
        bits[i]=0;states.append(dict(bits=list(bits),flags=list(flags),point=roof_vertex(bits,flags)))
    for a in range(k):
        flags[a]=0;states.append(dict(bits=list(bits),flags=list(flags),point=roof_vertex(bits,flags)))
    return dict(n=n,k=k,rows=roof_rows(n,k),states=states,exceptional_level_count=2**n+1)


def audit_large(c):
    n=c['n'];k=c['k'];d=n+k;rows=[tuple(map(Q,r)) for r in c['rows']];states=c['states']
    if n<1 or k<2 or rows!=roof_rows(n,k): raise ValueError('invalid multi-roof input')
    if c['exceptional_level_count']!=2**n+1: raise ValueError('incorrect level-count formula')
    points=[];act=[];inverses=[];ids=0;rowchecks=0
    for s in states:
        x=tuple(map(Q,s['point']));bits=s['bits'];flags=s['flags']
        if len(bits)!=n or len(flags)!=k or any(b not in (0,1) for b in bits+flags): raise ValueError('invalid Boolean lift')
        if x!=roof_vertex(bits,flags): raise ValueError('wrong lifted vertex')
        if any(g.dot(row[:-1],x)>row[-1] for row in rows): raise ValueError('infeasible point')
        I=[2*i+b for i,b in enumerate(bits)]+[2*n+2*a+s for a,s in enumerate(flags)]
        if old.active(rows,x)!=set(I): raise ValueError('incorrect full tight labels')
        R=explicit_inverse(bits,flags);ids+=check_identity([rows[i][:-1] for i in I],R)
        points.append(x);act.append(I);inverses.append(R);rowchecks+=len(rows)
    if points[0]!=roof_vertex([1]*n,[1]*k) or points[-1]!=roof_vertex([0]*n,[0]*k): raise ValueError('wrong endpoints')
    target=set(act[-1]);no_new=0
    for a,(x,y) in enumerate(zip(points,points[1:])):
        if x==y: raise ValueError('stationary edge')
        I=act[a];common=set(I)&set(act[a+1]);before=set(I)&target;after=set(act[a+1])&target
        if len(common)!=d-1 or not before<=after: raise ValueError('edge/common rank or target locking')
        no_new+=before==after
        kept=[j for j,i in enumerate(I) if i in common]
        R=[[row[j] for j in kept] for row in inverses[a]]
        ids+=check_identity([rows[I[j]][:-1] for j in kept],R)
        # These private endpoint bounds cut the common affine line at BOTH ends.
        ip=next(iter(set(I)-common));jp=next(iter(set(act[a+1])-common))
        if not g.dot(rows[ip][:-1],y)<rows[ip][-1] or not g.dot(rows[jp][:-1],x)<rows[jp][-1]:
            raise ValueError('common line not bounded by the endpoints')
    if len(states)-1>d: raise ValueError('explicit family path too long')
    return dict(dimension=d,exceptions=k,rows=len(rows),edges=len(states)-1,
        exception_levels_formula=2**n+1,residual_dimension_formula=k,residual_vertices_formula=2**k,
        theorem_bound=d+(2*d+1)**k-1,original_row_checks=rowchecks,right_inverse_identities=ids,
        steps_without_new_target_row=no_new)


def large(out):
    fixtures=[make_large(d-k,k) for d,k in [(8,2),(16,2),(32,3),(64,4)]]
    reports=[audit_large(c) for c in fixtures]
    maker=globals()['make_large'];globals()['make_large']=lambda *a: (_ for _ in ()).throw(RuntimeError('producer disabled'))
    try:
        assert reports==[audit_large(c) for c in fixtures]
    finally: globals()['make_large']=maker
    out.mkdir(parents=True,exist_ok=True)
    (out/'large-report.json').write_text(json.dumps(dict(kind='explicit_exact_family_certificates_not_Lean_instances',models=reports),indent=2)+'\n')
    (out/'large-fixtures.json').write_text(json.dumps(g.encoded(fixtures),indent=2)+'\n')
    print(json.dumps(reports),flush=True)


def negative(out):
    model=g.reference([(0,0),(2,0),(3,1),(2,2),(0,2),(-1,1)]);rows=old.h_rows(model);V=model['vertices']
    u=V.index((Q(0),Q(0)));v=V.index((Q(2),Q(2)));B=bad_rows(model,rows,v)
    c=residual_code(model,rows,v,B);p=produce(model,rows,u,v,c)
    cases=[]
    for name,edit in [
        ('omitted_bad_row',lambda x:x['exceptions'].pop()),
        ('missing_residual_vertex',lambda x:x['vertices'].pop()),
        ('wrong_dimension',lambda x:x.update(direction_dimension=0)),
        ('nonseparating_rows',lambda x:x['codes'][0].update(selected=[],slots=[None]*len(B))),
        ('missing_code',lambda x:x['codes'].pop()),
        ('incorrect_slot',lambda x:x['codes'][0]['slots'].__setitem__(0,len(rows))),
        ('false_count_bound',lambda x:x.update(bound=1)),
    ]:
        x=deepcopy(c);edit(x)
        try:check_code(model,rows,x)
        except (ValueError,AssertionError):cases.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted corrupted code '+name)
    for name,edit in [
        ('false_prefix',lambda x:x.update(prefix_length=100)),
        ('wrong_endpoint',lambda x:x['path'].__setitem__(-1,u)),
        ('zero_support',lambda x:x['records'][0]['edge'].update(support=(Q(0),Q(0)))),
        ('false_acquired_labels',lambda x:x['records'][0].update(after=[len(rows)])),
    ]:
        x=deepcopy(p);edit(x)
        try:consume(model,rows,c,x)
        except (ValueError,AssertionError):cases.append(dict(name=name,rejected=True))
        else:raise AssertionError('accepted corrupted route '+name)
    q=make_large(2,2);q['states'][1]['point']=q['states'][0]['point']
    try:audit_large(q)
    except (ValueError,AssertionError):cases.append(dict(name='false_large_vertex',rejected=True))
    else:raise AssertionError('accepted corrupted family')
    out.mkdir(parents=True,exist_ok=True)
    (out/'negative-controls.json').write_text(json.dumps(dict(kind='offline_malformed_certificate_controls',cases=cases),indent=2)+'\n')
    print('Rejected',len(cases),'malformed controls',flush=True)


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--stage',choices=['small','large','negative','all'],default='all')
    ap.add_argument('--model',default='all');args=ap.parse_args()
    if args.stage in ('small','all'):small(args.out,args.model)
    if args.stage in ('large','all'):large(args.out)
    if args.stage in ('negative','all'):negative(args.out)

if __name__=='__main__': main()
