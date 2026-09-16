#!/usr/bin/env python3
"""Independent exact geometry, metric, gain-cycle and saved-certificate tests."""
from fractions import Fraction as Q
from itertools import combinations, product
from collections import deque
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, random
import sympy as sp
import affine_conditioning_certificates as C


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(C.serial(data), sort_keys=True, indent=2)+'\n')


def metric_stage(folder):
    rng=random.Random(275); tested=0; independent=0; records=[]
    for e in [Q(1,2),Q(1,3),Q(1,17),Q(1,2**40),Q(1,2**160)]:
        local=0
        for _ in range(120):
            # Rational independent vectors, not generated from the asserted bound.
            p=[Q(rng.randint(-9,9)) for _ in range(3)]
            q=[Q(rng.randint(-9,9)) for _ in range(3)]
            X=sum(x*x for x in p);Y=sum(y*y for y in q);Z=sum(x*y for x,y in zip(p,q))
            if not X or not Y or X*Y==Z*Z:continue
            report=C.metric_bound(e,X,Y,Z)
            answers=[]
            for a,b in [(p,[x+e*y for x,y in zip(p,q)]),(q,[y+e*x for x,y in zip(p,q)])]:
                va,vb=sp.Matrix(a),sp.Matrix(b)
                distance=vb-va*((va.T*vb)[0]/(va.T*va)[0])
                answers.append(Q((distance.T*distance)[0]/(vb.T*vb)[0]));independent+=1
            assert list(map(Q,report['squared_pair_sines']))==answers
            tested+=1;local+=1
        normals=[(1,0),(1,e),(e,1),(0,1)]
        M=sp.Matrix([[1,-e],[-e,1]]);sines=[]
        for a,b in combinations(normals,2):
            a,b=sp.Matrix(a),sp.Matrix(b)
            sine=1-(a.T*M*b)[0]**2/((a.T*M*a)[0]*(b.T*M*b)[0]);sines.append(Q(sine))
        assert min(sines)==e*e
        optimum=C.metric_bound(e,1,1,-e)
        assert optimum['squared_pair_sines']==[str(e*e)]*2
        records.append({'epsilon':e,'random_metrics':local,'optimum_all_six_pair_squared_sines':sines,'optimum':optimum})
    dump(folder/'metric_examples.json',records)
    return {'status':'PASS','random_Gram_cases':tested,'independent_vector_projection_checks':independent,
            'attaining_metrics':len(records),'scope':'Finite tests support the separate universal Lean algebraic theorem.'}


def reference_polytope(e,d):
    A,b=C.product_H(e,d);points=set();systems=0
    for J in combinations(range(len(A)),d):
        systems+=1;M=sp.Matrix([A[i] for i in J])
        if not M.det():continue
        x=tuple(Q(t) for t in M.inv()*sp.Matrix([b[i] for i in J]))
        if all(C.edge.dot(a,x)<=t for a,t in zip(A,b)):points.add(x)
    expected={p+tuple(map(Q,bits)) for p in C.polygon(e) for bits in product((-1,1),repeat=d-2)}
    assert points==expected
    acts={x:set(C.edge.active(A,b,x)) for x in points};assert all(len(I)==d for I in acts.values())
    G={x:set() for x in points}
    for x,y in combinations(points,2):
        I=sorted(acts[x]&acts[y]);rank=sp.Matrix([A[i] for i in I]).rank() if I else 0
        if rank==d-1:G[x].add(y);G[y].add(x)
    D={}
    for source in G:
        ds={source:0};queue=deque([source])
        while queue:
            x=queue.popleft()
            for y in G[x]:
                if y not in ds:ds[y]=ds[x]+1;queue.append(y)
        assert len(ds)==len(G);D[source]=ds
    assert max(max(row.values()) for row in D.values())==d+2
    return G,D,systems


def geometry_stage(folder):
    stats={'complete_active_systems':0,'reference_vertices':0,'reference_edges':0,'checked_pairs':0,'route_edges':0,'facet_witnesses':0};refs=[];saved=[]
    for e,d in [(Q(1,2),2),(Q(1,17),2),(Q(1,2**160),2),(Q(1,3),3),(Q(1,5),4)]:
        G,D,systems=reference_polytope(e,d);stats['complete_active_systems']+=systems
        stats['reference_vertices']+=len(G);stats['reference_edges']+=sum(map(len,G.values()))//2
        V=C.polygon(e);vertices=[(i,list(bits)) for i in range(8) for bits in product((-1,1),repeat=d-2)]
        count=0
        for (i,u),(j,v) in combinations(vertices,2):
            record=C.product_record(e,d,i,j,u,v);report=C.verify_product_record(record)
            x,y=V[i]+tuple(map(Q,u)),V[j]+tuple(map(Q,v))
            assert report['route_edges']==D[x][y]
            stats['route_edges']+=report['route_edges'];stats['checked_pairs']+=1;count+=1
            points=[tuple(map(Q,p['point'])) for p in record['certificate']['vertices']]
            assert all(b in G[a] for a,b in zip(points,points[1:]))
        stats['facet_witnesses']+=len(C.product_anchors(e,d));saved.append(C.product_record(e,d))
        refs.append({'epsilon':e,'dimension':d,'vertices':len(G),'edges':sum(map(len,G.values()))//2,'all_distinct_pairs':count,'diameter':d+2})
    large=[]
    for d in (16,32):
        record=C.product_record(Q(1,2**160),d);report=C.verify_product_record(record)
        assert report['common_endpoint_facets']==0 and report['route_edges']==d+2
        large.append(report);saved.append(record)
    # Dense affine changes: check actual re-encoded ORIGINAL rows and mapped paths.
    affine=[]
    for d in (2,3,5):
        e=Q(1,17);A,b=C.product_H(e,d);points=C.shortest_product_points(e,d,0,[-1]*(d-2),4,[1]*(d-2))
        T=sp.eye(d)+sp.ones(d,d);inverse=T.inv();shift=sp.Matrix([Q(i,7) for i in range(d)])
        M=sp.Matrix(A)*inverse;rhs=sp.Matrix(b)+M*shift
        moved=[tuple(Q(z) for z in T*sp.Matrix(x)+shift) for x in points]
        row=C.route_packet(tuple(tuple(Q(x) for x in r) for r in M.tolist()),tuple(Q(x) for x in rhs),moved)
        assert row['verified']['original_edges']==d+2;affine.append(row)
    truncated=[]
    for d in (3,16,32):
        rec=C.truncated_record(Q(1,2**160),d);truncated.append(rec)
    # Independent complete graph for the coupled 3D model.
    AA,bb,_,_=C.truncated_data(Q(1,2**160),3)
    VV=set()
    for J in combinations(range(len(AA)),3):
        MM=sp.Matrix([AA[i] for i in J])
        if not MM.det():continue
        xx=tuple(Q(t) for t in MM.inv()*sp.Matrix([bb[i] for i in J]))
        if all(C.edge.dot(a,xx)<=z for a,z in zip(AA,bb)):VV.add(xx)
    assert len(VV)==18
    graph={x:set() for x in VV}
    for x,y in combinations(VV,2):
        I=set(C.edge.active(AA,bb,x))&set(C.edge.active(AA,bb,y))
        if I and sp.Matrix([AA[i] for i in I]).rank()==2:graph[x].add(y);graph[y].add(x)
    ds={tuple(map(Q,truncated[0]['input']['start'])):0};todo=deque(ds)
    while todo:
        x=todo.popleft()
        for y in graph[x]:
            if y not in ds:ds[y]=ds[x]+1;todo.append(y)
    assert ds[tuple(map(Q,truncated[0]['input']['target']))]==5
    dump(folder/'truncated_routes.json',truncated)
    dump(folder/'product_routes.json',saved);dump(folder/'dense_affine_routes.json',affine)
    return {'status':'PASS','small':stats,'models':refs,'large':large,'dense_affine_path_checks':len(affine),'nonproduct_truncated_routes':[C.verify_truncated_record(r) for r in truncated],'truncated_3D_reference_vertices':len(VV),
            'scope':'Geometry is a written product theorem plus exact original-H records, not the public scalar Lean target.'}


def independent_balance(A):
    """Exact nullspace of magnitude equations; no gain-tree traversal."""
    d=len(A[0]);M=[]
    for a in A:
        S=[i for i,x in enumerate(a) if x]
        if len(S)==2:
            i,j=S;row=[Q(0)]*d;row[i]=abs(a[i]);row[j]=-abs(a[j]);M.append(row)
    null=(sp.Matrix(M) if M else sp.zeros(0,d)).nullspace()
    # A component has at most one positive ray. Squared nullspace coordinates
    # identify whether every variable participates in a nonzero kernel vector.
    return all(any(v[i]!=0 for v in null) for i in range(d))


def gain_stage(folder):
    rng=random.Random(27501);balanced=bad=0;saved=[];cases=0
    for d in range(1,9):
        for attempt in range(32):
            scales=[Q(rng.randint(1,9),rng.randint(1,9)) for _ in range(d)]
            A=[tuple(Q(i==j)/scales[i] for j in range(d)) for i in range(d)]
            for i,j in combinations(range(d),2):
                if rng.random()>.45:continue
                r=[Q(0)]*d;r[i]=rng.choice((-1,1))*rng.randint(1,7)/scales[i];r[j]=abs(r[i])*scales[i]*rng.choice((-1,1))/scales[j]
                A.append(tuple(r))
            if attempt%2 and d>1:
                for n,r in enumerate(A):
                    S=[i for i,x in enumerate(r) if x]
                    if len(S)==2:
                        altered=list(r);altered[S[0]]*=2;A.append(tuple(altered));break
            cert=C.recognize_balance(A);ver=C.verify_balance(A,cert);truth=independent_balance(A)
            assert (cert['status']=='BALANCED')==truth;cases+=1
            if truth:balanced+=1
            else:bad+=1
            if len(saved)<4 or (not truth and sum(s['certificate']['status']=='INCONSISTENT_CYCLE' for s in saved)<4):saved.append({'A':C.serial(A),'certificate':cert,'verified':ver})
    transports=[]
    for d in (8,32):
        s=[Q(2**(20*i)) for i in range(d)];A=[];b=[]
        for i in range(d):
            for sign in (-1,1):A.append(tuple(Q(sign if j==i else 0)/s[i] for j in range(d)));b.append(Q(sign>0))
        for i in range(d-1):A.append(tuple((Q(j==i)-Q(j==i+1))/s[j] for j in range(d)));b.append(Q(0))
        cert=C.recognize_balance(A);B,rhs,_=C.balanced_H(A,b,cert)
        assert all(all(abs(t)==1 for t in row if t) for row in B)
        original=C.route_packet(A,b,[(Q(0),)*d,tuple(s)])
        assert original['verified']['original_edges']==1
        transports.append({'dimension':d,'scale_ratio':str(s[-1]/s[0]),'A':C.serial(A),'b':C.serial(b),'balance':cert,'original_route':original})
    dump(folder/'gain_certificates.json',saved);dump(folder/'balanced_simplex_routes.json',transports)
    return {'status':'PASS','independent_nullspace_cases':cases,'balanced':balanced,'inconsistent':bad,
            'transported_original_routes':[{'dimension':r['dimension'],'edges':1,'scale_ratio':r['scale_ratio']} for r in transports]}


def negative_stage(folder):
    good=C.product_record(Q(1,5),3);pos=C.recognize_balance([[1,-2,0],[0,2,3]])
    A=[[1,-2,0],[0,2,3],[2,0,3]];neg=C.recognize_balance(A);assert neg['status']=='INCONSISTENT_CYCLE'
    rejected=[]
    def reject(name,fun):
        try:fun()
        except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):rejected.append(name);return
        raise AssertionError('accepted '+name)
    def geometry(name,edit):
        c=deepcopy(good);edit(c);reject(name,lambda:C.verify_product_record(c))
    geometry('wrong epsilon',lambda c:c['family'].update(epsilon='1/4'))
    geometry('wrong diameter',lambda c:c.update(proved_family_diameter=4))
    geometry('missing cube coordinate',lambda c:c['family'].update(first_cube=[]))
    geometry('invalid octagon index',lambda c:c['family'].update(first_octagon=-1))
    geometry('wrong metric',lambda c:c.update(optimum_Gram_2x2=['1','1','0']))
    geometry('false facet anchor',lambda c:c['facet_anchors'].__setitem__(0,['0']*3))
    geometry('false inverse',lambda c:c['certificate']['vertices'][0]['inverse'][0].__setitem__(0,'999'))
    geometry('missing edge certificate',lambda c:c['certificate']['edges'].pop())
    for name,edit in [('gain product',lambda c:c.update(gain_product='1')),('cycle gap',lambda c:c['cycle'][0].update(to=2)),('row label',lambda c:c['cycle'][0].update(row=999)),('empty cycle',lambda c:c.update(cycle=[]))]:
        c=deepcopy(neg);edit(c);reject(name,lambda c=c:C.verify_balance(A,c))
    c=deepcopy(pos);c['scales'][0]='0';reject('zero scale',lambda:C.verify_balance([[1,-2,0],[0,2,3]],c))
    c=deepcopy(pos);c['row_weights'][0]='999';reject('false weight',lambda:C.verify_balance([[1,-2,0],[0,2,3]],c))
    reject('three nonzeros',lambda:C.recognize_balance([[1,2,3]]))
    reject('float coordinate',lambda:C.recognize_balance([[1,0.5]]))
    reject('singular Gram',lambda:C.metric_bound(Q(1,3),1,1,1))
    reject('epsilon boundary',lambda:C.metric_bound(1,1,1,0))
    return {'status':'PASS','rejected':rejected}


def audit_stage(folder):
    counts={'truncated_records':0,'product_records':0,'dense_affine_records':0,'gain_records':0,'transport_records':0,'original_edges':0}
    old={n:getattr(C,n) for n in ('recognize_balance','product_record','shortest_product_points','product_anchors','route_packet','truncated_record')}
    inv={n:getattr(C.edge,n) for n in ('inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses')}
    def kill(*a,**k):raise AssertionError('producer called during audit')
    try:
        for n in old:setattr(C,n,kill)
        for n in inv:setattr(C.edge,n,kill)
        for c in json.loads((folder/'product_routes.json').read_text()):
            r=C.verify_product_record(c);counts['product_records']+=1;counts['original_edges']+=r['route_edges']
        for c in json.loads((folder/'truncated_routes.json').read_text()):
            r=C.verify_truncated_record(c);counts['truncated_records']+=1;counts['original_edges']+=r['selected_shortest_edges']
        for c in json.loads((folder/'dense_affine_routes.json').read_text()):
            assert C.edge.verify_path(c['input'],c['certificate'])==c['verified'];counts['dense_affine_records']+=1;counts['original_edges']+=c['verified']['original_edges']
        for c in json.loads((folder/'gain_certificates.json').read_text()):
            assert C.verify_balance(c['A'],c['certificate'])==c['verified'];counts['gain_records']+=1
        for c in json.loads((folder/'balanced_simplex_routes.json').read_text()):
            C.verify_balance(c['A'],c['balance']);r=c['original_route'];assert C.edge.verify_path(r['input'],r['certificate'])==r['verified'];counts['transport_records']+=1;counts['original_edges']+=r['verified']['original_edges']
    finally:
        for n,f in old.items():setattr(C,n,f)
        for n,f in inv.items():setattr(C.edge,n,f)
    return {'status':'PASS','producer_functions_disabled':list(old)+list(inv),'counts':counts}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['metric','geometry','gain','negative','audit'],required=True)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args();a.fixtures.mkdir(parents=True,exist_ok=True)
    r=globals()[a.stage+'_stage'](a.fixtures)
    r['source_sha256']={n:hashlib.sha256((Path(__file__).parent/n).read_bytes()).hexdigest() for n in ['affine_conditioning_certificates.py','test_affine_conditioning_certificates.py','original_route_exclusion.py']}
    dump(a.out,r);print(json.dumps(C.serial(r),indent=2))
if __name__=='__main__':main()
