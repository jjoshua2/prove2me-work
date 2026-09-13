#!/usr/bin/env python3
"""Independent small-H / eroded-sum checks, blind simplex proposals, and rejection tests."""
from __future__ import annotations
import argparse,json,time,hashlib,random
from copy import deepcopy
from itertools import combinations,product
from pathlib import Path
from fractions import Fraction as Q
import simplex_summand_certificate as sc
import local_simplex_routes as routes
from exact_farkas_lp import parse,rat,serial,dot,require
from hpoly_segment_peeling import peel_one
from antipodal_segment_catalogue import catalogue
from test_segment_peeling import hull,vertices,graph,distances
ROOT=Path(__file__).resolve().parents[1]

def check_equality(A,b,G,t):
    """Independent full small-vertex equality, never trusts the eliminator."""
    A,b=parse(A,b);d=len(A[0]);t=rat(t)
    h=[max([Q(0)]+[dot(a,g) for g in G]) for a in A];rhs=[z-t*hi for z,hi in zip(b,h)]
    V=vertices(A,b);W=vertices(A,rhs)
    S={tuple(x[j]+t*g[j] for j in range(d)) for x in W for g in [(Q(0),)*d]+list(G)}
    # All sums lie in R. As V are extreme, V subset S is necessary AND sufficient.
    require(all(dot(a,x)<=z for x in S for a,z in zip(A,b)),'erosion inclusion failed')
    return set(V)<=S,len(V),len(W)

def triangle_product(blocks):
    d=2*blocks;A=[];b=[]
    for i in range(blocks):
        u,v=2*i,2*i+1
        for j in (u,v):A.append(tuple(-Q(k==j) for k in range(d)));b.append(Q(0))
        A.append(tuple(Q(k==u or k==v) for k in range(d)));b.append(Q(i+2,3))
    start=(Q(0),)*d;end=tuple(Q(i//2+2,3) if i%2==0 else Q(0) for i in range(d))
    return {'A':A,'b':b,'start':start,'end':end}

def nonproduct():
    tet=[(Q(0),)*3,(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1))]
    tri=[(Q(0),)*3,(Q(2),Q(0),Q(1)),(Q(0),Q(3),Q(1))]
    pts={tuple(x+y for x,y in zip(a,b)) for a in tet for b in tri}
    A,b,V=hull(pts,3)
    return {'A':A,'b':b,'start':[0,0,1],'end':V[-1]},V

def extraction_stage():
    cases=[
        ('self_triangle',[[-1,0],[0,-1],[1,1]],[0,0,1],[(Q(1),Q(0)),(Q(0),Q(1))]),
        ('triangle_absent_square',[[-1,0],[0,-1],[1,0],[0,1]],[0,0,1,1],[(Q(1),Q(0)),(Q(0),Q(1))]),
        ('tetra_self',[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],[0,0,0,1],
             [(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0)),(Q(0),Q(0),Q(1))]),
        ('tetra_has_no_triangle',[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],[0,0,0,1],
             [(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0))])]
    p=triangle_product(2);cases.append(('triangle_factor_product',p['A'],p['b'],
                 [(Q(1),Q(0),Q(0),Q(0)),(Q(0),Q(1),Q(0),Q(0))]))
    p,_=nonproduct();cases.append(('nonproduct_tetra_plus_triangle',p['A'],p['b'],
                 [(Q(2),Q(0),Q(1)),(Q(0),Q(3),Q(1))]))
    # Same full description with an implicit equality, repeated facets and zero row.
    cases.append(('embedded_triangle',[[-1,0,0],[0,-1,0],[1,1,0],[0,0,1],[0,0,-1],[-2,0,0],[0,0,0]],
                 [0,0,1,0,0,0,2],[(Q(1),Q(0),Q(0)),(Q(0),Q(1),Q(0))]))
    rec=[];decomps=0;ineq_checks=0
    for name,A,b,G in cases:
        V=vertices(A,b);out=sc.extract(A,b,G,V[0]);t=rat(out['certificate']['capacity'])
        good,n,ncore=check_equality(A,b,G,t);require(good,'claimed equality fails independent full vertex set')
        bad,_,_=check_equality(A,b,G,t+Q(1,100));require(not bad,'claimed maximality fails independent sum enumeration')
        for x in V+[tuple(sum(v[j] for v in V)/len(V) for j in range(len(V[0])))] :
            split=sc.decompose_point(A,b,G,t,x);decomps+=1;ineq_checks+=len(A)
        # k=1 is independently cross-checked against the old complete fiber criterion.
        old=peel_one(A,b,G[0],V[0]);one=sc.extract(A,b,[G[0]],V[0])
        require(old['certificate']['capacity']==one['certificate']['capacity'],'rank-one specialization disagrees')
        rec.append({'name':name,**out['verified'],'original_vertices':n,'core_vertices':ncore,
                    'lp_calls':out['lp_calls'],'lp_pivots':out['lp_pivots']})
        (ROOT/f'fixtures/{name}.json').write_text(json.dumps(serial({'A':A,'b':b,'simplex_generators':G,**out}),indent=2)+'\n')
    return {'examples':rec,'whole_vertex_equality_tests':len(rec),'strict_overshoot_tests':len(rec),
            'rank_one_crosschecks':len(rec),'explicit_point_decompositions':decomps,'point_inequality_checks':ineq_checks}

def route_stage():
    p,V=nonproduct();models=[('triangle_product4',triangle_product(2)),('nonproduct9',p),
        ('tetrahedron',{'A':[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],'b':[0,0,0,1],
                        'start':[0,0,0],'end':[1,0,0]})]
    counts={'models':0,'vertices':0,'graph_edges':0,'ordered_distances':0,'routes':0,'route_edges':0,
            'shortest_certified':0,'nonshortest_lifts':0};info=[]
    for name,data in models:
        maxrank=3 if name=='tetrahedron' else 2
        built=routes.build(data,maxrank);base=built['certificate'];A,b=parse(data['A'],data['b']);V=vertices(A,b);G=graph(A,b,V)
        # These important examples are certified segment-free by the PRIOR independent catalogue.
        old=catalogue(A,b,V[0]);require(old['verified']['positive_segment_directions']==0,'test not actually segment-free')
        nr=ne=0
        for i,u in enumerate(V):
            D=distances(G,i);counts['ordered_distances']+=len(D)
            for j in range(i+1):
                x=deepcopy(data);x['start']=u;x['end']=V[j];c=deepcopy(base)
                c['route']=routes.construct_route(x,c);report=routes.verify(x,c)
                raw=c['route']['route'] if c['route']['kind']=='direct_product' else c['route']['certificate']['route']
                path=[tuple(map(rat,v)) for v in raw]
                require(all(v in V for v in path) and all(V.index(y) in G[V.index(x)] for x,y in zip(path,path[1:])),
                        'independent original-H graph rejects route')
                L=report['ordinary_edges'];require(D[j]<=L,'shorter than graph distance')
                if report['shortest_certified']:require(L==D[j],'false shortestness')
                counts['shortest_certified']+=report['shortest_certified'];counts['nonshortest_lifts']+=L>D[j];nr+=1;ne+=L
        counts['models']+=1;counts['vertices']+=len(V);counts['graph_edges']+=sum(map(len,G))//2;counts['routes']+=nr;counts['route_edges']+=ne
        info.append({'name':name,**built['verified'],'reference_vertices':len(V),'all_pair_routes':nr,'segment_free_certificate':old['verified']})
        (ROOT/f'fixtures/route_{name}.json').write_text(json.dumps(serial({'input':data,**built}),indent=2)+'\n')
    return {'counts':counts,'examples':info}

def order_stage():
    points=[(Q(0),Q(0)),(Q(3),Q(0)),(Q(4),Q(2)),(Q(2),Q(4)),(Q(-1),Q(2))]
    A,b,V=hull(points,2)
    X=[(Q(3),Q(0)),(Q(9,2),Q(3))]
    Y=[(Q(3),Q(0)),(Q(9,5),Q(6,5))]
    ex=sc.extract(A,b,X,V[0]);ey=sc.extract(A,b,Y,V[0])
    def after(first,other):
        split=sc.decompose_point(A,b,first['certificate']['simplex_generators'],
                                    first['certificate']['capacity'],V[0])
        return sc.extract(A,first['verified']['eroded_rhs'],other,split['core_point'])
    xy=after(ex,Y);yx=after(ey,X)
    require([ex['certificate']['capacity'],ey['certificate']['capacity'],xy['certificate']['capacity'],yx['certificate']['capacity']]
             ==['2/3','1','0','0'],'order-dependence fixture changed')
    old=catalogue(A,b,V[0]);require(old['verified']['positive_segment_directions']==0,'pentagon not segment-free')
    # A one-edge antipodal route in a triangle misses two of its three directions:
    # the segment cover theorem does NOT extend to all simplex edge directions.
    c=(Q(2),Q(1));verts=[(Q(0),Q(0)),(Q(1),Q(0)),(Q(0),Q(1))]
    require(len(set(dot(c,v) for v in verts))==3,'antipodal example not strict')
    report={'status':'PASS','pentagon_vertices':serial(points),'first_triangle':serial(X),'second_triangle':serial(Y),
            'first_capacity':'2/3','second_capacity':'1','second_after_first':'0','first_after_second':'0',
            'segment_free':True,'segment_free_certificate':old['verified'],
            'simultaneous_individual_maxima_infeasible':True,
            'antipodal_simplex_direction_counterexample':{'triangle':serial(verts),'objective':serial(c),'route':[[1,0],[0,0]],
                                                          'walk_edges':1,'simplex_edge_directions':3}}
    (ROOT/'fixtures/noncommuting_triangles.json').write_text(json.dumps(serial({'A':A,'b':b,'first':ex,'second':ey,
                  'second_after_first':xy,'first_after_second':yx,'report':report}),indent=2)+'\n')
    return report

def dense_transform(data,seed):
    rng=random.Random(seed);d=len(data['start'])
    # Nilpotent rank-one shear: inverse is exact I-u v^T.
    u=[Q(rng.randrange(1,6),7) for _ in range(d)]
    v=[Q(rng.randrange(-4,5),5) for _ in range(d-1)]
    v.append(-sum((x*y for x,y in zip(u,v)),Q(0))/u[-1])
    T=[[Q(i==j)+u[i]*v[j] for j in range(d)] for i in range(d)]
    Ti=[[Q(i==j)-u[i]*v[j] for j in range(d)] for i in range(d)]
    shift=[Q(rng.randrange(-3,4),11) for _ in range(d)]
    AA=[];bb=[]
    for a,b in zip(data['A'],data['b']):
        row=[sum((a[k]*Ti[k][j] for k in range(d)),Q(0)) for j in range(d)]
        t=Q(rng.randrange(1,5),rng.randrange(1,5));AA.append([t*x for x in row]);bb.append(t*(b+dot(row,shift)))
    order=list(range(len(AA)));rng.shuffle(order)
    point=lambda x:[dot(row,x)+s for row,s in zip(T,shift)]
    return {'A':[AA[i] for i in order],'b':[bb[i] for i in order],'start':point(data['start']),'end':point(data['end'])}

def large_stage(size):
    data=triangle_product(size)
    if size==3:data=dense_transform(data,718)
    out=routes.build(data);report=out['verified']
    require(report['ordinary_edges']==size and report['shortest_certified'],'product shortest route failed')
    require(report['positive_simplex_factors']==size and report['core_kind']=='point','factors not recovered')
    report={**report,'reference_vertex_count_formula':3**size,'simplex_factors_supplied':False,
            'dense_hidden_affine_model':size==3,'whole_graph_enumerated':False}
    (ROOT/f'fixtures/triangle_product_{2*size}d.json').write_text(json.dumps(serial({'input':data,**out,'report':report}),indent=2)+'\n')
    return report

def negatives():
    A=[[-1,0],[0,-1],[1,1]];b=[0,0,1];G=[[1,0],[0,1]];out=sc.extract(A,b,G,[0,0]);c=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forgery '+name)
    for k,v in [('capacity','2'),('capacity','1/2'),('positive_circuit_count',0),('supports_examined',0),
                ('sharp_support',[0]),('sharp_point',[2,2]),('problem_sha256','bad'),('removed','-1')]:
        x=deepcopy(c);x[k]=v;reject(k,lambda x=x:sc.verify(A,b,G,x))
    x=deepcopy(c);x['demanding_circuit_proofs']=[];reject('missing_global_ray',lambda:sc.verify(A,b,G,x))
    x=deepcopy(c);x['demanding_circuit_proofs'][0]['ray'][0]='-1';reject('negative_ray',lambda:sc.verify(A,b,G,x))
    x=deepcopy(c);x['demanding_circuit_proofs'][0]['dual']=[[0,'-1']];reject('negative_original_Farkas',lambda:sc.verify(A,b,G,x))
    reject('dependent_simplex',lambda:sc.extract(A,b,[[1,0],[2,0]],[0,0]))
    reject('float',lambda:sc.extract(A,b,[[1.0,0],[0,1]],[0,0]))
    reject('enumeration_cap',lambda:sc.extract(A,b,G,[0,0],circuit_cap=1))
    data=triangle_product(2);out=routes.build(data);base=out['certificate']
    for field,value in [('boundedness',[]),('problem_sha256','bad')]:
        x=deepcopy(base);x[field]=value;reject('route_'+field,lambda x=x:routes.verify(data,x))
    x=deepcopy(base);x['route']['lower_bound']=999;reject('false_shortest_count',lambda:routes.verify(data,x))
    x=deepcopy(base);x['route']['route']=[x['route']['route'][0],x['route']['route'][-1]];reject('diagonal_as_edge',lambda:routes.verify(data,x))
    x=deepcopy(base);x['core_b'][0]='-2';reject('false_residual',lambda:routes.verify(data,x))
    octa={'A':[s for s in product((-1,1),repeat=3)],'b':[1]*8,'start':[1,0,0],'end':[-1,0,0]}
    reject('unsupported_octahedral_core',lambda:routes.build(octa))
    return {'rejected':len(names),'names':names}


def fourier_motzkin(C,rhs):
    """Independent scalar elimination, not the positive-circuit enumerator."""
    rows=[(tuple(a),rat(b)) for a,b in zip(C,rhs)]
    n=len(C[0])
    for _ in range(n):
        positive=[(a,b) for a,b in rows if a[-1]>0]
        negative=[(a,b) for a,b in rows if a[-1]<0]
        result=[(a[:-1],b) for a,b in rows if a[-1]==0]
        for a,b in positive:
            for c,d in negative:
                result.append((tuple(-c[-1]*x+a[-1]*y for x,y in zip(a[:-1],c[:-1])),
                               -c[-1]*b+a[-1]*d))
        merged={}
        for a,b in result:
            scale=max(map(abs,a),default=Q(0))
            if not scale:
                if b<0:return False
                continue
            a=tuple(x/scale for x in a);b/=scale
            merged[a]=min(merged.get(a,b),b)
        rows=list(merged.items())
    return all(b>=0 for _,b in rows)

def elimination_stage():
    rng=random.Random(719);tested=feasible=0
    for k in (1,2,3):
        d=3
        A=[tuple(Q(s*int(i==j)) for j in range(d)) for s in (-1,1) for i in range(d)]
        b=[Q(1)]*(2*d)
        for trial in range(12):
            while True:
                G=[tuple(Q(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(d)) for _ in range(k)]
                if sc.rank(G,d)==k:break
            P=sc.SimplexModel(A,b,G);rays,_=sc.positive_circuits(P.C,k)
            x=tuple(Q(rng.randrange(-3,4),4) for _ in range(d))
            for t in (Q(0),Q(1,10),Q(1),Q(4)):
                rhs=tuple(z-dot(a,x)-t*h for a,z,h in zip(P.A,P.b,P.support))+(Q(0),)*k+(t,)
                by_rays=all(sum((v*rhs[i] for i,v in zip(I,w)),Q(0))>=0 for I,w in rays)
                by_fm=fourier_motzkin(P.C,rhs)
                require(by_rays==by_fm,'independent Fourier-Motzkin disagrees with complete ray test')
                tested+=1;feasible+=by_fm
    require(0<feasible<tested,'feasibility oracle tests not exercising both outcomes')
    return {'independent_lift_feasibility_checks':tested,'feasible':feasible,'infeasible':tested-feasible,
            'candidate_ranks':[1,2,3]}

def hashes():
    files=[ROOT/'scripts'/p for p in ['simplex_summand_certificate.py','local_simplex_routes.py','test_low_rank_simplex.py']]
    files+=sorted((ROOT/'Solutions').glob('*.lean'))
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',required=True,choices=['extract','route','order','negative','large8','large16','dense','elimination','assemble'])
    a=ap.parse_args();start=time.monotonic()
    if a.stage=='assemble':
        stages={s:json.loads((ROOT/f'research/LOW_RANK_STAGE_{s}.json').read_text()) for s in ['extract','route','order','negative','large8','large16','dense','elimination']}
        require(all(x['status']=='PASS' and x['source_sha256']==hashes() for x in stages.values()),'stale/failing stage')
        totals=stages['route']['result']['counts'];large=[stages[s]['result'] for s in ['large8','large16','dense']]
        output={'status':'PASS','scope':'Exact global model equality/maximality and original-H routes. No Lean/platform verdict.',
                'stages':stages,'source_sha256':hashes(),'route_certificates':totals['routes']+len(large),
                'edge_occurrences':totals['route_edges']+sum(s['ordinary_edges'] for s in large)}
        (ROOT/'research/LOW_RANK_SIMPLEX_CHECK_2026-09-13.json').write_text(json.dumps(serial(output),indent=2,sort_keys=True)+'\n')
        print('ASSEMBLED',output['route_certificates'],output['edge_occurrences']);return
    f={'extract':extraction_stage,'route':route_stage,'order':order_stage,'negative':negatives,
        'large8':lambda:large_stage(8),'large16':lambda:large_stage(16),'dense':lambda:large_stage(3),'elimination':elimination_stage}
    result=f[a.stage]();out={'status':'PASS','seconds':round(time.monotonic()-start,3),
                            'source_sha256':hashes(),'result':result}
    (ROOT/f'research/LOW_RANK_STAGE_{a.stage}.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
    print(a.stage,'PASS',out['seconds']);print(json.dumps(serial(result),sort_keys=True))
if __name__=='__main__':main()
