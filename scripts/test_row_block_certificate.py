#!/usr/bin/env python3
"""Deterministic exact tests, genuine-edge enumeration, and adversarial controls."""
from __future__ import annotations
import argparse,copy,hashlib,itertools,json,random
from collections import deque
from fractions import Fraction as Q
from pathlib import Path
from row_block_certificate import certificate,verify_certificate,rank,inverse,matmul,dot,identity,jsonable


def factor(kind: str, d: int=1):
    if kind == 'simplex':
        A=[[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(1)]*d]
        return A,[Q(0)]*d+[Q(1)],[Q(1,d+1)]*d,[Q(1)]*(d+1)
    if kind == 'square':
        return [[Q(-1),Q(0)],[Q(0),Q(-1)],[Q(1),Q(0)],[Q(0),Q(1)]],[Q(0),Q(0),Q(2),Q(2)],[Q(1),Q(1)],[Q(1)]*4
    if kind == 'pentagon':
        A,b,p,w=factor('square')
        return A+[[Q(1),Q(1)]],b+[Q(3)],p,[Q(2),Q(2),Q(1),Q(1),Q(1)]
    if kind == 'hexagon':
        A,b,p,_=factor('pentagon')
        return A+[[Q(-1),Q(-1)]],b+[Q(-1)],p,[Q(1)]*6
    raise ValueError(kind)


def product(spec):
    fs=[factor(*s) for s in spec];D=sum(len(p) for _,_,p,_ in fs)
    A=[];b=[];p=[];w=[];off=0
    for a,r,x,weights in fs:
        h=len(x)
        A += [[Q(0)]*off+row+[Q(0)]*(D-off-h) for row in a]
        b+=r;p+=x;w+=weights;off+=h
    return dict(A=A,b=b,feasible_point=p,positive_balance=w)


def scramble(data,seed):
    rng=random.Random(seed);A=data['A'];b=data['b'];d=len(A[0]);M=identity(d)
    for _ in range(2*d):
        if d<2: break
        i,j=rng.sample(range(d),2);c=Q(rng.choice([-2,-1,1,2]))
        M[i]=[x+c*y for x,y in zip(M[i],M[j])]
    C=matmul(A,M);t=[Q(rng.randint(-3,3),2) for _ in range(d)]
    inv=inverse(M);p=[dot(r,data['feasible_point'])+z for r,z in zip(inv,t)]
    bb=[rhs+dot(row,t) for row,rhs in zip(C,b)]
    perm=list(range(len(C)));rng.shuffle(perm)
    scales=[Q(rng.randint(1,4),rng.randint(1,4)) for _ in C]
    return dict(A=[[scales[i]*x for x in C[i]] for i in perm],
        b=[scales[i]*bb[i] for i in perm],feasible_point=p,
        positive_balance=[data['positive_balance'][i]/scales[i] for i in perm])


def exact_graph(data):
    """Enumerate vertices and test common-tight-row rank d-1 for genuine edges."""
    A=data['A'];b=data['b'];d=len(A[0]);vertices=set()
    for I in itertools.combinations(range(len(A)),d):
        rows=[A[i] for i in I]
        if rank(rows)<d: continue
        inv=inverse(rows);rhs=[b[i] for i in I]
        x=tuple(dot(r,rhs) for r in inv)
        if all(dot(r,x)<=t for r,t in zip(A,b)): vertices.add(x)
    V=sorted(vertices)
    assert V
    active=[{j for j,(r,t) in enumerate(zip(A,b)) if dot(r,v)==t} for v in V]
    adj=[set() for _ in V]
    for i in range(len(V)):
        for j in range(i):
            if rank([A[r] for r in sorted(active[i]&active[j])])==d-1:
                adj[i].add(j);adj[j].add(i)
    diam=0
    for s in range(len(V)):
        dist={s:0};q=deque([s])
        while q:
            u=q.popleft()
            for v in adj[u]:
                if v not in dist:dist[v]=dist[u]+1;q.append(v)
        assert len(dist)==len(V)
        diam=max(diam,max(dist.values()))
    return {'vertices':len(V),'edges':sum(map(len,adj))//2,'diameter':diam}


def saturated_cube_carrier(k):
    # Intrinsic floor rows of PR122: cube bounds plus neutral cap restrictions.
    A=[];b=[]
    for j in range(k):
        A.append([-Q(i==j) for i in range(k)]);b.append(Q(0))
        A.append([Q(i==j) for i in range(k)]);b.append(Q(1))
    redundancy={}
    for j in range(1,k):
        row=[Q(0)]*k;row[j]=1;row[0]=-1
        idx=len(A);A.append(row);b.append(Q(5,2))
        lam=[Q(0)]*(2*k);lam[0]=1;lam[2*j+1]=1
        redundancy[str(idx)]=lam
    return dict(A=A,b=b,keep=list(range(2*k)),redundancy=redundancy,
        feasible_point=[Q(1,2)]*k,positive_balance=[Q(1)]*(2*k))


def run():
    full=[];mixed=[]
    specs=[ [('square',1),('square',1)], [('pentagon',1),('simplex',1)],
        [('pentagon',1),('pentagon',1)], [('simplex',3),('pentagon',1)],
        [('square',1),('square',1),('simplex',1)], [('simplex',4),('simplex',1)] ]
    for j,spec in enumerate(specs):
        original=product(spec)
        for rep in range(2):
            data=original if rep==0 else scramble(original,20260911+13*j)
            result=certificate(data);v=result['verified'];g=exact_graph(data)
            assert v['all_factor_excesses_at_most_three']
            assert g['diameter']<=v['ordinary_edge_bound_using_existing_small_excess_theorem']
            full.append({'case':j,'scrambled':bool(rep),**g,**v})
    saturations=[]
    for k in range(4,13):
        data=saturated_cube_carrier(k);cert=certificate(data);v=cert['verified']
        assert len(v['factors'])==k and all(f['excess']==1 for f in v['factors'])
        assert v['ordinary_edge_bound_using_existing_small_excess_theorem']==k
        # The unreduced normal system is connected: redundant caps obscure the product.
        raw=copy.deepcopy(data);raw.pop('keep');raw.pop('redundancy')
        weights=[Q(1)]*(3*k-1);weights[1]=Q(k)
        for j in range(1,k):weights[2*j]=Q(2)
        raw['positive_balance']=weights
        before=certificate(raw)['verified']
        assert len(before['factors'])==1 and not before['all_factor_excesses_at_most_three']
        saturations.append({'k':k,'ambient_dimension':2*k-1,'ambient_rows':4*k-2,
            'carrier_excess':k,'neutral_defect':k-1,'kappa':0,'s':0,'tau':0,
            'unreduced_single_block_excess':2*k-1,'certified_edge_bound_after_deletion':k,
            'dropped_rows_with_farkas_certificates':k-1,'factor_count':k})
    large=[]
    for k in [4,8,12,16]:
        data=product([('simplex',1)]*k+[('pentagon',1)]*2)
        v=certificate(scramble(data,100+k))['verified']
        assert v['ordinary_edge_bound_using_existing_small_excess_theorem']==k+6
        large.append(v)
    for spec in [[('hexagon',1)],[('hexagon',1),('simplex',1),('simplex',1)]]:
        data=product(spec);v=certificate(data)['verified'];g=exact_graph(data)
        assert v['ordinary_edge_bound_using_existing_small_excess_theorem'] is None
        assert len(v['unresolved_factor_indices'])==1
        mixed.append({**v,**g})
    negative=[]
    def rejected(name,data,cert=None):
        try:
            certificate(data) if cert is None else verify_certificate(data,cert)
        except (ValueError,ZeroDivisionError,IndexError,TypeError):negative.append(name);return
        raise AssertionError('bad certificate accepted: '+name)
    data=product([('square',1),('square',1)]);c=certificate(data)['certificate']
    bad=copy.deepcopy(c);bad['inverse_basis'][0][0]+=1;rejected('wrong_inverse',data,bad)
    bad=copy.deepcopy(c);bad['transformed_rows'][0][0]+=1;rejected('wrong_transformed_normal',data,bad)
    bad=copy.deepcopy(c);bad['coordinate_blocks'][0].append(bad['coordinate_blocks'][1][0]);rejected('duplicate_coordinate',data,bad)
    bad=copy.deepcopy(c);bad['row_blocks'][0].append(bad['row_blocks'][1][0]);rejected('duplicate_row',data,bad)
    bad=copy.deepcopy(c);bad['row_blocks'][0][0],bad['row_blocks'][1][0]=bad['row_blocks'][1][0],bad['row_blocks'][0][0];rejected('hidden_cross_block_coupling',data,bad)
    bad=copy.deepcopy(data);bad['positive_balance'][0]=0;rejected('nonpositive_balance',bad)
    bad=copy.deepcopy(data);bad['positive_balance'][0]=2;rejected('unbalanced_normals',bad)
    bad=copy.deepcopy(data);bad['feasible_point'][0]=100;rejected('infeasible_witness',bad)
    bad=saturated_cube_carrier(4);bad['redundancy']['8'][0]=-1;rejected('negative_farkas_multiplier',bad)
    bad=saturated_cube_carrier(4);bad['b'][8]=Q(1,2);rejected('invalid_farkas_rhs',bad)
    bad=saturated_cube_carrier(4);bad['redundancy'].pop('8');rejected('uncertified_row_deletion',bad)
    bad=copy.deepcopy(data);bad['A'][0][0]=0.5;rejected('floating_point_input',bad)
    return {'seed':20260911,'evidence':'exact rational certificates and finite graphs; not Lean instance proofs',
        'fully_enumerated_models':full,'saturated_zero_savings_carriers':saturations,
        'large_products_without_vertex_enumeration':large,'unresolved_by_sufficient_criterion':mixed,
        'negative_controls_rejected':negative,
        'totals':{'full_graphs':len(full)+len(mixed),'vertices':sum(x['vertices'] for x in full+mixed),
                  'edges':sum(x['edges'] for x in full+mixed),'zero_savings_families':len(saturations),
                  'negative_controls':len(negative)}}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    report=run();text=json.dumps(jsonable(report),indent=2)+'\n';args.output.write_text(text)
    print(json.dumps(report['totals'],indent=2));print('sha256='+hashlib.sha256(text.encode()).hexdigest())
