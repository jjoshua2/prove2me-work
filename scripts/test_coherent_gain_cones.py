#!/usr/bin/env python3
"""Exact all-small-basis, original-H graph, resonance and face-closure tests."""
from __future__ import annotations
from coherent_gain_cones import *
from itertools import combinations
from copy import deepcopy
import random,time
ROOT=Path(__file__).resolve().parents[1]


def inverse(A):
    d=len(A);a=[list(map(rat,row))+[Q(i==j)for j in range(d)]for i,row in enumerate(A)]
    for j in range(d):
        p=next((i for i in range(j,d)if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(d):
            if i!=j:
                t=a[i][j]
                if t:a[i]=[x-t*y for x,y in zip(a[i],a[j])]
    return tuple(tuple(row[d:])for row in a)


def rank(A):
    a=[list(map(rat,row))for row in A]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a))if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            t=a[i][j]
            if t:a[i]=[x-t*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def vertices(A,b):
    d=len(A[0]);out=set()
    for ids in combinations(range(len(A)),d):
        inv=inverse([A[i]for i in ids])
        if inv is None:continue
        x=tuple(dot(row,[b[i]for i in ids])for row in inv)
        if all(dot(a,x)<=z for a,z in zip(A,b)):out.add(x)
    return sorted(out)


def graph(A,b,V):
    acts=[{i for i,(a,z)in enumerate(zip(A,b))if dot(a,x)==z}for x in V]
    G=[set()for _ in V]
    for i,j in combinations(range(len(V)),2):
        if rank([A[k]for k in acts[i]&acts[j]])==len(A[0])-1:G[i].add(j);G[j].add(i)
    return G


def distances(G,i):
    D={i:0};q=deque([i])
    while q:
        u=q.popleft()
        for v in G[u]:
            if v not in D:D[v]=D[u]+1;q.append(v)
    return D


def cactus(d,precision=80,box=False):
    require(d>=3,'cactus generator needs at least three variables')
    A=[[-int(i==j)for j in range(d)]for i in range(d)];b=[Q(0)]*d
    if box:
        A += [[int(i==j)for j in range(d)]for i in range(d)];b += [Q(1)]*d
    anchor=0;k=0;cycle_gains=[]
    while 2*k+2<d:
        a,c=2*k+1,2*k+2
        G=1-Q(1,2**precision)if k==0 else 1-Q(1,3**(precision//2))if k==1 else 1-Q(1,10000+k)
        t=(1+G)/2;gains=[t,t,G/t**2];cycle_gains.append(G)
        for j,(u,v,g)in enumerate(zip([anchor,a,c],[a,c,anchor],gains)):
            row=[Q(0)]*d;row[u]=-g;row[v]=1;A.append(row)
            b.append(Q(1,3)+Q(k+j,100)if box else 1-g+(Q(1,8)if k and j==2 else 0))
        anchor=c;k+=1
    if 2*k+1<d:
        u,v=anchor,d-1;g=Q(999,1000);row=[Q(0)]*d;row[u]=-g;row[v]=1;A.append(row)
        b.append(Q(1,3)if box else 1-g)
    return {'A':A,'b':b,'start':[0]*d,'end':[1]*d},cycle_gains


def basis_tests():
    tested=valid=singular=0;largest=Q(0);sample_info=[]
    for d in(2,3,4,5,6):
        if d==2:
            eps=Q(1,2**120);A=[[-1,0],[0,-1],[-1,1],[1+eps,-1],[1,0],[0,1]]
        elif d==5:
            A=[[-int(i==j)for j in range(d)]for i in range(d)]+[[int(i==j)for j in range(d)]for i in range(d)]
            for i,j,g in [(0,1,Q(1)),(1,2,Q(1)),(0,2,Q(1)),(0,3,Q(1)),(3,4,Q(1)),(4,0,1-Q(1,2**80))]:
                row=[Q(0)]*d;row[i]=-g;row[j]=1;A.append(row)
        else:A=cactus(d,precision=10,box=True)[0]['A']
        S=certify_structure(A)['certificate'];N=normalized_rows(parse_rows(A),S)
        choices=list(combinations(range(len(A)),d));full_count=len(choices)
        if len(choices)>1600 and d!=5:
            random.Random(215+d).shuffle(choices);choices=choices[:1600]
        nvalid=0
        for B in choices:
            actual=inverse([N[r]for r in B]);tested+=1
            if actual is None:singular+=1;continue
            c=cone_witness(A,S,B);v=verify_cone(A,S,c)
            # Independent Gaussian inverse verifies every numerical cone margin.
            w=rat(c['width_squared']);center=tuple(map(rat,c['center']))
            for j in range(d):
                dual=tuple(actual[i][j]for i in range(d));m=dot(dual,center)
                require(m>0 and m*m>=w*dot(dual,dual)*dot(center,center),'Gaussian cone check failed')
            largest=max(largest,max(abs(x)for row in actual for x in row));valid+=1;nvalid+=1
        sample_info.append({'dimension':d,'rows':len(A),'basis_subsets_tested':len(choices),'nonsingular':nvalid,'all_subsets':len(choices)==full_count,'dense_balanced_block':d==5})
    return {'basis_subsets_tested':tested,'nonsingular_basis_cones':valid,'singular_bases':singular,
            'largest_inverse_entry':str(largest),'libraries':sample_info}


def small_tests():
    P3,_=cactus(3,precision=8);P5,_=cactus(5,precision=8)
    box,_=cactus(4,precision=6,box=True)
    eps=Q(1,2**80)
    cases=[('resonant_quadrilateral',{'A':[[-1,0],[0,-1],[-1,1],[1+eps,-1]],'b':[0,0,1,1],'start':[0,0],'end':[2/eps,2/eps+1]}),
           ('coherent_triangle3',P3),('two_unrelated_cycles5',P5),('clipped_box4',box),
           ('balanced_and_duplicate',{'A':[[-1,0],[1,0],[0,-1],[0,1],[-1,1],[1,-1],[-2,2],[0,0]],'b':[0,1,0,1,1,1,2,0],'start':[0,0],'end':[1,1]}),
           ('implicit_equality',{'A':[[1,-1],[-1,1],[-1,0],[1,0]],'b':[0,0,0,1],'start':[0,0],'end':[1,1]}),
           ('unbounded',{'A':[[1,-1],[-1,0],[1,0]],'b':[0,0,1],'start':[0,0],'end':[1,1]})]
    totals={'models':0,'vertices':0,'edges':0,'ordered_distances':0,'routes':0,'edge_occurrences':0,'basis_pivots':0,'stationary_pivots':0,'face_checks':0,'original_row_checks':0};info=[]
    for name,data in cases:
        A=parse_rows(data['A']);b=list(map(rat,data['b']));V=vertices(A,b);G=graph(A,b,V);record={'name':name,'dimension':len(A[0]),'rows':len(A),'vertices':len(V),'graph_edges':sum(map(len,G))//2,'max_route':0}
        for i,x in enumerate(V):
            D=distances(G,i);totals['ordered_distances']+=len(D)
            for j in range(i+1):
                p=deepcopy(data);p['start']=x;p['end']=V[j];out=construct_route(p);v=out['verified'];r=[tuple(map(rat,z))for z in out['certificate']['route_certificate']['route']]
                require(all(z in V for z in r),'unlisted original-H vertex')
                require(all(V.index(z)in G[V.index(y)]for y,z in zip(r,r[1:])),'independent H graph rejects edge')
                require(v['edges']>=D[j],'shorter than BFS')
                require(v['sample_within_bound'],'tested sampler exceeds existence bound')
                totals['routes']+=1;totals['edge_occurrences']+=v['edges'];totals['basis_pivots']+=v['basis_pivots'];totals['stationary_pivots']+=v['stationary_pivots'];totals['original_row_checks']+=v['original_row_checks'];totals['face_checks']+=int(v['intrinsic_dimension']>0)
                record['max_route']=max(record['max_route'],v['edges'])
        totals['models']+=1;totals['vertices']+=len(V);totals['edges']+=record['graph_edges'];info.append(record)
        print(record,flush=True)
    return totals,info


def large_tests():
    records=[]
    for d in(12,24,32):
        p,_=cactus(d,precision=120);begin=time.monotonic();out=construct_route(p)
        rec={'name':f'coherent_cactus_{d}',**out['verified'],'seconds':round(time.monotonic()-begin,3)};records.append(rec)
        (ROOT/f'fixtures/coherent_cactus_{d}.json').write_text(json.dumps(serial({'input':p,**out}),indent=2)+'\n')
        print({k:rec[k]for k in('name','edges','basis_pivots','stationary_pivots','seconds')},flush=True)
    rng=random.Random(216);base,_=cactus(7,precision=20)
    for k in range(3):
        p=deepcopy(base);s=[Q(rng.randrange(1,20),rng.randrange(1,20))*Q(2)**(k*i*15)for i in range(7)]
        mult=[Q(rng.randrange(1,20),rng.randrange(1,20))for _ in p['A']]
        p['A']=[[rat(x)*mult[r]/s[j]for j,x in enumerate(a)]for r,a in enumerate(p['A'])];p['b']=[rat(x)*v for x,v in zip(p['b'],mult)];p['end']=s
        order=list(range(len(p['A'])));rng.shuffle(order);p['A']=[p['A'][i]for i in order];p['b']=[p['b'][i]for i in order]
        out=construct_route(p);records.append({'name':'unknown_scale_'+str(k),**out['verified']})
    # Dense balanced core with two attached, unrelated coherent cycles.
    d=12;core=8;A=[[-int(i==j)for j in range(d)]for i in range(d)]
    A += [[int(i==j)for j in range(d)]for i in range(d)];b=[0]*d+[1]*d
    for i,j in combinations(range(core),2):
        row=[Q(0)]*d;row[i]=-1;row[j]=1;A.append(row);b.append(Q(1,3)+Q(i+j,100))
    for anchor,u,v,g in [(0,8,9,1-Q(1,2**120)),(3,10,11,1-Q(1,3**60))]:
        for x,y,t in [(anchor,u,Q(1)),(u,v,Q(1)),(v,anchor,g)]:
            row=[Q(0)]*d;row[x]=-t;row[y]=1;A.append(row);b.append(Q(1,4))
    p={'A':A,'b':b,'start':[0]*d,'end':[1]*d};out=construct_route(p)
    require(out['verified']['balanced_fundamental_cycles']>=20,'dense balanced core not exercised')
    records.append({'name':'dense_balanced_core_with_resonances',**out['verified']})
    (ROOT/'fixtures/dense_balanced_core_with_resonances.json').write_text(json.dumps(serial({'input':p,**out}),indent=2)+'\n')
    return records


def resonance_tests():
    results=[]
    for power in(8,40,120,240):
        eps=Q(1,2**power);A=[[-1,1],[1+eps,-1]];S=certify_structure(A)['certificate'];W=cone_witness(A,S,[0,1]);v=verify_cone(A,S,W)
        other=[[-(1+eps),1],[1,-1]];SS=certify_structure(other)['certificate'];ww=cone_witness(other,SS,[0,1]);vv=verify_cone(other,SS,ww)
        require(rat(vv['minimum_verified_squared_margin'])>=Q(1,3),'gain above one lost cone width')
        require(rat(v['minimum_verified_squared_margin'])>=Q(1,3),'coherent resonance narrowed the cone')
        require(rat(v['largest_inverse_entry'])>=2**power,'inverse blow-up missing')
        results.append({'epsilon_power':power,**v})
    # Exact valuation signs prove no single rational q>1 generates both gains.
    g1=1-Q(1,2**80);g2=1-Q(1,3**60)
    def valuation(n,p):
        out=0
        while n%p==0:n//=p;out+=1
        return out
    v21=valuation(g1.numerator,2)-valuation(g1.denominator,2)
    v22=valuation(g2.numerator,2)-valuation(g2.denominator,2)
    require(g1<1 and g2<1 and v21<0<v22,'noncommensurability certificate failed')
    return {'near_resonance_cones':results,'noncommensurate_cycle_gains':[str(g1),str(g2)],'two_adic_valuations':[v21,v22]}


def rejection_tests():
    p,_=cactus(5,precision=8);out=construct_route(p);S=out['certificate']['structure'];C=out['certificate'];names=[]
    def reject(name,call):
        try:call()
        except (ValueError,TypeError,KeyError,ZeroDivisionError,IndexError):names.append(name)
        else:raise AssertionError('accepted invalid certificate '+name)
    for key,value in [('matrix_sha256','bad'),('transport_product',1),('cycles',[])]:
        s=deepcopy(S);s[key]=value;reject(key,lambda s=s:verify_structure(p['A'],s))
    s=deepcopy(S);s['diagonal'][0]='-1';reject('negative_diagonal',lambda:verify_structure(p['A'],s))
    s=deepcopy(S);s['forest_rows']=s['forest_rows'][:-1];reject('incomplete_forest',lambda:verify_structure(p['A'],s))
    s=deepcopy(S);s['cycles'][0]['vertices'][1]=s['cycles'][0]['vertices'][0];reject('noncycle_vertices',lambda:verify_structure(p['A'],s))
    reject('incoherent_near_parallel_cycle',lambda:certify_structure([[1,-1],[1,-(1+Q(1,2**100))]]))
    reject('unbalanced_theta_overlap',lambda:certify_structure([[-1,1,0],[0,-1,1],[Q(1001,1000),0,-1],[-1,0,1]]))
    reject('unbalanced_dense_block',lambda:certify_structure([[-1,1,0],[0,-1,1],[-1,0,Q(1001,1000)]]))
    reject('same_sign_row',lambda:certify_structure([[1,1]]))
    reject('dense_row',lambda:certify_structure([[1,1,-1]]))
    reject('float',lambda:certify_structure([[1.0,-1]]))
    for key,value in [('visited_cone_witnesses',[]),('intrinsic_structure',None)]:
        c=deepcopy(C);c[key]=value;reject(key,lambda c=c:verify_route(p,c))
    c=deepcopy(C);c['visited_cone_witnesses'][0]['center']=['0']*5;reject('zero_cone_center',lambda:verify_route(p,c))
    c=deepcopy(C);c['visited_cone_witnesses'][0]['width_squared']=1;reject('false_width',lambda:verify_route(p,c))
    c=deepcopy(C);c['route_certificate']['route']=[c['route_certificate']['route'][0],c['route_certificate']['route'][-1]];reject('diagonal_as_edge',lambda:verify_route(p,c))
    c=deepcopy(C);c['route_certificate']['basis_steps']=c['route_certificate']['basis_steps'][1:];reject('missing_basis_pivot',lambda:verify_route(p,c))
    x=deepcopy(p);x['end']=[2]*5;reject('changed_target',lambda:verify_route(x,C))
    return {'count':len(names),'names':names}


def main():
    (ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True);start=time.monotonic()
    bases=basis_tests();print('basis audit',bases,flush=True)
    small,examples=small_tests();resonance=resonance_tests();large=large_tests();negative=rejection_tests()
    files=[ROOT/'scripts/coherent_gain_cones.py',ROOT/'scripts/test_coherent_gain_cones.py']+sorted((ROOT/'Solutions').glob('*.lean'))
    out={'status':'PASS','scope':'Exact original-H edges and rational cone certificates, not Lean or platform acceptance.',
         'basis_checks':bases,'small_totals':small,'small_examples':examples,'resonance_and_noncommensurability':resonance,
         'large_and_scaled_cases':large,'negative_controls':negative,
         'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files},
         'unchanged_dependency_sha256':{n:hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest()for n in['gain_lattice_certificate.py','gain_shadow_extension.py','signed_basis_shadow.py']},
         'elapsed_seconds':round(time.monotonic()-start,3)}
    (ROOT/'research/COHERENT_CONE_CHECK_2026-09-12.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':out['status'],'seconds':out['elapsed_seconds'],'small':small,'negative':negative['count'],'large_routes':[(x['name'],x['edges'])for x in large]},indent=2),flush=True)
if __name__=='__main__':main()
