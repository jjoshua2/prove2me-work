#!/usr/bin/env python3
"""Independent exact matrix, gauge, face, and original-edge regressions.

Small cases exhaust active bases; large route cases do not enumerate vertices.
The conditioner is verified independently of balancing, and the route verifier
never invokes path discovery. The external analytic existence theorem and this
finite sampler are intentionally different claims.
"""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from itertools import combinations,product
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,random,time
from gain_lattice_certificate import (
    rat,dot,serial,require,gain_kernel,gain_inverse,certify,verify as verify_condition,
    feasible_radius,cycle_gcd,parse_rows,tree_normalize,
)
from gain_shadow_extension import construct,verify as verify_route

ROOT=Path(__file__).resolve().parents[1]


def gauss_inverse(A):
    d=len(A);a=[list(map(rat,row))+[Q(i==j)for j in range(d)]for i,row in enumerate(A)]
    for j in range(d):
        p=next((i for i in range(j,d)if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
        for i in range(d):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return tuple(tuple(row[d:])for row in a)


def gauss_det(A):
    a=[list(map(rat,row))for row in A];d=len(a);out=Q(1)
    for j in range(d):
        p=next((i for i in range(j,d)if a[i][j]),None)
        if p is None:return Q(0)
        if p!=j:a[j],a[p]=a[p],a[j];out=-out
        v=a[j][j];out*=v
        for i in range(j+1,d):
            t=a[i][j]/v
            if t:a[i]=[x-t*y for x,y in zip(a[i],a[j])]
    return out


def rank(A):
    a=[list(map(rat,row))for row in A]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a))if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v:a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def normalized(A,c):
    s=list(map(rat,c['diagonal']));out=[]
    for row in A:
        r=tuple(rat(x)*t for x,t in zip(row,s));m=max(map(abs,r),default=Q(0))or Q(1)
        out.append(tuple(x/m for x in r))
    return out


def library(d):
    q=Q(d+1,d);A=[tuple(Q(i==j)for j in range(d))for i in range(d)]
    for i,j in combinations(range(d),2):
        for s in(-1,1):
            for k in(-1,0,1):A.append(tuple(Q(t==j)-s*q**k*int(t==i)for t in range(d)))
    return A,q


def matrix_checks():
    rng=random.Random(212);subsets=bases=proj=0;large_inverse=Q(0);records=[]
    for d in(2,3,4,6):
        A,q=library(d);packet=certify(A,q);c=packet['certificate'];N=normalized(A,c);U=rat(c['inverse_entry_bound'])
        choices=list(combinations(range(len(A)),d))if d<=3 else [tuple(sorted(rng.sample(range(len(A)),d)))for _ in range(700)]
        count=0;max_inv=Q(0)
        for ids in choices:
            rows=[N[i]for i in ids];actual=gauss_inverse(rows);expected_rank=rank(rows)
            require(gain_kernel(rows,d)['rank']==expected_rank,'gain-component/Gaussian rank mismatch');subsets+=1
            if actual is None:
                try:gain_inverse(rows)
                except ValueError:pass
                else:raise AssertionError('singular basis accepted')
                continue
            fast,_=gain_inverse(rows);require(fast==actual,'gain inverse/Gaussian mismatch');bases+=1;count+=1
            value=max(abs(x)for row in fast for x in row);max_inv=max(max_inv,value);large_inverse=max(large_inverse,value)
            require(value<=U,'global certified inverse bound failed')
            for j,row in enumerate(rows):
                sep=1/(dot(row,row)*sum(fast[i][j]**2 for i in range(d)))
                require(sep>=1/(2*d*U**2),'relative separation bound failed')
            # Independently project a basis onto one normal's orthogonal complement.
            if d>2 and proj<300:
                a=rows[-1];aa=dot(a,a)
                restricted=[tuple(x-dot(r,a)*y/aa for x,y in zip(r,a))for r in rows[:-1]]
                gram=[[dot(x,y)for y in restricted]for x in restricted];ginv=gauss_inverse(gram)
                require(ginv is not None,'projected basis lost independence')
                for j,r in enumerate(restricted):
                    sep=1/(ginv[j][j]*dot(r,r));require(sep>=1/(2*d*U**2),'face projection lost global separation')
                    proj+=1
        records.append({'dimension':d,'rows':len(A),'nonsingular_bases_checked':count,'largest_inverse':str(max_inv),'certified_bound':str(U)})
    # Magnitude-inconsistent cycles with nonunit-gain weighted kernels.
    for d in range(2,7):
        for _ in range(100):
            rows=[]
            for _ in range(rng.randrange(0,2*d)):
                i,j=rng.sample(range(d),2);a=[Q(0)]*d;a[i]=Q(rng.choice((-1,1))*rng.randrange(1,7),rng.randrange(1,7));a[j]=Q(rng.choice((-1,1)))
                rows.append(a)
            require(gain_kernel(rows,d)['rank']==rank(rows),'arbitrary gain rank failed');subsets+=1
    # Radius minimality: finite brute force, independent of Bellman--Ford.
    gauge_checks=0
    for _ in range(100):
        E=[(r,i,j,rng.randrange(-2,3))for r,(i,j)in enumerate([(0,1),(1,2),(0,2)])]
        best=None
        for p1,p2 in product(range(-5,6),repeat=2):
            p=[0,p1,p2];r=max(abs(k+p[i]-p[j])for _,i,j,k in E)
            best=r if best is None else min(best,r)
        for r in range(4):
            feasible,_=feasible_radius(3,E,r);require((feasible is not None)==(best<=r),'integer radius brute-force disagreement');gauge_checks+=1
    d=48;q=Q(d+1,d)
    integer_B=[[Q((d+1)*int(i==j)+d*int(j==(i+1)%d))for j in range(d)]for i in range(d)]
    determinant_value=gauss_det(integer_B)
    require(determinant_value==(d+1)**d-d**d,'integer gain-cycle determinant formula failed')
    packet=certify(integer_B,q);N=normalized(integer_B,packet['certificate']);inv,_=gain_inverse(N)
    require(inv==gauss_inverse(N),'large gain-cycle inverse mismatch')
    largest=max(abs(x)for row in inv for x in row)
    require(largest<=2,'large gain cycle unexpectedly ill conditioned')
    sharp=[[Q(i==j)for j in range(d)]for i in range(2,d)]
    sharp.extend([[Q(1),Q(-1)]+[Q(0)]*(d-2),[Q(1),-1/q]+[Q(0)]*(d-2)])
    inverse_sharp,_=gain_inverse(sharp);maximum=max(abs(x)for row in inverse_sharp for x in row)
    require(maximum==d+1,'near-resonance linear inverse lower bound failed')
    return {'kernel_collections':subsets,'nonsingular_bases':bases,'orthogonal_face_separation_checks':proj,
            'independent_gauge_checks':gauge_checks,'basis_examples':records,
            'large_quantized_basis':{'dimension':d,'integer_determinant':str(determinant_value),
                'largest_normalized_inverse':str(largest),'comparison_sharp_inverse':str(maximum),
                'two_additional_independent_basis_checks':2}}


def example(d,extra=0):
    q=Q(d+1,d);A=[[-int(i==j)for j in range(d)]for i in range(d)]
    A += [[Q(j==i)+q*int(j==(i+1)%d)for j in range(d)]for i in range(d)]
    b=[Q(0)]*d+[1+q]*d;r=random.Random(212)
    pairs=list(combinations(range(d),2));r.shuffle(pairs)
    for i,j in pairs[:extra]:
        k=r.choice((-1,0,1));sg=r.choice((-1,1));a=[Q(0)]*d;a[i]=sg*q**k;a[j]=1
        A.append(a);b.append(max(Q(0),sum(a))+Q(r.randrange(2,9),20))
    return {'A':A,'b':b,'start':[0]*d,'end':[1]*d,'gain_base':q}


def vertices(A,b):
    d=len(A[0]);out=set()
    for ids in combinations(range(len(A)),d):
        inv=gauss_inverse([A[i]for i in ids])
        if inv is None:continue
        x=tuple(dot(row,[b[i]for i in ids])for row in inv)
        if all(dot(a,x)<=t for a,t in zip(A,b)):out.add(x)
    return sorted(out)


def graph(A,b,vs):
    acts=[{i for i,(a,t)in enumerate(zip(A,b))if dot(a,v)==t}for v in vs];d=len(A[0]);G=[set()for _ in vs]
    for i,j in combinations(range(len(vs)),2):
        if rank([A[k]for k in acts[i]&acts[j]])==d-1:G[i].add(j);G[j].add(i)
    return G


def distances(G,u):
    D={u:0};q=deque([u])
    while q:
        i=q.popleft()
        for j in G[i]:
            if j not in D:D[j]=D[i]+1;q.append(j)
    return D


def route_checks():
    cases=[('cycle2',example(2)),('cycle4',example(4)),('cut_cycle4',example(4,4)),
           ('nonlattice_quadrilateral',{'A':[[-1,0],[0,-1],[2,1],[3,1]],'b':[0,0,3,4],'start':[0,0],'end':[1,1]}),
           ('pinned_gain_face',{'A':[[1,-1,0],[-1,1,0],[-2,1,0],[2,-1,0],[0,0,-1],[0,0,1]],
                               'b':[0,0,0,0,0,1],'start':[0,0,0],'end':[0,0,1],'gain_base':2})]
    deg=example(4)
    for a in [[1,0,1,0],[0,1,0,1],[Q(5,4),0,0,1]]:
        deg['A'].append(a);deg['b'].append(sum(a))
    deg['A'].append([0,0,0,0]);deg['b'].append(0)
    cases.append(('degenerate_gain_cycle',deg))
    eps=Q(1,2**80);q=1+eps
    cases.append(('near_resonant_triangle',{'A':[[1,-1],[-q,1],[1,0]],'b':[0,0,1],
                                         'start':[0,0],'end':[1,q],'gain_base':q}))
    counts={'models':0,'vertices':0,'edges':0,'ordered_distances':0,'routes':0,'route_edges':0,'pivots':0,'stationary_pivots':0,'row_checks':0};recs=[]
    for name,data in cases:
        A=parse_rows(data['A']);b=list(map(rat,data['b']));vs=vertices(A,b);G=graph(A,b,vs)
        counts['models']+=1;counts['vertices']+=len(vs);counts['edges']+=sum(map(len,G))//2;big=0
        for i,x in enumerate(vs):
            D=distances(G,i);counts['ordered_distances']+=len(D)
            for j in range(i+1):
                p=deepcopy(data);p['start']=x;p['end']=vs[j];out=construct(p);v=out['verified'];route=[tuple(map(rat,x))for x in out['certificate']['route']]
                require(all(x in vs for x in route),'unlisted original vertex')
                require(all(vs.index(y)in G[vs.index(x)]for x,y in zip(route,route[1:])),'independent graph rejects edge')
                require(v['edges']>=D[j],'route shorter than independent graph distance')
                counts['routes']+=1;counts['route_edges']+=v['edges'];counts['pivots']+=v['pivots'];counts['stationary_pivots']+=v['stationary_pivots'];counts['row_checks']+=v['row_checks'];big=max(big,v['edges'])
        recs.append({'name':name,'dimension':len(A[0]),'rows':len(A),'vertices':len(vs),'edges':sum(map(len,G))//2,'maximum_constructed_route':big})
    large=[]
    for d,e in[(12,24),(24,60),(32,100)]:
        data=example(d,e);out=construct(data);large.append({'name':f'quantized_{d}d',**out['verified']})
        (ROOT/f'fixtures/gain_lattice_{d}d.json').write_text(json.dumps(serial({'input':data,**out}),indent=2)+'\n')
    # Unknown arbitrary coordinate scales and row scaling, NOT only q-powers.
    r=random.Random(213);data=example(8,10)
    for k in range(4):
        p=deepcopy(data);s=[Q(r.randrange(1,20),r.randrange(1,20))for _ in range(8)]
        if k==3:s=[a*Q(2)**(30*i)for i,a in enumerate(s)]
        mult=[Q(r.randrange(1,10),r.randrange(1,10))for _ in p['A']]
        p['A']=[[rat(x)*mult[i]/s[j]for j,x in enumerate(row)]for i,row in enumerate(p['A'])]
        p['b']=[rat(x)*t for x,t in zip(p['b'],mult)];p['end']=s
        order=list(range(len(p['A'])));r.shuffle(order);p['A']=[p['A'][i]for i in order];p['b']=[p['b'][i]for i in order]
        out=construct(p);require(out['verified']['conditioning']['integer_gauge_radius']==1,'failed unknown scaling recovery')
        large.append({'name':'unknown_scaling_'+str(k),**out['verified']})
    return counts,recs,large


def determinant(u,v):return u[0]*v[1]-u[1]*v[0]


def crossratio_checks():
    eps=Q(1,2**80);rng=random.Random(214);rows=[]
    matrices=[((Q(1),Q(0)),(Q(0),Q(1))),((Q(1),Q(1,2**40)),(Q(-1),Q(1,2**40)))]
    while len(matrices)<50:
        T=tuple(tuple(Q(rng.randrange(-100,101),rng.randrange(1,20))for _ in range(2))for _ in range(2))
        if determinant(*T):matrices.append(T)
    for T in matrices:
        u,v=T;p=tuple(a+b for a,b in zip(u,v));q=tuple(a+(1+eps)*b for a,b in zip(u,v))
        sine=lambda a,b:determinant(a,b)**2/(dot(a,a)*dot(b,b))
        require(sine(p,q)*sine(u,v)==eps**2*sine(u,p)*sine(v,q),'affine-invariant cross ratio failed')
        minimum=min(sine(a,b)for a,b in combinations((u,v,p,q),2))
        require(minimum<=eps,'uniform all-basis conditioning was falsely recovered')
        rows.append(str(minimum))
    # Checking only a chosen fundamental-cycle gap misses cancellation.
    A=[[Q(1),Q(-1)],[Q(2),Q(-1)],[Q(2)+eps,Q(-1)]]
    inv=gauss_inverse(A[1:]);require(max(abs(x)for row in inv for x in row)>1/eps,'missing near-canceling chord obstruction')
    return {'dense_affine_preconditioners_checked':len(matrices),'epsilon':str(eps),
            'original_min_squared_separation':rows[0],'balanced_preconditioner_min_squared_separation':rows[1],
            'fundamental_cycle_gains':[str(Q(2)),str(Q(2)+eps)],
            'hidden_cycle_gain':str((2+eps)/2),'bad_chord_basis_largest_inverse':str(max(abs(x)for row in inv for x in row))}


def rejection_checks():
    p=example(4,4);out=construct(p);c=out['certificate'];g=c['conditioning'];badnames=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,ZeroDivisionError,IndexError):badnames.append(name)
        else:raise AssertionError('negative control accepted: '+name)
    for key,val in [('matrix_sha256','bad'),('integer_radius',0),('cycle_gcd',99),('inverse_entry_bound','1/100'),
                    ('cycle_gap_bound',1),('path_exponent_budget',0),('smaller_radius_negative_cycle',[])]:
        x=deepcopy(g);x[key]=val;reject('gain_'+key,lambda x=x:verify_condition(p['A'],x))
    x=deepcopy(g);x['diagonal'][0]='-1';reject('negative_scaling',lambda:verify_condition(p['A'],x))
    x=deepcopy(g);x['exponents'][4]=True;reject('boolean_exponent',lambda:verify_condition(p['A'],x))
    x=deepcopy(g);x['exponents'][4]=99;reject('false_original_gain',lambda:verify_condition(p['A'],x))
    x=deepcopy(g);x['smaller_radius_negative_cycle'][0]['from']=99;reject('bad_negative_cycle',lambda:verify_condition(p['A'],x))
    reject('nonlattice_cycle',lambda:certify([[2,-1],[3,-1]],2))
    reject('bad_base',lambda:certify(p['A'],1))
    reject('float_row',lambda:certify([[1.0,-1]],2))
    reject('dense_row',lambda:certify([[1,1,1]],2))
    for key,val in [('input_sha256','bad'),('dimension',1),('final_basis',[0,0,0,0]),('conditioning',None)]:
        x=deepcopy(c);x[key]=val;reject('route_'+key,lambda x=x:verify_route(p,x))
    x=deepcopy(c);x['basis_steps']=x['basis_steps'][1:];reject('missing_pivot',lambda:verify_route(p,x))
    x=deepcopy(c);x['basis_steps'][0]['alpha_constant']='99';reject('false_step',lambda:verify_route(p,x))
    x=deepcopy(c);x['route']=[x['route'][0],x['route'][-1]];reject('diagonal_as_edge',lambda:verify_route(p,x))
    x=deepcopy(p);x['end']=[2]*4;reject('infeasible_target',lambda:construct(x))
    x=deepcopy(p);x['start']=['1/10']*4;reject('nonvertex_source',lambda:construct(x))
    reject('pivot_cap',lambda:construct(p,limit=1))
    return {'rejected':len(badnames),'names':badnames}


def main():
    (ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True)
    start=time.monotonic();matrix=matrix_checks();counts,small,large=route_checks();cross=crossratio_checks();negative=rejection_checks()
    calibration=0
    for d in range(1,31):
        for R in(1,2,3,5):
            q=1+Q(1,d*R)
            for g in(1,2,d):
                U=q**((d-1)*R)/(1-q**(-g));require(U<=6*d*R,'calibrated inverse arithmetic failed');calibration+=1
    own=['gain_lattice_certificate.py','gain_shadow_extension.py','test_gain_lattice_routing.py']
    files=[ROOT/'scripts'/p for p in own]+sorted((ROOT/'Solutions').glob('*.lean'))
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}
    result={'status':'PASS','scope':'Exact finite matrix, gauge and ORIGINAL-H edge checks; not Lean/platform acceptance or a uniform sampler runtime theorem.',
            'matrix_checks':matrix,'small_route_totals':counts,'small_models':small,'large_and_scaled_routes':large,
            'cross_ratio_and_cycle_cancellation':cross,'negative_controls':negative,'calibrated_inverse_cases':calibration,
            'source_sha256':hashes,'unchanged_dependency_sha256':hashlib.sha256((ROOT/'scripts/signed_basis_shadow.py').read_bytes()).hexdigest(),
            'elapsed_seconds':round(time.monotonic()-start,3)}
    (ROOT/'research/GAIN_LATTICE_CHECK_2026-09-12.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
