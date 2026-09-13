#!/usr/bin/env python3
"""Exact exhaustive small bases/H-polytopes and nonenumerating signed routes."""
from signed_basis_shadow import *
from itertools import combinations,product
from collections import deque
from copy import deepcopy
from math import comb
import time
ROOT=Path(__file__).resolve().parents[1]


def rank(A):
    a=[list(map(F,r)) for r in A]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];v=a[k][j];a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v:a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def inverse(A):
    d=len(A);a=[list(map(F,r))+[F(i==j) for j in range(d)] for i,r in enumerate(A)];det=F(1)
    for j in range(d):
        p=next((i for i in range(j,d) if a[i][j]),None)
        if p is None:return None,F(0)
        if p!=j:a[j],a[p]=a[p],a[j];det=-det
        v=a[j][j];det*=v;a[j]=[x/v for x in a[j]]
        for i in range(d):
            if i!=j:
                v=a[i][j]
                if v:a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return tuple(tuple(r[d:]) for r in a),det


def library(d):
    return [tuple(int(i==j) for j in range(d)) for i in range(d)]+[tuple(int(k==i)+s*int(k==j) for k in range(d)) for i,j in combinations(range(d),2) for s in (-1,1)]


def all_vertices(A,b):
    A=[tuple(map(F,a)) for a in A];b=tuple(map(F,b));d=len(A[0]);vs=set()
    for ids in combinations(range(len(A)),d):
        inv,_=inverse([A[i] for i in ids])
        if inv is None:continue
        x=tuple(dot(r,[b[i] for i in ids]) for r in inv)
        if all(dot(a,x)<=z for a,z in zip(A,b)):vs.add(x)
    return sorted(vs)


def graph(A,b,vs):
    active=[{i for i,(a,z) in enumerate(zip(A,b)) if dot(a,x)==z} for x in vs];d=len(A[0]);G=[set()for _ in vs]
    for i,j in combinations(range(len(vs)),2):
        if rank([A[k] for k in active[i]&active[j]])==d-1:G[i].add(j);G[j].add(i)
    return G


def distances(G,s):
    dist={s:0};q=deque([s])
    while q:
        i=q.popleft()
        for j in G[i]:
            if j not in dist:dist[j]=dist[i]+1;q.append(j)
    return dist


def stable(d,pairs):
    return {'A':[[-int(i==j) for j in range(d)] for i in range(d)]+[[int(k==i)+int(k==j) for k in range(d)] for i,j in pairs],
            'b':[0]*d+[1]*len(pairs),'start':[0]*d,'end':['1/2']*d}


def odd_tree(d,dense=False):
    pairs=[(0,1),(1,2),(0,2)]+[(i,(i-1)//2) for i in range(3,d)];p=stable(d,pairs)
    if dense:
        rng=random.Random(211)
        for i,j in combinations(range(d),2):
            if (i,j) in pairs or (j,i) in pairs:continue
            p['A'].append([int(k==i)+int(k==j) for k in range(d)]);p['b'].append(F(1000+rng.randrange(1,900),1000))
    return p


def rotated_blocks(d,coupled=True):
    need(d%2==0,'even size')
    B=[]
    for i in range(0,d,2):
        for s in (-1,1):B.append([int(j==i)+s*int(j==i+1) for j in range(d)])
    p={'A':[[-x for x in a]for a in B]+B,'b':[0]*d+[1]*d,'start':[0]*d,'end':[int(i%2==0) for i in range(d)]}
    if coupled:
        for i in range(1,d-2,2):
            p['A'].append([int(j==i)+int(j==i+2) for j in range(d)]);p['b'].append(F(1,3))
    return p,B


def basis_suite():
    cnt=full=halves=0;worst=F(1);maxdet=0
    for d in range(1,5):
        L=library(d)
        for k in range(d+1):
            for ids in combinations(range(len(L)),k):
                A=[L[i]for i in ids];ks=signed_kernel(A,d);need(ks['rank']==rank(A),'signed component rank differs from Gaussian elimination');cnt+=1
                if k!=d:continue
                inv,det=inverse(A)
                if inv is None:continue
                got,_=basis_inverse(A);need(got==inv,'signed inverse differs from Gaussian inverse');full+=1;maxdet=max(maxdet,abs(det))
                halves+=int(any(abs(x)==F(1,2) for r in inv for x in r))
                for j in range(d):
                    inverse_norm=sum(inv[i][j]**2 for i in range(d));normal_norm=sum(x*x for x in A[j]);rho=1/(normal_norm*inverse_norm)
                    need(rho>=F(1,2*d),'delta-distance squared bound failed');worst=min(worst,rho)
    big,B=rotated_blocks(64);inv,det=inverse(B);got,_=basis_inverse(B)
    need(inv==got and abs(det)==2**32,'large-determinant inverse fixture failed')
    return {'signed_row_subsets':cnt,'nonsingular_bases':full,'bases_with_halves':halves,'max_small_determinant':maxdet,
            'minimum_observed_squared_relative_distance':worst,'large_basis_dimension':64,'large_basis_determinant':abs(det),
            'large_basis_max_inverse_entry':max(abs(x)for r in inv for x in r)}


def small_suite():
    cases=[('odd_triangle',stable(3,[(0,1),(1,2),(0,2)])),('stable_K4',stable(4,list(combinations(range(4),2)))),
           ('odd_cycle5',stable(5,[(0,1),(1,2),(2,3),(3,4),(0,4)])),('coupled_diamonds4',rotated_blocks(4)[0]),
           ('equality_line',{'A':[[1,-1],[-1,1],[-1,0],[1,1]],'b':[0,0,0,1],'start':[0,0],'end':['1/2','1/2']}),
           ('unbounded_signed_strip',{'A':[[-1,0],[1,0],[1,-1],[-1,-1]],'b':[0,1,0,0],'start':[0,0],'end':[1,1]}),
           ('duplicated_triangle',stable(3,[(0,1),(1,2),(0,2),(0,1)]))]
    totals={'instances':0,'vertices':0,'edges':0,'ordered_distances':0,'routes':0,'edge_occurrences':0,'stationary_pivots':0,'basis_pivots':0,'row_checks':0,'retries':0};records=[]
    for name,p in cases:
        A=[tuple(map(F,a))for a in p['A']];b=tuple(map(rat,p['b']));vs=all_vertices(A,b);G=graph(A,b,vs)
        info={'name':name,'vertices':len(vs),'edges':sum(map(len,G))//2,'routes':0,'maximum_route':0}
        for i,u in enumerate(vs):
            D=distances(G,i);totals['ordered_distances']+=len(D)
            for j in range(i+1):
                case=deepcopy(p);case['start']=u;case['end']=vs[j];out=construct(case);s=out['verified'];rr=[tuple(map(rat,x)) for x in out['certificate']['route']]
                need(all(q in vs for q in rr),'route contains unenumerated vertex')
                need(all(vs.index(y)in G[vs.index(x)]for x,y in zip(rr,rr[1:])),'route contains nonedge in independent graph')
                need(s['edges']>=D[j]and s['edges']<=36*s['intrinsic_dimension']**3,'route count check')
                for key,sk in [('edge_occurrences','edges'),('stationary_pivots','stationary_pivots'),('basis_pivots','basis_pivots'),('row_checks','row_checks')]:totals[key]+=s[sk]
                totals['retries']+=len(out['retry_failures']);totals['routes']+=1;info['routes']+=1;info['maximum_route']=max(info['maximum_route'],s['edges'])
        records.append(info);totals['instances']+=1;totals['vertices']+=len(vs);totals['edges']+=sum(map(len,G))//2
        print(name,info,flush=True)
    return totals,records


def extra_suite():
    cases=[('signed_odd_tree_12',odd_tree(12)),('signed_odd_tree_dense_24',odd_tree(24,True)),
           ('coupled_rotated_blocks_32',rotated_blocks(32)[0]),('coupled_rotated_blocks_48',rotated_blocks(48)[0])]
    records=[];rng=random.Random(211)
    for name,p in cases:
        begin=time.monotonic();out=construct(p);record={'name':name,**out['verified'],'seconds':round(time.monotonic()-begin,3)};records.append(record)
        (ROOT/f'fixtures/{name}.json').write_text(json.dumps(serial({'input':p,**out}),indent=2)+'\n')
        print(record,flush=True)
    base=odd_tree(8)
    for k in range(4):
        p=deepcopy(base);s=[F(rng.randrange(1,10),rng.randrange(1,10))for _ in range(8)];r=[F(rng.randrange(1,10),rng.randrange(1,10))for _ in p['A']]
        p['A']=[[F(v)*r[i]/s[j]for j,v in enumerate(a)]for i,a in enumerate(p['A'])];p['b']=[F(v)*r[i]for i,v in enumerate(p['b'])]
        p['start']=[rat(x)*a for x,a in zip(p['start'],s)];p['end']=[rat(x)*a for x,a in zip(p['end'],s)]
        order=list(range(len(r)));rng.shuffle(order);p['A']=[p['A'][i]for i in order];p['b']=[p['b'][i]for i in order]
        out=construct(p);records.append({'name':'diagonal_rescaling_'+str(k),**out['verified']})
    # Pin an entire odd-sign component in the endpoint common face.
    p=stable(3,[(0,1),(1,2),(0,2)]);p['A']=[a+[0]for a in p['A']]+[[0,0,0,-1],[0,0,0,1]];p['b']+= [0,1]
    p['start']=['1/2']*3+[0];p['end']=['1/2']*3+[1];out=construct(p);need(out['verified']['intrinsic_dimension']==1,'odd component failed to pin in quotient')
    records.append({'name':'odd_cycle_pinned_face',**out['verified']})
    return records


def exponential_star_suite():
    tested=0;rows_checked=0;cases=[]
    for d in (3,4,5,6,7,8,32,64):
        p=stable(d,[(0,1),(1,2),(0,2)]+[(0,i) for i in range(3,d)])
        p['start']=[1]+[0]*(d-1)
        masks=range(1<<(d-3)) if d<=8 else [0,1,(1<<(d-3))-1]+[random.Random(d+k).getrandbits(d-3) for k in range(5)]
        for mask in masks:
            p['end']=[F(1,2)]*3+[F((mask>>(i-3))&1,2)for i in range(3,d)]
            out=construct(p);need(out['verified']['edges']==1 and out['verified']['intrinsic_dimension']==1,'odd-star apex edge failed')
            if d<=8:
                common=[a for a,b in zip(p['A'],p['b'])if dot(a,p['start'])==b==dot(a,p['end'])]
                need(rank(common)==d-1,'independent odd-star edge rank failed')
            tested+=1;rows_checked+=out['verified']['row_checks']
        cases.append({'dimension':d,'rows':2*d,'proved_distinct_edge_direction_lower_bound':1<<(d-3),'edge_certificates':len(masks)})
    return {'edge_certificates':tested,'original_row_checks':rows_checked,'family':cases}


def negative_suite():
    p=rotated_blocks(4)[0];out=construct(p);c=out['certificate'];rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,ZeroDivisionError,IndexError):rejected.append(name)
        else:raise AssertionError('accepted bad certificate '+name)
    for name,key,val in [('dimension','dimension',1),('hash','input_sha256','bad'),('final','final_basis',[0,0,0,0])]:
        bad=deepcopy(c);bad[key]=val;reject(name,lambda bad=bad:verify(p,bad))
    for name,key,val in [('time','time','-1'),('leave','leave_position',999),('enter','enter',0),('alpha','alpha_constant',1000)]:
        bad=deepcopy(c);bad['basis_steps'][0][key]=val;reject(name,lambda bad=bad:verify(p,bad))
    bad=deepcopy(c);bad['basis_steps']=bad['basis_steps'][1:];reject('omitted_pivot',lambda:verify(p,bad))
    bad=deepcopy(c);bad['route']=[bad['route'][0],bad['route'][-1]];reject('diagonal_as_edge',lambda:verify(p,bad))
    bad=deepcopy(c);bad['source_weights'][0]='-1';reject('false_exposing_objective',lambda:verify(p,bad))
    bad=deepcopy(p);bad['A'][0][0]=0.1;reject('float',lambda:construct(bad))
    bad=deepcopy(p);bad['start']=[100]*4;reject('infeasible_source',lambda:construct(bad))
    bad=deepcopy(p);bad['start']=['1/3',0,'1/3',0];reject('nonvertex_source',lambda:construct(bad))
    bad=deepcopy(p);bad['A'].append([1,1,1,0]);bad['b'].append(10);reject('dense_row',lambda:construct(bad))
    eps=F(1,2**80)
    gain={'A':[[1,-1],[-(1+eps),1],[1,0]],'b':[0,0,1],'start':[0,0],'end':[1,1+eps]}
    reject('near_unit_unbalanced_gain_cycle',lambda:construct(gain))
    inv,det=inverse(gain['A'][:2]);need(abs(det)==eps and max(abs(x)for r in inv for x in r)>2**80,'gain imbalance sensitivity check')
    reject('pivot_cap',lambda:construct(p,limit=1))
    return {'rejected':len(rejected),'names':rejected,'near_unit_cycle_epsilon':eps,'inverse_largest_entry':max(abs(x)for r in inv for x in r)}


def main():
    start=time.monotonic();counts=basis_suite();small,recs=small_suite();large=extra_suite();stars=exponential_star_suite();neg=negative_suite()
    source={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for folder in ('scripts','Solutions')for p in sorted((ROOT/folder).glob('*'))if p.is_file()and p.suffix in ('.py','.lean')}
    out={'status':'PASS','scope':'Exact matrix and ORIGINAL edge checks; no Lean/platform verification or implementation of the published expected-length sampler.',
         'basis_checks':counts,'small_totals':small,'small_examples':recs,'additional_examples':large,'odd_star_direction_obstruction':stars,'negative_controls':neg,
         'source_sha256':source,'elapsed_seconds':round(time.monotonic()-start,3)}
    (ROOT/'research/SIGNED_BASIS_CHECK_2026-09-12.json').write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n');print(json.dumps(serial(out),indent=2))
if __name__=='__main__':main()
