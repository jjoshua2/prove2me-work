#!/usr/bin/env python3
"""Independent finite-cycle classification, Gaussian cones and original-H routes.
Large inputs do not enumerate their cycles or vertices. Not a Lean verdict.
"""
from __future__ import annotations
from copy import deepcopy
from itertools import combinations, product
from pathlib import Path
from collections import deque
import hashlib, json, random, time, argparse
from fork_balanced_gain_cones import *
from coherent_gain_cones import certify_structure as old_structure
ROOT=Path(__file__).resolve().parents[1]


def gauss_inverse(A):
    d=len(A);a=[list(map(rat,r))+[Q(i==j) for j in range(d)] for i,r in enumerate(A)]
    for j in range(d):
        p=next((i for i in range(j,d) if a[i][j]),None)
        if p is None:return None
        a[j],a[p]=a[p],a[j];z=a[j][j];a[j]=[x/z for x in a[j]]
        for i in range(d):
            if i!=j:
                z=a[i][j]
                if z:a[i]=[x-z*y for x,y in zip(a[i],a[j])]
    return tuple(tuple(r[d:]) for r in a)


def gaussian_rank(A):
    a=[list(map(rat,r)) for r in A]
    if not a:return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None:continue
        a[k],a[p]=a[p],a[k];z=a[k][j];a[k]=[x/z for x in a[k]]
        for i in range(k+1,len(a)):
            z=a[i][j]
            if z:a[i]=[x-z*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a):break
    return k


def direct_cycle_property(d,E):
    G=adjacency(d,E)
    for start in range(d):
        def walk(u,seen,rs,gain,orient):
            for v,r,g in G[u]:
                if r in rs:continue
                forward=E[r][0]==u
                if v==start and len(rs)>=1:
                    ss=orient+[forward]
                    if not (all(ss) or not any(ss)) and gain*g!=1:return False
                elif v>start and v not in seen:
                    if not walk(v,seen|{v},rs|{r},gain*g,orient+[forward]):return False
            return True
        if not walk(start,{start},set(),Q(1),[]):return False
    return True


def classifier_tests():
    tested=accepted=0
    for d in range(1,5):
        pairs=list(combinations(range(d),2))
        for states in product(range(5),repeat=len(pairs)):
            E={}
            for r,((u,v),s) in enumerate(zip(pairs,states)):
                if s:E[r]=(u,v,Q(1 if s in (1,3) else 2)) if s<=2 else (v,u,Q(1 if s in (1,3) else 2))
            truth=direct_cycle_property(d,E)
            try:c=certify_forks(d,E);verify_forks(d,E,serial(c));got=True
            except ValueError:got=False
            require(truth==got,'fork/cycle enumeration mismatch');tested+=1;accepted+=int(got)
    parallel=0
    for choices in product(range(6),repeat=3):
        E={i:(0,1,[Q(1),Q(2),Q(1,2)][z%3]) if z<3 else (1,0,[Q(1),Q(2),Q(1,2)][z%3]) for i,z in enumerate(choices)}
        truth=direct_cycle_property(2,E)
        try:c=certify_forks(2,E);verify_forks(2,E,serial(c));got=True
        except ValueError:got=False
        require(truth==got,'parallel-edge mismatch');parallel+=1
    rng=random.Random(217);sampled=0
    for d in (5,6,7):
        for _ in range(100):
            pairs=rng.sample(list(combinations(range(d),2)),min(9,d*(d-1)//2));E={}
            for r,(u,v) in enumerate(pairs):
                if rng.randrange(2):u,v=v,u
                E[r]=(u,v,rng.choice((Q(1),Q(2),Q(1,2),Q(3,2))))
            truth=direct_cycle_property(d,E)
            try:c=certify_forks(d,E);verify_forks(d,E,serial(c));got=True
            except ValueError:got=False
            require(truth==got,'sampled cycle mismatch');sampled+=1
    return {'exhaustive_simple_gain_graphs':tested,'accepted_simple_graphs':accepted,'parallel_multigraphs':parallel,'sampled_gain_graphs':sampled}


def diamond_chain(r,bits=80):
    d=3*r+1;A=[[-int(i==j) for j in range(d)] for i in range(d)];b=[Q(0)]*d;levels=[0]*d;root=0
    for k in range(r):
        upper,lower,merge=3*k+1,3*k+2,3*k+3;levels[upper]=levels[lower]=2*k+1;levels[merge]=2*k+2
        for u,v,extra in [(root,upper,0),(upper,merge,0),(root,lower,0),(lower,merge,Q(1,3))]:
            a=[Q(0)]*d;a[u]=-1;a[v]=1;A.append(a);b.append(Q(levels[v]-levels[u])+extra)
        root=merge
    g=1-Q(1,2**bits);a=[Q(0)]*d;a[root]=-g;a[0]=1;A.append(a);b.append(1-g);T=1+g*2*r/(1-g)
    return {'A':A,'b':b,'start':[0]*d,'end':[T+x for x in levels]}


def parallel_paths(k,bits=40):
    d=k+2;s,t=0,d-1;A=[[-int(i==j) for j in range(d)] for i in range(d)];b=[Q(0)]*d
    for i in range(1,k+1):
        for u,v,extra in [(s,i,0),(i,t,Q(0) if i==1 else Q(i,7))]:
            a=[Q(0)]*d;a[u]=-1;a[v]=1;A.append(a);b.append(1+extra)
    g=1-Q(1,2**bits);a=[Q(0)]*d;a[t]=-g;a[s]=1;A.append(a);b.append(1-g);T=1+2*g/(1-g)
    return {'A':A,'b':b,'start':[0]*d,'end':[T]+[T+1]*k+[T+2]}


def dense_attachment():
    p=diamond_chain(1,8);d=6;A=[list(a)+[0,0] for a in p['A']];b=p['b'][:]
    for j in (4,5):a=[0]*d;a[j]=-1;A.append(a);b.append(0)
    for u,v,c in [(0,4,1),(4,5,1),(0,5,Q(7,3))]:
        a=[0]*d;a[u]=-1;a[v]=1;A.append(a);b.append(c)
    return {'A':A,'b':b,'start':[0]*d,'end':p['end']+[p['end'][0]+1,p['end'][0]+2]}


def basis_tests():
    rng=random.Random(218);records=[];subsets=valid=0;maxinv=Q(0)
    for name,p,cap in [('diamond4',diamond_chain(1,30),10000),('parallel5',parallel_paths(3,20),10000),('dense_attachment6',dense_attachment(),700),('double_diamond7',diamond_chain(2,10),500)]:
        c=certify_structure(p['A'])['certificate'];A=parse_rows(p['A']);N,_=normalize_rows(A,list(map(rat,c['diagonal'])));d=len(A[0]);gamma=rat(c['transport_bound'])
        ids=list(combinations(range(len(A)),d));full=len(ids)<=cap
        if not full:rng.shuffle(ids);ids=ids[:cap]
        nvalid=0
        for B in ids:
            inv=gauss_inverse([N[i] for i in B]);subsets+=1
            if inv is None:continue
            center=basis_center(N,B,gamma);vec=tuple(map(rat,center['center']));width=rat(center['width_squared'])
            for j in range(d):
                u=tuple(inv[i][j] for i in range(d));a=dot(u,vec)
                require(a>0 and a*a>=width*dot(u,u)*dot(vec,vec),'Gaussian cone check failed')
            valid+=1;nvalid+=1;maxinv=max(maxinv,max(abs(x) for row in inv for x in row))
        records.append({'name':name,'dimension':d,'rows':len(A),'subsets':len(ids),'nonsingular':nvalid,'exhaustive':full})
    return {'basis_subsets':subsets,'nonsingular_cones':valid,'largest_inverse':str(maxinv),'libraries':records}


def enumerate_vertices(A,b):
    out=set();d=len(A[0])
    for B in combinations(range(len(A)),d):
        inv=gauss_inverse([A[i] for i in B])
        if inv is None:continue
        x=tuple(dot(row,[b[i] for i in B]) for row in inv)
        if all(dot(a,x)<=z for a,z in zip(A,b)):out.add(x)
    return sorted(out)


def vertex_graph(A,b,vs):
    acts=[{i for i,(a,z) in enumerate(zip(A,b)) if dot(a,x)==z} for x in vs];G=[set() for _ in vs];d=len(A[0])
    for i,j in combinations(range(len(vs)),2):
        if gaussian_rank([A[k] for k in acts[i]&acts[j]])==d-1:G[i].add(j);G[j].add(i)
    return G


def distances(G,start):
    D={start:0};q=deque([start])
    while q:
        u=q.popleft()
        for v in G[u]:
            if v not in D:D[v]=D[u]+1;q.append(v)
    return D


def small_route_tests():
    deg=parallel_paths(2,8);deg['b'][-2]=1
    duplicate=deepcopy(deg);duplicate['A'].append([2*x for x in duplicate['A'][4]]);duplicate['b'].append(2*duplicate['b'][4]);duplicate['A'].append([0]*4);duplicate['b'].append(0)
    models=[('diamond4',diamond_chain(1,8),None),('three_parallel5',parallel_paths(3,8),None),('nonsimple_parallel4',deg,None),('duplicates_constants',duplicate,None),('dense_attachment6',dense_attachment(),30),('equality',{'A':[[1,-1],[-1,1],[-1,0],[1,0]],'b':[0,0,0,1],'start':[0,0],'end':[1,1]},None),('unbounded',{'A':[[1,-1],[-1,0],[1,0]],'b':[0,0,1],'start':[0,0],'end':[1,1]},None)]
    totals={'models':0,'vertices':0,'graph_edges':0,'ordered_distances':0,'routes':0,'edges':0,'pivots':0,'stationary':0,'face_checks':0,'original_evaluations':0};records=[]
    for name,p,cap in models:
        A=parse_rows(p['A']);b=list(map(rat,p['b']));V=enumerate_vertices(A,b);G=vertex_graph(A,b,V);DD=[distances(G,i) for i in range(len(V))];totals['ordered_distances']+=sum(map(len,DD))
        pairs=[(i,j) for i in range(len(V)) for j in range(i+1)]
        if cap and len(pairs)>cap:random.Random(219).shuffle(pairs);pairs=pairs[:cap]
        maxlen=0
        for i,j in pairs:
            data=deepcopy(p);data['start']=V[i];data['end']=V[j];out=construct_route(data);v=out['verified'];route=[tuple(map(rat,x)) for x in v['original_route']]
            require(all(x in V for x in route),'unlisted vertex');require(all(V.index(y) in G[V.index(x)] for x,y in zip(route,route[1:])),'independent graph rejects edge');require(v['edges']>=DD[i][j] and v['sample_within_bound'],'route length check failed')
            totals['routes']+=1;totals['edges']+=v['edges'];totals['pivots']+=v['basis_pivots'];totals['stationary']+=v['stationary_pivots'];totals['face_checks']+=int(v['intrinsic_dimension']>0);totals['original_evaluations']+=v['original_feasibility_evaluations'];maxlen=max(maxlen,v['edges'])
        totals['models']+=1;totals['vertices']+=len(V);totals['graph_edges']+=sum(map(len,G))//2
        rec={'name':name,'dimension':len(A[0]),'rows':len(A),'vertices':len(V),'graph_edges':sum(map(len,G))//2,'tested_pairs':len(pairs),'max_route':maxlen};records.append(rec);print(rec,flush=True)
    return {'totals':totals,'models':records}


def large_tests():
    records=[]
    for r in (4,8,12):
        p=diamond_chain(r,120);start=time.monotonic();out=construct_route(p);v=out['verified'];v.pop('original_route')
        rec={'name':f'diamond_chain_{r}','diamonds':r,'proved_unbalanced_directed_cycles':2**r,'structural_certificate_vertex_occurrences':verify_structure(p['A'],out['certificate']['structure'])['corridor_vertex_occurrences'],**v,'seconds':round(time.monotonic()-start,3)};records.append(rec)
        (ROOT/f'fixtures/overlapping_diamonds_{r}.json').write_text(json.dumps(serial({'input':p,**out}),indent=2)+'\n');print({k:rec[k] for k in ('name','dimension','edges','seconds')},flush=True)
        try:old_structure(p['A'])
        except ValueError:pass
        else:raise AssertionError('old isolated criterion unexpectedly accepted')
    r=20;p=diamond_chain(r,240);c=certify_structure(p['A']);s=list(map(rat,c['certificate']['diagonal']));N,m=normalize_rows(parse_rows(p['A']),s);end=[rat(x)/t for x,t in zip(p['end'],s)];bb=[rat(x)/t for x,t in zip(p['b'],m)];active=[i for i,(a,b) in enumerate(zip(N,bb)) if dot(a,end)==b]
    require(len(active)==len(end),'large target not simple');center=basis_center(N,active,rat(c['certificate']['transport_bound']));cone=verify_cone(N,center,c['certificate']['transport_bound'])
    million={'diamonds':r,'dimension':len(end),'rows':len(p['A']),'proved_unbalanced_cycles':2**r,'forks':c['verified']['forks'],'corridor_vertex_occurrences':c['verified']['corridor_vertex_occurrences'],'feasible_target_cone':cone,'classical_safe_diameter':c['verified']['classical_safe_diameter']}
    (ROOT/'fixtures/million_cycle_structure.json').write_text(json.dumps(serial({'input':p,'structure':c['certificate'],'target_cone':center,'summary':million}),indent=2)+'\n')
    # Two interacting-cycle blocks with unrelated gain scales; the shared
    # articulation causes no new simple mixed cycles. The target is degenerate.
    first=diamond_chain(2,120);second=diamond_chain(2,120);n1=len(first['start']);d=2*n1-1
    A=[list(a)+[0]*(n1-1) for a in first['A']];b=first['b'][:];g2=1-Q(1,3**60)
    second['A'][-1][-1]=-g2
    second['b'][-1]=(1-g2)*first['end'][0]-g2*4
    require(second['b'][-1]>0,'second block not feasible at zero')
    for a,z in zip(second['A'],second['b']):
        row=[Q(0)]*d
        for j,x in enumerate(a):row[0 if j==0 else n1+j-1]=x
        A.append(row);b.append(z)
    end=first['end']+[first['end'][0]+(second['end'][i]-second['end'][0]) for i in range(1,n1)]
    data={'A':A,'b':b,'start':[0]*d,'end':end};out=construct_route(data);v=out['verified'];v.pop('original_route')
    records.append({'name':'two_noncommensurate_overlap_blocks','proved_unbalanced_directed_cycles':8,**v})
    (ROOT/'fixtures/two_noncommensurate_overlap_blocks.json').write_text(json.dumps(serial({'input':data,**out}),indent=2)+'\n')
    rng=random.Random(220)
    for k in range(3):
        p=diamond_chain(2,40);d=len(p['start']);s=[Q(rng.randrange(1,20),rng.randrange(1,20))*Q(2)**(k*i*12) for i in range(d)];mult=[Q(rng.randrange(1,9),rng.randrange(1,9)) for _ in p['A']]
        p['A']=[[rat(x)*mult[i]/s[j] for j,x in enumerate(a)] for i,a in enumerate(p['A'])];p['b']=[rat(x)*t for x,t in zip(p['b'],mult)];p['end']=[rat(x)*t for x,t in zip(p['end'],s)];order=list(range(len(p['A'])));rng.shuffle(order);p['A']=[p['A'][i] for i in order];p['b']=[p['b'][i] for i in order]
        out=construct_route(p);v=out['verified'];v.pop('original_route');records.append({'name':'unknown_scaling_'+str(k),**v})
    return {'routes':records,'million_cycle_certificate':million}


def negative_tests():
    p=diamond_chain(1,20);out=construct_route(p);base=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,ZeroDivisionError,IndexError):names.append(name)
        else:raise AssertionError('negative control accepted: '+name)
    for key,value in [('matrix_sha256','bad'),('transport_bound',1),('forks',[])]:
        c=deepcopy(base['structure']);c[key]=value;reject(key,lambda c=c:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);c['forest_rows']=c['forest_rows'][:-1];reject('incomplete_forest',lambda:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);c['diagonal'][0]='-1';reject('negative_diagonal',lambda:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);c['forks'][0]['potentials'][0]='2';reject('false_corridor_gain',lambda:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);c['forks'][0]['corridor']=[];c['forks'][0]['potentials']=[];reject('false_separation',lambda:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);f=c['forks'][0];f['corridor']=[f['corridor'][0],f['corridor'][-1]];f['potentials']=['1','1'];reject('hidden_bypass',lambda:verify_structure(p['A'],c))
    c=deepcopy(base['structure']);c['forks'][0]['vertex']=True;reject('boolean_fork_vertex',lambda:verify_structure(p['A'],c))
    c=deepcopy(base);c['basis_cones']=[];reject('missing_cone',lambda:verify_route(p,c))
    c=deepcopy(base);c['basis_cones'][0]['center']=['0']*4;reject('zero_center',lambda:verify_route(p,c))
    c=deepcopy(base);c['basis_cones'][0]['width_squared']=1;reject('false_width',lambda:verify_route(p,c))
    c=deepcopy(base);c['face_forks']=[];reject('missing_face_forks',lambda:verify_route(p,c))
    c=deepcopy(base);c['route_certificate']['route']=[c['route_certificate']['route'][0],c['route_certificate']['route'][-1]];reject('diagonal_as_edge',lambda:verify_route(p,c))
    c=deepcopy(base);c['route_certificate']['basis_steps']=c['route_certificate']['basis_steps'][1:];reject('missing_pivot',lambda:verify_route(p,c))
    x=deepcopy(p);x['end']=[1]*4;reject('changed_requested_target',lambda:verify_route(x,base))
    x=deepcopy(p);x['A'][0][0]=1.0;reject('float_input',lambda:certify_structure(x['A']))
    reject('same_sign_row',lambda:certify_structure([[1,1]]));reject('dense_row',lambda:certify_structure([[1,-1,1]]))
    eps=Q(1,2**120);x=diamond_chain(1,120);x['A'][7][2]=-(1+eps);reject('unequal_path_gains',lambda:certify_structure(x['A']))
    reject('same_direction_parallel_resonance',lambda:verify_structure([[-1,1],[-(1+eps),1]],certify_structure([[-1,1],[-(1+eps),1]])['certificate']))
    E={0:(0,1,Q(1)),1:(0,2,Q(1)),2:(1,3,Q(1)),3:(2,3,Q(1)),4:(3,4,Q(2)),5:(4,5,Q(3)),6:(5,3,Q(1))};f=next(z for z in certify_forks(6,E) if z['vertex']==0);require(set(f['corridor'])=={1,2,3},'incorrect attachment corridor')
    return {'count':len(names),'names':names,'single_attachment_positive_control':True}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--part',choices=['classifier','basis','small','large','negative','all','assemble'],default='all');args=ap.parse_args();(ROOT/'fixtures').mkdir(exist_ok=True);(ROOT/'research').mkdir(exist_ok=True)
    tasks={'classifier':classifier_tests,'basis':basis_tests,'small':small_route_tests,'large':large_tests,'negative':negative_tests}
    for name,fn in tasks.items():
        if args.part in (name,'all'):
            start=time.monotonic();result=fn();result['elapsed_seconds']=round(time.monotonic()-start,3);(ROOT/f'research/FORK_{name.upper()}_CHECK.json').write_text(json.dumps(serial(result),indent=2,sort_keys=True)+'\n');print(name,json.dumps(serial(result))[:1000],flush=True)
    if args.part in ('all','assemble'):
        own=[ROOT/'scripts/fork_balanced_gain_cones.py',Path(__file__).resolve()]+sorted((ROOT/'Solutions').glob('*.lean'))
        out={'status':'PASS','scope':'Exact finite graph, original-H edge and cone checks, not Lean/platform acceptance.',
             'parts':{name:json.loads((ROOT/f'research/FORK_{name.upper()}_CHECK.json').read_text()) for name in tasks},
             'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in own},
             'unchanged_dependency_sha256':{p:hashlib.sha256((ROOT/'scripts'/p).read_bytes()).hexdigest() for p in ['coherent_gain_cones.py','gain_lattice_certificate.py','gain_shadow_extension.py','signed_basis_shadow.py']}}
        (ROOT/'research/FORK_BALANCE_CHECK_2026-09-13.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
if __name__=='__main__':main()
