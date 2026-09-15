#!/usr/bin/env python3
"""Independent graph, literal-subdivision, and rational original-edge tests.
Geometry utilities adapt the earlier local pseudoforest tests; that family and
carrier method are not claimed anew. New selected facets realize arbitrarily
many long incidence cycles sharing one label, rather than one cycle/component.
"""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from math import sin, cos, pi
from pathlib import Path
import argparse, copy, hashlib, json, random
import cactus_defect_refinement as C
from cactus_reference_segments import Segment

need = C.require

def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {k: serial(v) for k, v in x.items()}
    if isinstance(x, (tuple, list, set, frozenset)): return [serial(v) for v in x]
    return x

def high_union(K): return set().union(*K.higher()) if K.higher() else set()

def independent_graph(K):
    """Spanning-tree fundamental cycles, independent of Tarjan blocks."""
    G = C.incidence(K); tree = {v: set() for v in G}; seen = set(); extras = []; comps = 0
    for root in sorted(G):
        if root in seen: continue
        comps += 1; seen.add(root); queue = deque([root])
        while queue:
            v = queue.popleft()
            for w in sorted(G[v]):
                if w not in seen:
                    seen.add(w); queue.append(w); tree[v].add(w); tree[w].add(v)
                elif w not in tree[v] and v < w: extras.append((v, w))
    used = set(); cactus = True; long = 0
    for u, v in extras:
        previous = {u: None}; queue = deque([u])
        while v not in previous:
            x = queue.popleft()
            for y in tree[x]:
                if y not in previous: previous[y] = x; queue.append(y)
        cycle = {frozenset((u, v))}; x = v
        while previous[x] is not None:
            cycle.add(frozenset((x, previous[x]))); x = previous[x]
        if used & cycle: cactus = False
        used |= cycle; long += len(cycle) > 4
    return cactus, comps, len(extras), long


def generated_cactus(seed, rounds):
    rng = random.Random(seed); H = [{0, 1, 2}]; n = 3
    for _ in range(rounds):
        mode = rng.choice(('tree', 'label', 'high')); r = rng.randint(2, 6)
        if mode == 'tree':
            anchor = rng.choice(sorted(rng.choice(H))); size = rng.randint(2, 5)
            H.append({anchor, *range(n, n+size)}); n += size
        elif mode == 'label':
            anchor = rng.choice(sorted(rng.choice(H)))
            xs = [anchor, *range(n, n+r-1)]; n += r-1
            for j in range(r):
                size = rng.randint(1, 3); private = list(range(n, n+size)); n += size
                H.append({xs[j], xs[(j+1) % r], *private})
        else:
            old = rng.randrange(len(H)); xs = list(range(n, n+r)); n += r
            H[old] |= {xs[0], xs[1]}
            for j in range(r-1):
                size = rng.randint(1, 3); private = list(range(n, n+size)); n += size
                H.append({xs[(j+1) % r], xs[(j+2) % r], *private})
    pairs = [frozenset(e) for e in combinations(range(n), 2) if not any(set(e) <= N for N in H)]
    rng.shuffle(pairs)
    return C.Complex.create(n, H+pairs[:min(len(pairs), rounds//2)])


def bouquet(count, r=3, high_joint=False):
    H = []; n = 1
    if high_joint: H.append({0})
    for _ in range(count):
        if high_joint:
            xs = list(range(n, n+r)); n += r; H[0] |= set(xs[:2]); start = 1
        else:
            xs = [0, *range(n, n+r-1)]; n += r-1; start = 0
        for j in range(start, r):
            H.append({xs[j], xs[(j+1) % r], n}); n += 1
    return C.Complex.create(n, H)


def all_faces(K):
    return {frozenset(S) for r in range(K.n+1) for S in combinations(range(K.n), r) if K.face(S)}


def maximal(F): return C.base.ordered(S for S in F if not any(S < T for T in F))


def literal_check(K, p):
    F = maximal(all_faces(K)); checks = carriers = 0
    for s in p['steps']:
        E = frozenset(s['account']['edge']); z = K.n
        # Independent definition on maximal simplices, not the nonface identity.
        FF = [T for S in F for T in ([S] if not E <= S else [(S-{u}) | {z} for u in E])]
        expected = {frozenset(T) for S in FF for r in range(len(S)+1) for T in combinations(S, r)}
        J, _ = C.base.account(K, sorted(E))
        for r in range(J.n+1):
            for S in combinations(range(J.n), r):
                need(J.face(S) == (frozenset(S) in expected), 'literal stellar mismatch'); checks += 1
        if len({len(T) for T in FF}) == 1:
            d = len(FF[0])
            for S, T in combinations(FF, 2):
                if len(S & T) != d-1: continue
                A = (S-{z}) | E if z in S else S; B = (T-{z}) | E if z in T else T
                need(A in F and B in F and (A == B or len(A & B) == d-1), 'literal carrier chord'); carriers += 1
        K = J; F = C.base.ordered(FF)
    return checks, carriers


def abstract():
    counts = {'small_antichains': 0, 'small_cactus': 0, 'independent_graph_checks': 0,
              'literal_membership_checks': 0, 'literal_carrier_checks': 0,
              'random_cacti': 0, 'random_steps': 0, 'neutral_openings': 0,
              'negative_controls': 0}
    possible = [frozenset(S) for r in range(2, 5) for S in combinations(range(4), r)]
    for mask in range(1 << len(possible)):
        H = [S for j, S in enumerate(possible) if mask & (1 << j)]
        if C.base.ordered(H) != C.base.minimal(H): continue
        K = C.Complex.create(4, H); counts['small_antichains'] += 1
        a, _ = C.inspect(K); alt = independent_graph(K)
        need(a['cactus'] == alt[0], 'independent cactus mismatch'); counts['independent_graph_checks'] += 1
        if not a['cactus']: continue
        p = C.construct(K); counts['small_cactus'] += 1
        x, y = literal_check(K, p)
        counts['literal_membership_checks'] += x; counts['literal_carrier_checks'] += y
    for seed in range(160):
        K = generated_cactus(2026091500+seed, 1+seed % 10); p = C.construct(K); r = C.verify(K, p)
        counts['random_cacti'] += 1; counts['random_steps'] += r['subdivisions']; counts['neutral_openings'] += r['neutral_openings']
        for s in p['steps']:
            a, _ = C.inspect(K); alt = independent_graph(K)
            need(a['cactus'] == alt[0] and (a['components'], a['cycle_rank'], a['long_cycles']) == alt[1:], 'independent graph ledger mismatch')
            counts['independent_graph_checks'] += 1; K, _ = C.base.account(K, s['account']['edge'])
    family = []
    for high in (False, True):
        for n in (2, 3, 8, 16):
            for r in (2, 3, 5):
                K = bouquet(n, r, high); p = C.construct(K); out = C.verify(K, p)
                family.append({'joint': 'high' if high else 'label', 'cycles': n, 'cycle_high_nodes': r, **out})
    K = bouquet(3); p = C.construct(K)
    def bad(call):
        try: call()
        except (ValueError, KeyError, TypeError, IndexError): counts['negative_controls'] += 1; return
        raise AssertionError('invalid certificate accepted')
    mutations = [lambda q:q.update(input_sha256='wrong'), lambda q:q['steps'].pop(),
                 lambda q:q['steps'][0]['after'].update(long_cycles=0),
                 lambda q:q['steps'][0]['account'].update(created_higher_weight=0),
                 lambda q:q['initial'].update(linear_bound=999),
                 lambda q:q['steps'][0].update(kind='twin'),
                 lambda q:q['steps'][0]['account'].update(edge=[0, 0]),
                 lambda q:q['steps'][0]['before'].update(potential=999),
                 lambda q:q['terminal'].update(minimal_nonfaces=[[0, 1, 2]])]
    for mutation in mutations:
        q = copy.deepcopy(p); mutation(q); bad(lambda:C.verify(K, q))
    bad(lambda:C.construct(K, step_cap=0))
    # A theta incidence block has overlapping cycles, not merely many cycles.
    theta = C.Complex.create(6, [{0,1,2,3}, {0,1,4}, {0,2,5}])
    bad(lambda:C.construct(theta))
    cyc = C.Complex.create(7, [S for S in combinations(range(7),3)
                             if all((a-b)%7 not in (1,6) for a,b in combinations(S,2))])
    bad(lambda:C.construct(cyc))
    bad(lambda:C.Complex.create(4, [[0,1],[0,1,2]]))
    # Verifier does not call the planner.
    saved = C.select; C.select = lambda *args: (_ for _ in ()).throw(RuntimeError('selector forbidden'))
    try: need(C.verify(K, p)['status'] == 'PASS', 'saved replay failed')
    finally: C.select = saved
    return {'status': 'PASS', 'counts': counts, 'bouquets': family,
            'outside_cactus': {'theta': C.inspect(theta)[0], 'cyclic_7_4': C.inspect(cyc)[0]}}


def dot(x, y): return sum((a*b for a,b in zip(x,y)), Q(0))
def sub(x, y): return tuple(a-b for a,b in zip(x,y))
def cross(x, y): return (x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2], x[0]*y[1]-x[1]*y[0])

def solve(A, b):
    T = [list(row)+[v] for row,v in zip(A,b)]; n=len(A)
    for j in range(n):
        p=next((i for i in range(j,n) if T[i][j]),None); need(p is not None,'singular system')
        T[j],T[p]=T[p],T[j]; z=T[j][j]; T[j]=[x/z for x in T[j]]
        for i in range(n):
            if i!=j:
                a=T[i][j]; T[i]=[x-a*y for x,y in zip(T[i],T[j])]
    return tuple(row[-1] for row in T)

def support(points, face):
    a,b,c=[points[i] for i in sorted(face)]; normal=cross(sub(b,a),sub(c,a)); beta=dot(normal,a)
    if beta<0: normal=tuple(-x for x in normal); beta=-beta
    need(beta>0 and all(dot(normal,x)==beta if i in face else dot(normal,x)<beta for i,x in enumerate(points)), 'not entire strict triangle support')
    return normal,beta


def missing(n, facets):
    FS=set(map(frozenset,facets)); pairs={frozenset(e)for f in FS for e in combinations(f,2)}
    out=[S for S in combinations(range(n),2)if frozenset(S)not in pairs]
    out += [S for S in combinations(range(n),3)if frozenset(S)not in FS and all(frozenset(e)in pairs for e in combinations(S,2))]
    out += [S for S in combinations(range(n),4)if all(frozenset(e)in FS for e in combinations(S,3))]
    return C.Complex.create(n,out)


def geometric_bouquet(r):
    """Stack 3r specified facets of a capped 4r-antiprism.
    The selected triples form r loose cycles sharing only the bottom pole.
    Rounded trigonometry proposes rational points; ALL supports are exact.
    """
    q=4*r
    def xy(t):return (Q(round(100000*cos(t)),100000),Q(round(100000*sin(t)),100000))
    pts=[xy(2*pi*i/q)+(Q(-1),)for i in range(q)]+[xy(2*pi*(i+.5)/q)+(Q(1),)for i in range(q)]
    pts += [(Q(0),Q(0),Q(-2)),(Q(0),Q(0),Q(2))]; B,T=2*q,2*q+1
    F=[]
    for i in range(q):
        j=(i+1)%q; F += [{B,i,j},{T,q+i,q+j},{i,j,q+i},{j,q+i,q+j}]
    F=C.base.ordered(F); need(not missing(len(pts),F).higher(),'base is not flag')
    selected=[]
    for j in range(r):
        i=4*j; selected += [{B,i,i+1},{i+1,i+2,q+i+1},{B,i+2,i+3}]
    logs=[]
    for f in map(frozenset,selected):
        a,b=support(pts,f); center=tuple(sum((pts[i][j]for i in f),Q(0))/3 for j in range(3)); eps=Q(1)
        for h in F:
            if h==f:continue
            c,d=support(pts,h); gap=d-dot(c,center); need(gap>0,'not in facet relative interior')
            slope=dot(c,a)
            if slope>0:eps=min(eps,gap/(2*slope))
        z=tuple(x+eps*y for x,y in zip(center,a)); label=len(pts); pts.append(z)
        F=C.base.ordered([h for h in F if h!=f]+[{label,*e}for e in combinations(f,2)])
        for h in F:support(pts,h)
        logs.append({'facet':sorted(f),'new_label':label,'epsilon':eps,'point':z})
    K=missing(len(pts),F); need(set(K.higher())==set(map(frozenset,selected)),'wrong complete higher list')
    stats,_=C.inspect(K);need(stats['cactus'] and stats['components']==1 and stats['long_cycles']==r,'wrong geometric cactus')
    polar={f:tuple(x/b for x in a)for f in F for a,b in [support(pts,f)]}
    A=tuple(pts); b=(Q(1),)*len(A); anchors=[]
    for i in range(len(A)):
        xs=[x for f,x in polar.items()if i in f]; y=tuple(sum((x[j]for x in xs),Q(0))/len(xs)for j in range(3))
        need(all(dot(a,y)==1 if j==i else dot(a,y)<1 for j,a in enumerate(A)),'nongenuine original facet');anchors.append(y)
    return K,F,A,b,polar,anchors,logs


def edge_audit(A,b,x,y,F,H):
    d=len(x);F,H=set(F),set(H)
    need(F!=H and len(F)==len(H)==d and len(F&H)==d-1,'not a basis exchange')
    for z,S in [(x,F),(y,H)]:
        need(all(dot(a,z)==v if i in S else dot(a,z)<v for i,(a,v)in enumerate(zip(A,b))), 'invalid original vertex')
        need(solve([A[i]for i in sorted(S)],[b[i]for i in sorted(S)])==z,'incorrect active solution')
    direction=sub(y,x); ratios=[(v-dot(a,x))/dot(a,direction)for a,v in zip(A,b)if dot(a,direction)>0]
    need(ratios and min(ratios)==1,'not maximal original step')


def distances(F,start):
    D={start:0};queue=deque([start])
    while queue:
        f=queue.popleft()
        for h in F:
            if h not in D and len(f&h)==len(f)-1:D[h]=D[f]+1;queue.append(h)
    need(len(D)==len(F),'disconnected reference graph')
    return D


def full_hull(A,F):
    found=set();tests=0
    for f in combinations(range(len(A)),3):
        x,y,z=[A[i]for i in f];a=cross(sub(y,x),sub(z,x))
        if not any(a):continue
        b=dot(a,x);v=[dot(a,p)-b for p in A];tests+=1
        if all(t<=0 for t in v)or all(t>=0 for t in v):
            on=frozenset(i for i,t in enumerate(v)if t==0);need(len(on)==3,'nonsimplicial hull');found.add(on)
    need(found==set(F),'full hull omitted a facet')
    return tests


def geometry(fixtures):
    counts={'models':0,'routes':0,'original_edges':0,'refined_edges':0,'nonshortest':0,'full_hull_triangle_candidates':0}
    records=[]
    for r in (1,2,3):
        K,F,A,b,V,anchors,logs=geometric_bouquet(r);p=C.construct(K);v=C.verify(K,p)
        if r<=2:counts['full_hull_triangle_candidates']+=full_hull(A,F)
        rng=random.Random(771+r);pairs=list(combinations(F,2));rng.shuffle(pairs);pairs=pairs[:40]
        saved=[];old_w_descending=C.base.refine(K,policy='budget')
        for X,Y in pairs:
            out=C.flag_route(K,p,X,Y,3,Segment);path=list(map(frozenset,out['original_path']))
            for a,c in zip(path,path[1:]):edge_audit(A,b,V[a],V[c],a,c)
            D=distances(F,X);need(len(path)-1>=D[Y],'shorter than reference distance')
            counts['routes']+=1;counts['original_edges']+=out['original_edges'];counts['refined_edges']+=out['refined_edges'];counts['nonshortest']+=out['original_edges']>D[Y]
            if not saved:saved.append({'route':out,'coordinates':[V[f]for f in path]})
        counts['models']+=1
        records.append({'cycles':r,'dimension':3,'original_facets':K.n,'original_vertices':len(F),
                        **v,'all_pairs_structural_bound':K.n-3+v['subdivisions'],
                        'old_strict_budget_completion':old_w_descending['status'],
                        'old_strict_budget_steps':len(old_w_descending['steps']),
                        'sample_pairs':len(pairs)})
        if fixtures:
            fixtures.mkdir(parents=True,exist_ok=True)
            (fixtures/f'cactus-polytope-r{r}.json').write_text(json.dumps(serial({'complex':K.payload(),'A':A,'b':b,
                'facets':[sorted(f)for f in F],'anchors':anchors,'stacking':logs,'refinement':p,'saved_routes':saved}),sort_keys=True,indent=2)+'\n')
    return {'status':'PASS','counts':counts,'models':records,
            'scope':'Genuine rational simple 3-polytopes; higher-dimensional wedges and abstract nonspheres have separate evidence. Not shortestness or new best 3D diameter bounds.'}


def wedge(fixtures, r=3):
    K,F,A,b,V,anchors,logs=geometric_bouquet(r)
    X,Y=next((x,y)for x,y in combinations(F,2)if not x&y)
    chosen=[i for i in range(K.n)if i not in X|Y]; w=len(chosen);d=3+w;n=K.n
    AA=[list(a)+[Q(0)]*w for a in A];bb=list(b)
    for j,i in enumerate(chosen):
        AA[i][3+j]=Q(1);lo=[Q(0)]*d;lo[3+j]=Q(-1);AA.append(lo);bb.append(Q(0))
    AA=tuple(map(tuple,AA));bb=tuple(bb)
    subst={i:{i,n+j} for j,i in enumerate(chosen)}
    H=[set().union(*(subst.get(i,{i})for i in N))for N in K.missing]
    KK=C.Complex.create(n+w,H); pre=[(i,n+j)for j,i in enumerate(chosen)]
    p=C.with_twin_prelude(KK,pre);audit=C.verify_prelude(KK,p)
    start=frozenset(set(X)|set(range(n,n+w)));end=frozenset(set(Y)|set(chosen))
    need(not start&end,'high-dimensional endpoints share an original facet')
    route=C.flag_route(KK,p,start,end,d,Segment); path=list(map(frozenset,route['original_path']));coords={}
    for S in path:coords[S]=solve([AA[i]for i in sorted(S)],[bb[i]for i in sorted(S)])
    for S,T in zip(path,path[1:]):edge_audit(AA,bb,coords[S],coords[T],S,T)
    # Each old facet anchor lifts at t=0 for a chosen facet and half slack
    # otherwise; a lower facet uses zero instead. Every final facet is genuine.
    center=tuple(sum((z[j]for z in V.values()),Q(0))/len(V)for j in range(3));final_anchors=[]
    for target in range(n+w):
        x=anchors[target] if target<n and target not in chosen else center
        tt=[(1-dot(A[i],x))/2 for i in chosen]
        if target in chosen:tt[chosen.index(target)]=1-dot(A[target],x)
        if target>=n:tt[target-n]=Q(0)
        z=tuple(x)+tuple(tt)
        need(all(dot(a,z)==beta if j==target else dot(a,z)<beta for j,(a,beta)in enumerate(zip(AA,bb))),'wedge facet not genuine')
        final_anchors.append(z)
    report={'status':'PASS','cycles':r,'dimension':d,'original_facets':len(AA),
            'base_dimension':3,'base_facets':n,'wedges':w,'base_long_cycles':r,**audit,
            'route':{k:v for k,v in route.items()if k not in ('refined_path','original_path')},
            'common_original_facets':0,'genuine_facet_anchors':len(final_anchors),
            'enumerated_original_graph':False,'scope':'Proved wedge transport of complete base nonfaces; exact final original edges. Classical wedge estimates may be stronger.'}
    if fixtures:
        fixtures.mkdir(parents=True,exist_ok=True)
        (fixtures/'cactus-wedge-route.json').write_text(json.dumps(serial({'report':report,'complex':KK.payload(),'A':AA,'b':bb,
            'anchors':final_anchors,'refinement':p,'route':route,'coordinates':[coords[S]for S in path]}),sort_keys=True,indent=2)+'\n')
    return report


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=('abstract','geometry','wedge'),required=True)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--fixtures',type=Path);args=ap.parse_args()
    result=abstract()if args.stage=='abstract'else geometry(args.fixtures)if args.stage=='geometry'else wedge(args.fixtures)
    result['source_sha256']={s:hashlib.sha256(Path(__file__).with_name(s).read_bytes()).hexdigest()for s in
                            ('cactus_defect_refinement.py','test_cactus_defect_refinement.py','stellar_defect_budget.py','cactus_reference_segments.py')}
    args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result.get('counts',result),sort_keys=True))
if __name__=='__main__':main()
