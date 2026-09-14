#!/usr/bin/env python3
"""Independent small image hulls, unbounded fibres, and finite forgery tests.
Neither source vertices nor a projected graph are inputs to the new discoverer.
The reference vertex enumeration below is used only by small test fixtures.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib,json,random,time
import projected_face_discovery as D
from exact_farkas_lp import parse,rat,serial,require,dot
ROOT=Path(__file__).resolve().parents[1]


def inverse(A):
    n=len(A);M=[list(map(rat,a))+[Q(i==j) for j in range(n)] for i,a in enumerate(A)]
    for j in range(n):
        p=next((i for i in range(j,n) if M[i][j]),None)
        if p is None:return None
        M[j],M[p]=M[p],M[j];a=M[j][j];M[j]=[x/a for x in M[j]]
        for i in range(n):
            if i!=j:
                a=M[i][j]
                if a:M[i]=[x-a*y for x,y in zip(M[i],M[j])]
    return tuple(tuple(a[n:]) for a in M)


def rank(rows):
    if not rows:return 0
    M=[list(map(rat,row)) for row in rows];r=0
    for j in range(len(M[0])):
        p=next((i for i in range(r,len(M)) if M[i][j]),None)
        if p is None:continue
        M[r],M[p]=M[p],M[r];a=M[r][j];M[r]=[x/a for x in M[r]]
        for i in range(r+1,len(M)):
            a=M[i][j]
            if a:M[i]=[x-a*y for x,y in zip(M[i],M[r])]
        r+=1
        if r==len(M):break
    return r


def vertices(A,b):
    A,b=parse(A,b);n=len(A[0]);out=set()
    for I in combinations(range(len(A)),n):
        M=inverse([A[i] for i in I])
        if M is None:continue
        x=tuple(dot(a,[b[i] for i in I]) for a in M)
        if all(dot(a,x)<=t for a,t in zip(A,b)):out.add(x)
    return sorted(out)


def det(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])


def polygon(points):
    points=sorted(set(points));lower=[];upper=[]
    for p in points:
        while len(lower)>1 and det(lower[-2],lower[-1],p)<=0:lower.pop()
        lower.append(p)
    for p in reversed(points):
        while len(upper)>1 and det(upper[-2],upper[-1],p)<=0:upper.pop()
        upper.append(p)
    return lower[:-1]+upper[:-1]


def box(d):
    return [[sg*int(i==j) for j in range(d)] for sg in (-1,1) for i in range(d)], [0]*d+[1]*d


def small():
    A3,b3=box(3);A4,b4=box(4);eps=Q(1,8)
    cases=[('cube_hexagon',A3,b3,[[1,0,1],[0,1,1]]),
      ('cube4_octagon',A4,b4,[[1,0,1,2],[0,1,2,-1]]),
      ('near_parallel_cube_projection',A3,b3,[[1,0,1],[0,1,1+Q(1,2**120)]]),
      ('tetrahedron_projection',[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],[0,0,0,1],[[1,0,1],[0,1,1]]),
      ('pyramid_projection',[[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],[0,1,1,1,1],[[1,0,1],[0,1,-1]]),
      ('deformed_cube', [[-1,0,0],[1,0,0],[eps,-1,0],[eps,1,0],[0,eps,-1],[0,eps,1]],
       [0,1,0,1,0,1],[[0,1,0],[0,0,1]])]
    stats={'systems':0,'source_vertices_enumerated':0,'image_points':0,'image_hull_vertices':0,
           'queries':0,'edges':0,'no_edges':0,'transverse_refutations':0,'endpoint_refutations':0,'nonvertex_image_queries':0,'source_edges_not_image_edges':0}
    examples=[]
    for name,A,b,G in cases:
        V=vertices(A,b);Y=sorted(set(D.image(G,x) for x in V));H=polygon(Y)
        edges={frozenset((a,c)) for a,c in zip(H,H[1:]+H[:1])}
        for sx,sy in combinations(V,2):
            common=[a for a,t in zip(A,b) if dot(a,sx)==t==dot(a,sy)]
            iu,iv=D.image(G,sx),D.image(G,sy)
            if rank(common)==len(A[0])-1 and iu!=iv and frozenset((iu,iv)) not in edges:
                stats['source_edges_not_image_edges']+=1
        record={'name':name,'source_vertices':len(V),'image_points':len(Y),'hull_vertices':len(H),'queries':0,'edges':0}
        for u,v in combinations(Y,2):
            data={'A':A,'b':b,'G':G,'u':u,'v':v};out=D.discover(data);status=out['verified']['status']
            expected=frozenset((u,v)) in edges
            require((status=='EDGE')==expected,'independent hull disagrees with edge discovery')
            stats['queries']+=1;record['queries']+=1
            stats['nonvertex_image_queries']+=int(u not in H or v not in H)
            if expected:
                stats['edges']+=1;record['edges']+=1
            else:
                stats['no_edges']+=1
                key='transverse_refutations' if out['verified']['negative_kind']=='transverse_midpoint' else 'endpoint_refutations'
                stats[key]+=1
            if len(examples)<6 and (expected or out['verified'].get('negative_kind')=='transverse_midpoint'):
                examples.append({'input':data,**out})
        stats['systems']+=1;stats['source_vertices_enumerated']+=len(V);stats['image_points']+=len(Y);stats['image_hull_vertices']+=len(H)
        print(record,flush=True)
    return stats,examples


def unbounded_cube(d,cone=2,lineality=1):
    n=d+cone+lineality
    A=[[sg*int(i==j) for j in range(n)] for sg in (-1,1) for i in range(d)]
    b=[0]*d+[1]*d
    for i in range(d,d+cone):A.append([-int(i==j) for j in range(n)]);b.append(0)
    G=[[int(i==j) for j in range(n)] for i in range(d)]
    return {'A':A,'b':b,'G':G,'u':[0]*d,'v':[1]+[0]*(d-1)}


def affine(data,seed=917):
    rng=random.Random(seed);n=len(data['A'][0]);u=[Q(rng.choice((-1,1)),rng.randrange(2,7)) for _ in range(n)]
    v=[Q(rng.choice((-1,1)),rng.randrange(2,7)) for _ in range(n-1)]
    v.append(-sum((x*y for x,y in zip(u,v)),Q(0))/u[-1])
    T=[[Q(i==j)+u[i]*v[j] for j in range(n)] for i in range(n)]
    Ti=inverse(T);offset=[Q(rng.randrange(-4,5),9) for _ in range(n)]
    transform_row=lambda a:[sum((a[k]*Ti[k][j] for k in range(n)),Q(0)) for j in range(n)]
    A=[transform_row(a) for a in data['A']];G=[transform_row(g) for g in data['G']]
    b=[rat(t)+dot(a,offset) for a,t in zip(A,data['b'])]
    for j in range(len(A)):
        s=Q(rng.randrange(1,9),rng.randrange(1,9));A[j]=[s*x for x in A[j]];b[j]*=s
    perm=list(range(len(A)));rng.shuffle(perm)
    shift=D.image(G,offset)
    return {'A':[A[i] for i in perm],'b':[b[i] for i in perm],'G':G,
            'u':D.add(tuple(map(rat,data['u'])),shift),'v':D.add(tuple(map(rat,data['v'])),shift)}


def extra():
    cases=[]
    for d in (4,8,16):
        p=unbounded_cube(d);cases.append((f'unbounded_{d}d_edge',p,'EDGE'))
        p=deepcopy(p);p['v']=[1]*d;cases.append((f'unbounded_{d}d_diagonal',p,'NO_EDGE'))
    p=affine(unbounded_cube(3),seed=908);cases.append(('hidden_dense_edge',p,'EDGE'))
    p=unbounded_cube(3);p['v']=[1,1,1];p=affine(p,seed=909);cases.append(('hidden_dense_diagonal',p,'NO_EDGE'))
    p=unbounded_cube(2);p['v']=['1/2',0];cases.append(('truncated_endpoint',p,'NO_EDGE'))
    p={'A':[[-1,0],[1,0],[0,-1],[0,1]],'b':[0,2,0,0],'G':[[1,1],[2,2]],'u':[0,0],'v':[2,4]}
    cases.append(('lower_dimensional_image',p,'EDGE'))
    p={'A':[[-1,0]],'b':[0],'G':[[1,0]],'u':[0],'v':[1]};cases.append(('unbounded_image_ray',p,'NO_EDGE'))
    p=unbounded_cube(2);p['A'] += [[0]*len(p['A'][0]),[0]*len(p['A'][0]),p['A'][0]];p['b'] += [0,1,0]
    cases.append(('constant_duplicate_rows',p,'EDGE'))
    # Source nonnegative orthant has a bounded edge after adding just x1<=1;
    # image is unbounded, but this particular edge is genuine.
    p={'A':[[-1,0,0],[1,0,0],[0,-1,0]],'b':[0,1,0],'G':[[1,0,0],[0,1,0]],'u':[0,0],'v':[1,0]}
    cases.append(('bounded_edge_of_unbounded_image',p,'EDGE'))
    results=[];witnesses=[]
    for name,p,status in cases:
        start=time.monotonic();out=D.discover(p);require(out['verified']['status']==status,'boundary classification failed')
        results.append({'name':name,**out['verified'],'slack_LP_pivots':out['discovery']['slack_LP_pivots'],
                        'seconds':round(time.monotonic()-start,3)})
        witnesses.append({'input':p,**out})
        print(name,status,results[-1]['seconds'],flush=True)
    # Auditor must keep working without any discovery/linear algebra path.
    targets=['ExactLP','feasible_point','rank_one_modulo_rows','row_coefficients']
    saved={key:getattr(D,key) for key in targets};oldMatrix=D.sp.Matrix
    def forbidden(*a,**k):raise AssertionError('auditor invoked discovery')
    try:
        for key in targets:setattr(D,key,forbidden)
        D.sp.Matrix=forbidden
        for w in witnesses:D.verify(w['input'],w['certificate'])
    finally:
        for key,v in saved.items():setattr(D,key,v)
        D.sp.Matrix=oldMatrix
    return results,witnesses


def negatives():
    p=unbounded_cube(2);o=D.discover(p);c=o['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forged '+name)
    for key,value in [('problem_sha256','bad'),('endpoint_lifts',[])]:
        x=deepcopy(c);x[key]=value;reject(key,lambda x=x:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['zero_slack_duals']=[];reject('omitted_zero_slack_proof',lambda:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['anchor']=[0]*len(p['G'][0]);reject('non_midpoint_anchor',lambda:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['normal']=[0,0];reject('false_image_normal',lambda:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['positive_weights']=[0];reject('zero_selected_weight',lambda:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['selected_rows'].append(x['face_certificate']['selected_rows'][0]);reject('repeated_face_row',lambda:D.verify(p,x))
    x=deepcopy(c);x['face_certificate']['zero_slack_duals'][0]['dual']=[[0,'-1']];reject('negative_dual',lambda:D.verify(p,x))
    x=deepcopy(c);x['result']['edge_certificate']['residual'][0][0]='99';reject('false_rank_one_identity',lambda:D.verify(p,x))
    x=deepcopy(c);x['result']['edge_certificate']['upper']=[0]*len(p['A']);reject('false_endpoint_bound',lambda:D.verify(p,x))
    q=deepcopy(p);q['v']=[1,1];cc=D.discover(q)['certificate']
    x=deepcopy(cc);x['result']['plus']=x['result']['minus'];reject('false_transverse_midpoint',lambda:D.verify(q,x))
    x=deepcopy(cc);x['result']['plus']=[99]*len(p['G'][0]);reject('infeasible_transverse_point',lambda:D.verify(q,x))
    q=deepcopy(p);q['v']=['1/2',0];cc=D.discover(q)['certificate']
    x=deepcopy(cc);x['result']['outside_parameter']='1';reject('false_endpoint_extension',lambda:D.verify(q,x))
    q=deepcopy(p);q['u']=[0.0,0];reject('float_endpoint',lambda:D.discover(q))
    q=deepcopy(p);q['v']=q['u'];reject('collapsed_endpoints',lambda:D.discover(q))
    q=deepcopy(p);q['u']=[-1,0];reject('infeasible_image_endpoint',lambda:D.discover(q))
    reject('explicit_pivot_cap',lambda:D.discover(p,pivot_cap=1))
    return names


def main():
    ROOT.joinpath('fixtures').mkdir(exist_ok=True);start=time.monotonic()
    small_stats,examples=small();large,examples2=extra();bad=negatives()
    extraedges=sum(x['status']=='EDGE' for x in large)
    files=['scripts/projected_face_discovery.py','scripts/test_projected_face_discovery.py',
           'research/publication_packets/projected_face_discovery/solution.lean']
    report={'status':'PASS','scope':'Exact rational original-image edge decisions and minimal-face certificates. NOT Lean-extracted JSON or a route-length theorem.',
            'small_reference_hulls':small_stats,'boundary_and_large':large,'rejected':len(bad),'rejection_names':bad,
            'total_queries':small_stats['queries']+len(large),'total_edges':small_stats['edges']+extraedges,
            'total_non_edges':small_stats['no_edges']+len(large)-extraedges,'auditor_with_discovery_disabled':True,
            'source_sha256':{n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in files},
            'dependency_sha256':{n:hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest() for n in ['exact_farkas_lp.py','projected_face_certificate.py']},
            'seconds':round(time.monotonic()-start,3)}
    (ROOT/'fixtures/projected_discovery_examples.json').write_text(json.dumps(serial(examples+examples2),indent=2)+'\n')
    (ROOT/'research/PROJECTED_FACE_DISCOVERY_TESTS.json').write_text(json.dumps(serial(report),indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:report[k] for k in ['total_queries','total_edges','total_non_edges','rejected','seconds']},indent=2))
if __name__=='__main__':main()
