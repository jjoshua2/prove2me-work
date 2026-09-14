#!/usr/bin/env python3
"""Exact independent hulls and failure controls. Enumeration is TEST-ONLY."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from math import gcd,lcm
from pathlib import Path
import argparse,hashlib,json,time
import image_tangent_pivot as P
from exact_farkas_lp import rat,serial,dot,require
ROOT=Path(__file__).resolve().parents[1]

def rref(rows,n):
    a=[list(row) for row in rows];k=0;piv=[]
    for j in range(n):
        i=next((i for i in range(k,len(a)) if a[i][j]),None)
        if i is None:continue
        a[i],a[k]=a[k],a[i];s=a[k][j];a[k]=[x/s for x in a[k]]
        for i in range(len(a)):
            if i!=k and a[i][j]:
                s=a[i][j];a[i]=[x-s*y for x,y in zip(a[i],a[k])]
        piv.append(j);k+=1
        if k==len(a):break
    return a,piv

def rank(rows,n):return len(rref(rows,n)[1])
def solve(A,b):
    n=len(A[0]);a,p=rref([list(row)+[rhs] for row,rhs in zip(A,b)],n)
    if len(p)!=n or any(not any(r[:n]) and r[n] for r in a):return None
    x=[Q(0)]*n
    for row,j in zip(a,p):x[j]=row[n]
    return tuple(x)

def source_vertices(A,b):
    n=len(A[0]);V=set()
    for I in combinations(range(len(A)),n):
        x=solve([A[i] for i in I],[b[i] for i in I])
        if x is not None and P.feasible(A,b,x):V.add(x)
    return sorted(V)

def hull(points,p):
    points=sorted(set(points));rows=set()
    for I in combinations(range(len(points)),p):
        x=points[I[0]];a,piv=rref([P.sub(points[i],x) for i in I[1:]],p)
        if len(piv)!=p-1:continue
        free=next(j for j in range(p) if j not in piv);v=[Q(0)]*p;v[free]=1
        for row,j in zip(a,piv):v[j]=-row[free]
        b=dot(v,x);vals=[dot(v,z)-b for z in points]
        if all(z<=0 for z in vals) and any(z<0 for z in vals):pass
        elif all(z>=0 for z in vals) and any(z>0 for z in vals):v=P.mul(-1,v);b=-b
        else:continue
        row=tuple(v)+(b,);den=lcm(*(z.denominator for z in row));ints=tuple(int(z*den) for z in row);g=gcd(*ints)
        rows.add(tuple(Q(z//g) for z in ints))
    A=[r[:p] for r in sorted(rows)];b=[r[p] for r in sorted(rows)]
    V=[x for x in points if rank([a for a,t in zip(A,b) if dot(a,x)==t],p)==p]
    require(V,'empty independent hull')
    active=[{j for j,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t} for x in V];G=[set() for x in V]
    for i,j in combinations(range(len(V)),2):
        if rank([A[k] for k in active[i]&active[j]],p)==p-1:G[i].add(j);G[j].add(i)
    return A,b,V,G

def bfs(G,s):
    dist={s:0};q=deque([s])
    while q:
        i=q.popleft()
        for j in G[i]:
            if j not in dist:dist[j]=dist[i]+1;q.append(j)
    return dist

def cube(n):return [[sg*int(i==j) for j in range(n)] for sg in(-1,1) for i in range(n)],[0]*n+[1]*n
def identity(n):return [[int(i==j) for j in range(n)] for i in range(n)]

def small_stage():
    models=[('square',*cube(2),identity(2)),('triangle',[[-1,0],[0,-1],[1,1]],[0,0,1],identity(2)),
        ('pentagon',[[-1,0],[0,-1],[1,0],[0,1],[1,1]],[0,0,2,2,3],identity(2)),
        ('octahedron',[list(s) for s in product((-1,1),repeat=3)],[1]*8,identity(3)),
        ('cube3',*cube(3),identity(3)),
        ('pyramid',[[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],[0,1,1,1,1],identity(3)),
        ('cube_hexagon',*cube(3),[[1,1,0],[0,1,1]]),
        ('cube_octagon',*cube(4),[[1,2,3,-1],[3,1,-2,4]]),
        ('simplex_shadow',[[-1,0,0],[0,-1,0],[0,0,-1],[1,1,1]],[0,0,0,1],[[1,0,1],[0,1,1]])]
    totals=dict.fromkeys(['models','image_vertices','image_edges','routes','route_edges','ordered_graph_distances',
            'normalized_slope_comparisons','nonshortest_routes','source_edges_not_image_edges'],0)
    examples=[];saved=[]
    for name,aa,bb,gg in models:
        A,b=P.parse(aa,bb);G=tuple(tuple(map(rat,g)) for g in gg);S=source_vertices(A,b)
        IA,ib,V,H=hull([P.im(G,x) for x in S],len(G));dist=[bfs(H,i) for i in range(len(V))]
        act=[{i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t} for x in S];badproj=0
        for i,j in combinations(range(len(S)),2):
            if rank([A[k] for k in act[i]&act[j]],len(A[0]))==len(A[0])-1:
                x,y=P.im(G,S[i]),P.im(G,S[j])
                if x!=y and (x not in V or y not in V or V.index(y) not in H[V.index(x)]):badproj+=1
        nr=ne=ns=0
        for i,u in enumerate(V):
            for j,v in enumerate(V):
                data={'A':A,'b':b,'G':G,'u':u,'v':v};out=P.construct(data);cert=out['certificate'];report=out['verified']
                route=[u]+[tuple(map(rat,s['to'])) for s in cert['steps']]
                require(all(x in V for x in route),'selected point is not an image vertex')
                for k,step in enumerate(cert['steps']):
                    x,y=route[k:k+2];ix,iy=V.index(x),V.index(y);require(iy in H[ix],'not an independent image edge')
                    c=tuple(map(rat,cert['target_vertex']['normal']));h=P.mul(-1,tuple(map(rat,step['start_vertex']['normal'])))
                    slope=dot(c,P.sub(y,x))/dot(h,P.sub(y,x))
                    for jj in H[ix]:
                        delta=P.sub(V[jj],x);require(dot(h,delta)>0,'nonpositive ray height')
                        require(dot(c,delta)/dot(h,delta)<=slope,'normalized slope not maximal');totals['normalized_slope_comparisons']+=1
                require(report['original_image_edges']>=dist[i][j],'shorter than independent graph distance')
                ns+=report['original_image_edges']>dist[i][j];nr+=1;ne+=report['original_image_edges']
                if len(saved)<4 and report['original_image_edges']>=2:saved.append({'input':serial(data),**out})
        totals['models']+=1;totals['image_vertices']+=len(V);totals['image_edges']+=sum(map(len,H))//2
        totals['ordered_graph_distances']+=sum(map(len,dist));totals['routes']+=nr;totals['route_edges']+=ne
        totals['nonshortest_routes']+=ns;totals['source_edges_not_image_edges']+=badproj
        ex={'name':name,'source_vertices':len(S),'image_vertices':len(V),'image_facets':len(IA),'source_rows':len(A),
            'routes':nr,'edges':ne,'nonshortest':ns,'source_bad_projections':badproj};examples.append(ex);print(ex,flush=True)
    (ROOT/'fixtures/image_tangent_small.json').write_text(json.dumps(saved,indent=2)+'\n')
    return {'totals':totals,'examples':examples}

def paired_cube(p):
    n=2*p+1;A=[];b=[]
    for j in range(2*p):
        for s in(-1,1):A.append([s*int(i==j) for i in range(n)]);b.append(0 if s<0 else 1)
    return {'A':A,'b':b,'G':[[int(j in (2*i,2*i+1)) for j in range(n)] for i in range(p)],'u':[0]*p,'v':[2]*p}

def extra_stage():
    cases=[('paired_cube_lineality_'+str(p),paired_cube(p)) for p in(2,4,8)]
    eps=Q(1,2**120);A,b=cube(2)
    cases.append(('thin_projection',{'A':A,'b':b,'G':[[1,0],[1,eps]],'u':[0,0],'v':[1,1+eps]}))
    cases.append(('lower_dimensional_image',{'A':[a+[0] for a in A],'b':b,'G':[[1,0,0],[0,1,0],[1,2,0]],'u':[0,0,0],'v':[1,1,3]}))
    base=paired_cube(2);T=[[Q(int(i==j))+Q((i+1)*(j+1),100) for j in range(5)] for i in range(5)]
    iv=[solve(T,[Q(int(i==j)) for i in range(5)]) for j in range(5)];inv=list(map(list,zip(*iv)));shift=[Q(i-2,7) for i in range(5)]
    mulrow=lambda a:tuple(sum(Q(a[i])*inv[i][j] for i in range(5)) for j in range(5))
    AA=[mulrow(a) for a in base['A']];bb=[Q(t)+dot(a,shift) for a,t in zip(AA,base['b'])]
    GG=[mulrow(g) for g in base['G']];offset=P.im(GG,shift)
    cases.append(('dense_source_chart',{'A':AA,'b':bb,'G':GG,'u':offset,'v':P.add(offset,(Q(2),Q(2)))}))
    rec=[];premature=0;source_nonadj=0
    for name,data in cases:
        start=time.monotonic();out=P.construct(data);A,b,G,u,v=P.read(data)
        for step in out['certificate']['steps']:
            x=tuple(map(rat,step['start_vertex']['anchor']));d=tuple(map(rat,step['lex_optima'][-1]['point']))
            bound=min([(t-dot(a,x))/dot(a,d) for a,t in zip(A,b) if dot(a,d)>0],default=None);actual=rat(step['ray_optimum']['value'])
            if bound is not None and bound<actual:premature+=1
            y=tuple(map(rat,step['ray_optimum']['point']))[:-1];shared=[a for a,t in zip(A,b) if dot(a,x)==t==dot(a,y)]
            if rank(shared,len(A[0]))<len(A[0])-1:source_nonadj+=1
        rec.append({'name':name,'source_dimension':len(A[0]),'image_ambient_dimension':len(G),
            'original_image_edges':out['verified']['original_image_edges'],'seconds':round(time.monotonic()-start,3)})
        print(rec[-1],flush=True);(ROOT/f'fixtures/tangent_{name}.json').write_text(json.dumps(serial({'input':data,**out}),indent=2)+'\n')
    require(premature>0,'missing premature source-ray example');require(source_nonadj>0,'missing nonedge source lifts')
    return {'examples':rec,'routes':len(rec),'edges':sum(x['original_image_edges'] for x in rec),
            'fixed_source_line_stops_prematurely':premature,'source_lift_steps_not_source_edges':source_nonadj}

def negative_stage():
    data=paired_cube(2);out=P.construct(data);cert=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted forgery '+name)
    for key,value in [('problem_sha256','bad'),('image_boundedness',[]),('steps',[])]:
        c=deepcopy(cert);c[key]=value;reject(key,lambda c=c:P.verify(data,c))
    c=deepcopy(cert);c['target_vertex']['image_rows'][0]=['0']*len(c['target_vertex']['rows']);reject('false_target_singleton',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['lex_optima'].pop();reject('incomplete_lex_ties',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['ray_vertex']['zero_duals'].pop();reject('missing_ray_fibre_dual',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['ray_optimum']['value']='0';reject('zero_length',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['ray_optimum']['value']='1/2';reject('premature_source_block',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['ray_optimum']['dual']=[[0,'-1']];reject('negative_endpoint_dual',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['to']=data['v'];reject('diagonal_as_edge',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['start_vertex']['normal']=['0','0'];reject('false_normalization',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps'][0]['lex_optima'][0]['value']='99';reject('false_normalized_optimum',lambda:P.verify(data,c))
    c=deepcopy(cert);c['steps']=c['steps'][::-1];reject('reordered_path',lambda:P.verify(data,c))
    bad=deepcopy(data);bad['u']=[1,1];reject('nonvertex_start',lambda:P.construct(bad))
    bad=deepcopy(data);bad['v']=[1,1];reject('nonvertex_target',lambda:P.construct(bad))
    reject('route_cap',lambda:P.construct(data,edge_cap=0));reject('pivot_cap',lambda:P.construct(data,pivot_cap=1))
    bad=deepcopy(data);bad['G'][0][0]=1.0;reject('floating_projection',lambda:P.construct(bad))
    A,b=P.parse(*cube(2));G=tuple(tuple(map(Q,g)) for g in identity(2));M,rhs=P.tangent_system(A,[0,1],G,(Q(1),Q(1)))
    reject('optimal_diagonal_not_ray_vertex',lambda:P.discover_vertex(M,rhs,G,(Q(1,2),Q(1,2))))
    bad={'A':[[-1,0],[0,-1]],'b':[0,0],'G':identity(2),'u':[0,0],'v':[1,1]};reject('unbounded_image',lambda:P.construct(bad))
    old=(P.ExactLP,P.feasible_point,P.row_repr,P.discover_vertex)
    def forbidden(*args,**kwargs):raise RuntimeError('auditor invoked discovery')
    P.ExactLP=P.feasible_point=P.row_repr=P.discover_vertex=forbidden
    try:report=P.verify(data,cert)
    finally:P.ExactLP,P.feasible_point,P.row_repr,P.discover_vertex=old
    return {'rejected':len(names),'names':names,'auditor_with_discovery_disabled':report['status'],'square_optimal_slice_midpoint_rejected':True}

def hashes():
    files=[ROOT/'scripts'/n for n in ['image_tangent_pivot.py','test_image_tangent_pivot.py','exact_farkas_lp.py']]
    files.append(ROOT/'research/publication_packets/normalized_tangent_image_edge/solution.lean')
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['small','extra','negative','assemble']);a=ap.parse_args()
    for stage in (['small','extra','negative'] if a.stage is None else [a.stage]):
        if stage=='assemble':continue
        start=time.monotonic();r=globals()[stage+'_stage']();o={'status':'PASS','source_sha256':hashes(),'result':r,'seconds':round(time.monotonic()-start,3)}
        (ROOT/f'research/IMAGE_TANGENT_STAGE_{stage}.json').write_text(json.dumps(serial(o),indent=2,sort_keys=True)+'\n');print(stage,'PASS',o['seconds'],flush=True)
    if a.stage is None or a.stage=='assemble':
        stages={s:json.loads((ROOT/f'research/IMAGE_TANGENT_STAGE_{s}.json').read_text()) for s in ['small','extra','negative']}
        require(all(o['status']=='PASS' and o['source_sha256']==hashes() for o in stages.values()),'stale test stage')
        s=stages['small']['result']['totals'];e=stages['extra']['result']
        o={'status':'PASS','source_sha256':hashes(),'route_certificates':s['routes']+e['routes'],
            'original_image_edges':s['route_edges']+e['edges'],'stages':stages,
            'scope':'Exact software regression, not a polynomial route bound or a Lean-extracted instance verdict.'}
        (ROOT/'research/IMAGE_TANGENT_SELECTION_TESTS.json').write_text(json.dumps(serial(o),indent=2,sort_keys=True)+'\n');print('TOTAL',o['route_certificates'],o['original_image_edges'],flush=True)
if __name__=='__main__':main()
