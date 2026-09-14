#!/usr/bin/env python3
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random,time
import sympy as sp
import projected_face_certificate as pc

ROOT=Path(__file__).resolve().parents[1]


def vertices(A,b):
    n=len(A[0]);out=set()
    for ids in combinations(range(len(A)),n):
        M=sp.Matrix([A[i] for i in ids]);r=sp.Matrix([b[i] for i in ids])
        if M.det()==0:continue
        x=tuple(Q(str(v)) for v in M.inv()*r)
        if all(pc.dot(a,x)<=beta for a,beta in zip(A,b)):out.add(x)
    return sorted(out)


def cross(o,a,b):return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])

def hull(points):
    pts=sorted(set(tuple(p) for p in points))
    def chain(ps):
        out=[]
        for p in ps:
            while len(out)>1 and cross(out[-2],out[-1],p)<=0:out.pop()
            out.append(p)
        return out
    return chain(pts)[:-1]+chain(reversed(pts))[:-1]


def rank(rows,n):return int(sp.Matrix(rows).rank()) if rows else 0


def image_edges(A,b,G,V):
    H=hull([pc.apply(G,x) for x in V]);certs=[]
    for i,u in enumerate(H):
        v=H[(i+1)%len(H)];delta=[v[j]-u[j] for j in range(2)]
        f=[delta[1],-delta[0]];beta=pc.dot(f,u)
        face=[x for x in V if pc.dot(f,pc.apply(G,x))==beta]
        pc.require(all(pc.dot(f,pc.apply(G,x))<=beta for x in V),'reference normal points inward')
        J=[j for j,a in enumerate(A) if all(pc.dot(a,x)==b[j] for x in face)]
        xs=[x for x in face if tuple(pc.apply(G,x))==u]
        ys=[x for x in face if tuple(pc.apply(G,x))==v]
        # Prefer lifts with many differing hidden coordinates: they need not be adjacent.
        x=xs[0];y=ys[-1]
        cert=pc.produce(A,b,G,J,x,y,f)
        certs.append(cert)
    return H,certs


def affine_hide(A,b,G,c,rng,steps=12):
    A=deepcopy(A);b=b[:];G=deepcopy(G);c=deepcopy(c);n=len(c['x'])
    for _ in range(steps):
        i,j=rng.sample(range(n),2);s=Q(rng.choice([-2,-1,1,2]),rng.choice([1,2]))
        for row in A+G+[c['coordinate']]: row[i]-=s*row[j]
        c['x'][j]+=s*c['x'][i];c['y'][j]+=s*c['y'][i]
    offset=[Q(rng.randrange(-4,5),3) for _ in range(n)]
    b=[beta+pc.dot(a,offset) for a,beta in zip(A,b)]
    c['x']=[x+t for x,t in zip(c['x'],offset)]
    c['y']=[x+t for x,t in zip(c['y'],offset)]
    pc.audit(A,b,G,c)
    return A,b,G,c


def roof_extension(baseA,baseb,cert,n,unbounded=False):
    A=[a+[Q(0)]*(n-2) for a in baseA];b=baseb[:]
    G=[[Q(i==j) for i in range(n)] for j in range(2)]
    c=deepcopy(cert);c['coordinate'] += [Q(0)]*(n-2)
    for pointno,key in enumerate(('x','y')):
        u,v=c[key]
        for j in range(2,n):
            roof=Q(3+j%3,2)+u/4-v/5
            value=Q((j+1)*(10**5+17)) if unbounded else (Q(0) if pointno==0 else roof)
            c[key].append(value)
    for j in range(2,n):
        row=[Q(0)]*n;row[j]=-1;A.append(row);b.append(Q(0))
        if not unbounded:
            row=[Q(0)]*n;row[j]=1;row[0]=-Q(1,4);row[1]=Q(1,5)
            A.append(row);b.append(Q(3+j%3,2))
    c['lower'] += [Q(0)]*(len(A)-len(baseA));c['upper'] += [Q(0)]*(len(A)-len(baseA))
    pc.audit(A,b,G,c)
    return A,b,G,c


def cube_fibre_edge(p,step):
    n=2*p
    A=[[Q(sign*(i==j)) for i in range(n)] for j in range(p) for sign in (1,-1)]
    b=[Q(1)]*(2*p)
    for j in range(p,n):
        A.append([-Q(i==j) for i in range(n)]);b.append(Q(0))
    G=[[Q(i==j) for i in range(n)] for j in range(p)]
    image_x=[Q(1 if j<step else -1) for j in range(p)]
    image_y=[Q(1 if j<=step else -1) for j in range(p)]
    x=image_x+[Q((step+1)*(j+1)*10**6) for j in range(p)]
    y=image_y+[Q((step+2)*(j+1)*10**6) for j in range(p)]
    J=[2*j+(0 if image_x[j]>0 else 1) for j in range(p) if j!=step]
    f=[Q(0) if j==step else image_x[j] for j in range(p)]
    phi=[Q(i==step)/2 for i in range(n)]
    W=[[Q((1 if row%2==0 else -1)*(j==row//2)) for j in range(p)] for row in J]
    lower=[Q(0)]*len(A);upper=lower[:]
    lower[2*step+1]=Q(1,2);upper[2*step]=Q(1,2)
    c=dict(x=x,y=y,rows=J,weights=[Q(1)]*len(J),normal=f,coordinate=phi,
           residual=W,lower=lower,upper=upper,lower_eq=[Q(0)]*len(J),upper_eq=[Q(0)]*len(J))
    pc.audit(A,b,G,c)
    return A,b,G,c


def main():
    start=time.monotonic();rng=random.Random(245241)
    cases=[]
    for n in (2,3,4):
        cubeA=[[Q(s*(i==j)) for i in range(n)] for j in range(n) for s in (1,-1)]
        cubeb=[Q(1)]*len(cubeA)
        for run in range(6):
            A=deepcopy(cubeA);b=cubeb[:]
            if run>=2:
                for _ in range(2):
                    row=[Q(rng.randrange(-2,3)) for _ in range(n)]
                    if any(row):A.append(row);b.append(Q(3,2))
            G=[[Q(i==j) for i in range(n)] for j in range(2)] if run<2 else [[Q(rng.randrange(-3,4)) for _ in range(n)] for j in range(2)]
            if rank(G,n)!=2:continue
            V=vertices(A,b);H,cs=image_edges(A,b,G,V)
            cases.append((A,b,G,V,H,cs))
    # Non-simple octahedron, including redundant original inequalities.
    A=[[Q(x) for x in row] for row in product((-1,1),repeat=3)];b=[Q(1)]*8
    A += [A[0][:],[Q(0)]*3];b += [Q(1),Q(2)]
    G=[[Q(1),0,0],[0,Q(1),0]];V=vertices(A,b);H,cs=image_edges(A,b,G,V)
    cases.append((A,b,G,V,H,cs))
    counts=dict(models=len(cases),original_vertices=0,image_vertices=0,edge_certificates=0,
                higher_dimensional_preimage_edges=0,nonadjacent_source_lift_pairs=0,
                all_original_vertex_support_tests=0,column_identities=0,rank_gap_checks=0)
    fixtures=[]
    for A,b,G,V,H,cs in cases:
        n=len(G[0]);counts['original_vertices']+=len(V);counts['image_vertices']+=len(H)
        for c in cs:
            out=pc.audit(A,b,G,c);counts['edge_certificates']+=1;counts['column_identities']+=out['column_identity_checks']
            r=rank([A[j] for j in c['rows']],n);gap=rank([A[j] for j in c['rows']]+G,n)-r
            pc.require(gap==1,'wrong independent quotient rank')
            counts['rank_gap_checks']+=1;counts['higher_dimensional_preimage_edges']+=n-r>1
            common=[A[i] for i in range(len(A)) if pc.dot(A[i],c['x'])==b[i] and pc.dot(A[i],c['y'])==b[i]]
            counts['nonadjacent_source_lift_pairs']+=rank(common,n)!=n-1
            f=c['normal'];beta=out['support_value'];u=out['image_start'];v=out['image_end']
            for z in V:
                im=pc.apply(G,z);value=pc.dot(f,im);pc.require(value<=beta,'global bound failed')
                if value==beta:
                    pc.require(cross(u,v,im)==0 and 0<=pc.dot(c['coordinate'],z)-pc.dot(c['coordinate'],c['x'])<=1,'face not the whole segment')
                counts['all_original_vertex_support_tests']+=1
        if len(fixtures)<3:fixtures.append({'A':A,'b':b,'G':G,'certificate':cs[0]})
    baseA=[[Q(1),0],[-Q(1),0],[0,Q(1)],[0,-Q(1)],[Q(1),Q(1)],[-Q(1),-Q(1)]]
    baseb=[Q(1)]*6;G=[[Q(1),0],[0,Q(1)]];V=vertices(baseA,baseb);H,cs=image_edges(baseA,baseb,G,V)
    large=[]
    for n in (8,32,64,128):
        for unbounded in (False,True):
            total=0
            for c in cs:
                A,b,G,ce=roof_extension(baseA,baseb,c,n,unbounded)
                A,b,G,ce=affine_hide(A,b,G,ce,rng,steps=min(3*n,96))
                o=pc.audit(A,b,G,ce);total+=o['column_identity_checks']
            large.append({'source_dimension':n,'image_dimension':2,'original_rows':len(A),'image_edges_certified':len(cs),
                          'preimage_face_dimension':n-1,'unbounded_fibres':unbounded,'source_vertices_assumed':False,
                          'original_graph_enumerated':False,'column_identities':total})
            if n==8:fixtures.append({'A':A,'b':b,'G':G,'certificate':ce})
    high_image_routes=[]
    for image_dim in (8,16,32):
        total=0;last=None
        for step in range(image_dim):
            A,b,G,ce=cube_fibre_edge(image_dim,step)
            # The SAME invertible affine coordinate change for all route steps.
            A,b,G,ce=affine_hide(A,b,G,ce,random.Random(1700+image_dim),steps=3*image_dim)
            out=pc.audit(A,b,G,ce)
            if last is not None:pc.require(last==out['image_start'],'route images do not concatenate')
            last=out['image_end'];total+=out['column_identity_checks']
        high_image_routes.append({'source_dimension':2*image_dim,'image_dimension':image_dim,
            'image_facet_count':2*image_dim,'original_rows':len(A),'verified_route_edges':image_dim,
            'preimage_face_dimension':image_dim+1,'unbounded_fibres':True,
            'source_graph_enumerated':False,'image_graph_enumerated':False,'column_identities':total})
    # Auditor still works when every producer helper and symbolic rank routine fails.
    A,b,G,cert=roof_extension(baseA,baseb,cs[0],8,True)
    old=pc.row_coefficients,pc.independent_rows,sp.Matrix
    def fail(*a,**kw):raise AssertionError('auditor invoked an algebraic search')
    pc.row_coefficients=pc.independent_rows=sp.Matrix=fail
    pc.audit(A,b,G,cert)
    pc.row_coefficients,pc.independent_rows,sp.Matrix=old
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('forgery passed: '+name)
    good=cs[0]
    changes=[('zero_exposure_weight',lambda c:c['weights'].__setitem__(0,Q(0))),
      ('false_image_line',lambda c:c['residual'][0].__setitem__(0,c['residual'][0][0]+1)),
      ('wrong_image_normal',lambda c:c['normal'].__setitem__(0,c['normal'][0]+1)),
      ('wrong_coordinate',lambda c:c['coordinate'].__setitem__(0,c['coordinate'][0]+1)),
      ('infeasible_endpoint',lambda c:c['x'].__setitem__(0,Q(20))),
      ('collapsed_image',lambda c:c.update(y=c['x'][:])),
      ('missing_selected_row',lambda c:c['rows'].pop()),
      ('negative_upper_multiplier',lambda c:c['upper'].__setitem__(0,-Q(1))),
      ('inexact_number',lambda c:c['x'].__setitem__(0,float(c['x'][0]))),
      ('unexpected_field',lambda c:c.update(assume_edge=True))]
    for name,mutate in changes:
        c=deepcopy(good);mutate(c)
        reject(name,lambda c=c:pc.audit(baseA,baseb,[[Q(1),0],[0,Q(1)]],c))
    # An apparent diagonal with a zero objective has no rank-one quotient identity.
    reject('square_diagonal_rank_two',lambda:pc.produce([[1,0],[-1,0],[0,1],[0,-1]],[1,0,1,0],[[1,0],[0,1]],[],[0,0],[1,1],[0,0]))
    # A subsegment is not the entire edge; sharp lower/upper certificates cannot hold.
    c=deepcopy(good);c['y']=[(x+y)/2 for x,y in zip(c['x'],c['y'])];c['coordinate']=[2*x for x in c['coordinate']]
    reject('proper_subsegment',lambda:pc.audit(baseA,baseb,[[Q(1),0],[0,Q(1)]],c))
    for fixture in fixtures: pc.audit(fixture['A'],fixture['b'],fixture['G'],fixture['certificate'])
    path=ROOT/'fixtures/projected_face_examples.json'
    path.write_text(json.dumps(pc.jsonable(fixtures),indent=2)+'\n')
    report={'status':'PASS','scope':'exact rational arithmetic; separate from Lean compilation',**counts,
            'large_cases':large,'high_dimensional_image_routes':high_image_routes,'search_free_audit':'PASS','rejected':rejected,'rejected_count':len(rejected),
            'seconds':round(time.monotonic()-start,3),
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/'research/PROJECTED_FACE_EDGE_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
