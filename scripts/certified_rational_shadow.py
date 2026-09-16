#!/usr/bin/env python3
"""Original-H, exact rational shadow routes with deterministic finite-bit genericity.

No vertex graph, edge-direction list, flag refinement or Minkowski decomposition
is an input. Common original facet equalities are retained. Nonsimple vertices
and lower-dimensional bounded presentations are allowed. The support oracle is
unchanged exact_farkas_lp; its free-variable lifting may return a nonvertex at a
tie, so a separate exposed-face support solve resolves such an INTERNAL query.

This is classical shadow/dichotomic routing with a concrete original-row
perturbation and certificate interface. The number of shadow edges need NOT be
polynomial. Black (2024, Thm 1.2) rules out a universal short SINGLE shadow.
The verifier runs no LP, inverse discovery, rank search or vertex enumeration.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import gcd, lcm, factorial
from pathlib import Path
import argparse, hashlib, json
import exact_farkas_lp as lp

require, rat, serial, dot = lp.require, lp.rat, lp.serial, lp.dot


def parse(data):
    A,b=lp.parse(data['A'],data['b']);d=len(A[0])
    u,v=tuple(map(rat,data['start'])),tuple(map(rat,data['target']))
    require(len(u)==len(v)==d,'endpoint dimension')
    return A,b,u,v


def digest(A,b,u,v):
    return hashlib.sha256(json.dumps(serial([A,b,u,v]),separators=(',',':')).encode()).hexdigest()


def integer_rows(A,b):
    """Positive row scalings, including rhs; no sign changes or facet deletion."""
    AA=[];bb=[]
    for row,t in zip(A,b):
        scale=lcm(*(v.denominator for v in row+(t,)))
        vals=[int(v*scale) for v in row+(t,)];g=0
        for v in vals:g=gcd(g,abs(v))
        if g: vals=[v//g for v in vals]
        AA.append(tuple(vals[:-1]));bb.append(vals[-1])
    return tuple(AA),tuple(bb)


def primitive(c):
    scale=lcm(*(x.denominator for x in map(Q,c)))
    values=tuple(int(x*scale) for x in c);g=0
    for x in values:g=gcd(g,abs(x))
    return tuple(Q(x//g) for x in values) if g else tuple(Q(0) for _ in c)


def independent_rows(A,ids,need):
    """Producer-only rational elimination. Its output receives inverse witnesses."""
    if need==0:return [],[]
    rows=[];chosen=[];pivots=[]
    for i in ids:
        row=list(map(Q,A[i]))
        for p,basis in zip(pivots,rows):
            q=row[p]
            if q: row=[x-q*y for x,y in zip(row,basis)]
        p=next((j for j,x in enumerate(row) if x),None)
        if p is not None:
            t=row[p];row=[x/t for x in row]
            # Pivots need not be ascending: later rows vanish at all earlier ones.
            chosen.append(i);rows.append(row);pivots.append(p)
            if len(chosen)==need:return chosen,pivots
    require(need==0 or len(chosen)==need,'original tight rows do not have required rank')
    return chosen,pivots


def inverse(M):
    n=len(M);a=[list(map(Q,row))+[Q(i==j) for j in range(n)] for i,row in enumerate(M)]
    require(all(len(row)==2*n for row in a),'nonsquare basis')
    for j in range(n):
        k=next((i for i in range(j,n) if a[i][j]),None);require(k is not None,'singular basis')
        a[j],a[k]=a[k],a[j];q=a[j][j];a[j]=[x/q for x in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                q=a[i][j];a[i]=[x-q*y for x,y in zip(a[i],a[j])]
    return tuple(tuple(row[n:]) for row in a)


def rank_packet(A,ids,need):
    d=len(A[0]);ids,columns=independent_rows(A,ids,need)
    B=[[A[i][j] for j in columns] for i in ids]
    inv=inverse(B);R=[[Q(0)]*need for _ in range(d)]
    for j,column in enumerate(columns):R[column]=list(inv[j])
    return {'rows':ids,'right_inverse':R}


def audit_rank(A,c,need):
    d=len(A[0]);I=c['rows'];raw=c['right_inverse']
    require(type(I)is list and len(I)==need and len(set(I))==need and
            all(type(i)is int and 0<=i<len(A) for i in I),'bad rank row labels')
    require(type(raw)is list and len(raw)==d and all(len(row)==need for row in raw),'right inverse shape')
    R=[list(map(rat,row)) for row in raw]
    require(all(sum((A[i][k]*R[k][j] for k in range(d)),Q(0))==int(s==j)
                for s,i in enumerate(I) for j in range(need)),'false right inverse identity')
    return I


def active(A,b,x):return [i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t]


def vertex_packet(A,b,x):
    require(len(x)==len(A[0]) and all(dot(a,x)<=t for a,t in zip(A,b)),'infeasible vertex')
    return {'point':list(x),**rank_packet(A,active(A,b,x),len(x))}


def audit_vertex(A,b,c):
    x=tuple(map(rat,c['point']));d=len(A[0]);require(len(x)==d,'vertex coordinate shape')
    I=audit_rank(A,c,d)
    require(all(dot(a,x)<=t for a,t in zip(A,b)) and all(dot(A[i],x)==b[i] for i in I),
            'invalid original vertex or tight basis')
    return x


def edge_packet(A,b,x,y):
    require(x!=y,'stationary pair is not an edge')
    shared=sorted(set(active(A,b,x))&set(active(A,b,y)))
    c=rank_packet(A,shared,len(x)-1);v=tuple(t-s for s,t in zip(x,y))
    c['start_blocker']=next(i for i in active(A,b,x) if dot(A[i],v)<0)
    c['end_blocker']=next(i for i in active(A,b,y) if dot(A[i],v)>0)
    return c


def audit_edge(A,b,x,y,c):
    require(x!=y,'zero-length purported edge');I=audit_rank(A,c,len(x)-1)
    require(all(dot(A[i],x)==b[i]==dot(A[i],y) for i in I),'edge rows not common/tight')
    v=tuple(t-s for s,t in zip(x,y))
    for key,p,sign in [('start_blocker',x,-1),('end_blocker',y,1)]:
        i=c[key];require(type(i)is int and 0<=i<len(A),'invalid endpoint blocker')
        require(dot(A[i],p)==b[i] and sign*dot(A[i],v)>0,'not a maximal original segment')
    first=next(z for z in v if z)
    return tuple(z/first for z in v)


def generic_objectives(A,b,pu,pv):
    """Polynomial bit-size genericity for ALL original edge lines, not a sample.
    For integer normals bounded by H, a cofactor edge vector has coordinates
    <=G=(d-1)!H^(d-1). Inner products are <=dHG; determinant coefficients are
    <=C=2(dHG)^2. Base R=2C+2 prevents cancellation in all relevant polynomials.
    Independent endpoint bases make those determinant polynomials nonzero.
    """
    d=len(A[0]);IA,ib=integer_rows(A,b);H=max(1,max(abs(z) for row in IA for z in row))
    G=factorial(d-1)*H**(d-1);C=2*(d*H*G)**2;R=2*C+2
    U,V=pu['rows'],pv['rows']
    f=tuple(sum(IA[i][j]*R**(d-1-k) for k,i in enumerate(U)) for j in range(d))
    h=tuple(sum(IA[i][j]*R**(d*(d-1-k)) for k,i in enumerate(V)) for j in range(d))
    return tuple(map(Q,f)),tuple(map(Q,h)),{
        'integer_normal_bound':H,'cofactor_bound':G,'determinant_coefficient_bound':C,'base':R,
        'max_determinant_degree':d*d-1,'endpoint_objective_max_bits':max(abs(z).bit_length() for z in f+h)}


def working_face(A,b,u,v):
    locked=sorted(set(active(A,b,u))&set(active(A,b,v)))
    AA=A+tuple(tuple(-z for z in A[i]) for i in locked)
    bb=b+tuple(-b[i] for i in locked)
    return AA,bb,locked


def bounds(A,b,solver):
    out=[];d=len(A[0])
    for j in range(d):
        for sign in (-1,1):
            c=tuple(Q(sign*int(i==j)) for i in range(d));o=solver.maximize(c)
            out.append({'coordinate':j,'sign':sign,'optimum':o})
    return out


def audit_bounds(A,b,records):
    seen=set();d=len(A[0]);require(type(records)is list,'bad boundedness list')
    for r in records:
        j,s=r['coordinate'],r['sign']
        require(type(j)is int and 0<=j<d and type(s)is int and s in(-1,1)and(j,s)not in seen,'bad coordinate bound')
        seen.add((j,s));lp.verify_optimum(A,b,tuple(Q(s*int(i==j)) for i in range(d)),r['optimum'])
    require(len(seen)==2*d,'incomplete boundedness certificate')


def tie_vertex(A,b,objective,primary,secondary,pivot_cap):
    """The split-variable simplex point may be interior to an exposed EDGE.
    Optimize secondary on its EXACT supporting equality to obtain a vertex.
    This is an additional counted LP, not silently a free lexicographic oracle.
    """
    point,value=lp.verify_optimum(A,b,objective,primary)
    AA=A+(objective,tuple(-z for z in objective));bb=b+(value,-value)
    solver=lp.ExactLP(AA,bb,point,pivot_cap);out=solver.maximize(secondary)
    y,_=lp.verify_optimum(AA,bb,secondary,out)
    return y,out,solver.pivots


def construct(data,query_cap=10000,pivot_cap=20000,basis_rotations=(0,0)):
    A,b,u,v=parse(data);d=len(u)
    require(type(query_cap)is int and query_cap>0,'invalid support-query cap')
    pu,pv=vertex_packet(A,b,u),vertex_packet(A,b,v)
    require(len(basis_rotations)==2 and all(type(r)is int and 0<=r<d for r in basis_rotations),
            'invalid endpoint basis rotation')
    rotated=[]
    for packet,r in zip((pu,pv),basis_rotations):
        ids=packet['rows'];ids=ids[r:]+ids[:r]
        rotated.append({'point':packet['point'],**rank_packet(A,ids,d)})
    pu,pv=rotated
    source=lp.ExactLP(A,b,u,pivot_cap);bd=bounds(A,b,source)
    WA,Wb,locked=working_face(A,b,u,v)
    f,h,gen=generic_objectives(A,b,pu,pv);slope=tuple(y-x for x,y in zip(f,h))
    solver=lp.ExactLP(WA,Wb,u,pivot_cap);nodes=[];pending=[(u,v)];tie_count=tie_pivots=0
    vertices={u:pu,v:pv}
    while pending:
        x,y=pending.pop()
        if x==y:continue
        require(len(nodes)<query_cap,'support-query cap; no complete shadow claimed')
        den=dot(slope,tuple(q-p for p,q in zip(x,y)))
        require(den>0,'endpoint support slopes are not ordered')
        t=dot(f,tuple(p-q for p,q in zip(x,y)))/den
        require(0<t<1,'query outside endpoint objective segment')
        c=primitive(tuple((1-t)*p+t*q for p,q in zip(f,h)))
        result=solver.maximize(c);z,value=lp.verify_optimum(WA,Wb,c,result)
        common=dot(c,x);require(common==dot(c,y)<=value,'false chord intersection')
        record={'left':list(x),'right':list(y),'time':t,'primary':result}
        if value==common:
            record.update(kind='edge',edge=edge_packet(A,b,x,y))
        else:
            try:pz=vertex_packet(A,b,z)
            except ValueError:
                z,second,pivots=tie_vertex(WA,Wb,c,result,primitive(h),pivot_cap)
                record['secondary']=second;tie_count+=1;tie_pivots+=pivots
                pz=vertex_packet(A,b,z)
            require(dot(slope,x)<dot(slope,z)<dot(slope,y),'new support vertex not between slopes')
            require(dot(c,z)==value,'tie resolver changed primary support')
            vertices[z]=pz;record.update(kind='split',middle=list(z))
            pending.extend([(z,y),(x,z)])
        nodes.append(record)
    cert=serial({'format':'certified-rational-shadow-v1','problem_sha256':digest(A,b,u,v),
        'endpoint_bases':[pu,pv],'genericity':gen,'locked_rows':locked,'boundedness':bd,
        'vertices':list(vertices.values()),'queries':nodes})
    report=verify(data,cert)
    require(solver.calls==report['primary_support_queries'] and tie_count==report['tie_resolution_queries'],
            'query accounting changed')
    return {'certificate':cert,'verified':report,'discovery':{
        'boundedness_LP_calls':source.calls,'primary_support_LP_calls':solver.calls,'tie_resolution_LP_calls':tie_count,
        'original_tableau_pivots':source.pivots+solver.pivots,'tie_tableau_pivots':tie_pivots,
        'global_vertex_graph_enumerated':False,'edge_directions_supplied':False,
        'scope':'Output-sensitive support queries; tableau pivots are separate and need not be polynomial.'}}


def verify(data,c):
    A,b,u,v=parse(data);d=len(u)
    require(c['format']=='certified-rational-shadow-v1'and c['problem_sha256']==digest(A,b,u,v),'changed original input')
    pu,pv=c['endpoint_bases'];require(audit_vertex(A,b,pu)==u and audit_vertex(A,b,pv)==v,'wrong endpoint bases')
    audit_bounds(A,b,c['boundedness'])
    f,h,gen=generic_objectives(A,b,pu,pv);require(c['genericity']==gen,'changed finite-bit genericity certificate')
    WA,Wb,locked=working_face(A,b,u,v);require(c['locked_rows']==locked,'wrong common-face equalities')
    slope=tuple(y-x for x,y in zip(f,h));V={}
    for p in c['vertices']:
        x=audit_vertex(A,b,p);require(x not in V,'duplicate path vertex certificate')
        require(all(dot(A[i],x)==b[i] for i in locked),'vertex left the common original face');V[x]=p
    pending=[] if u==v else[(u,v)];leaves=[];split=secondary=0;directions=set()
    for rec in c['queries']:
        require(pending,'extraneous support query');x,y=pending.pop()
        require(tuple(map(rat,rec['left']))==x and tuple(map(rat,rec['right']))==y,'wrong query tree order')
        den=dot(slope,tuple(q-p for p,q in zip(x,y)));require(den>0,'unordered slopes')
        t=dot(f,tuple(p-q for p,q in zip(x,y)))/den
        require(0<t<1 and rat(rec['time'])==t,'incorrect crossing time')
        obj=primitive(tuple((1-t)*p+t*q for p,q in zip(f,h)))
        point,value=lp.verify_optimum(WA,Wb,obj,rec['primary']);common=dot(obj,x)
        require(common==dot(obj,y)<=value,'invalid support query bound')
        if rec['kind']=='edge':
            require(value==common and 'secondary'not in rec,'unsupported leaf')
            require(x in V and y in V,'missing original vertex certificate')
            g=audit_edge(A,b,x,y,rec['edge']);require(g not in directions,'edge direction repeated along straight shadow')
            directions.add(g);leaves.append((x,y,t))
        else:
            require(rec['kind']=='split' and value>common,'unjustified split')
            z=tuple(map(rat,rec['middle']));require(z in V and dot(obj,z)==value,'incorrect inserted support vertex')
            require(dot(slope,x)<dot(slope,z)<dot(slope,y),'split not between slopes')
            if 'secondary'in rec:
                AA=WA+(obj,tuple(-q for q in obj));bb=Wb+(value,-value)
                zz,_=lp.verify_optimum(AA,bb,primitive(h),rec['secondary'])
                require(zz==z,'secondary output changed');secondary+=1
            else: require(point==z,'uncertified replacement of primary support point')
            split+=1;pending.extend([(z,y),(x,z)])
    require(not pending,'incomplete shadow traversal')
    path=[u];times=[]
    for x,y,t in leaves:
        require(x==path[-1],'disconnected edge leaves')
        require(not times or times[-1]<t,'shadow walls not strictly ordered')
        require(dot(h,tuple(b-a for a,b in zip(x,y)))>0,'not target-objective monotone')
        path.append(y);times.append(t)
    require(path[-1]==v and set(path)==set(V) and len(path)==len(set(path)),'wrong endpoints or repeated/unbound path points')
    L=len(leaves);require(len(c['queries'])==(2*L-1 if L else 0) and split==max(0,L-1)and secondary<=split,
                         'dichotomic query count failed')
    return {'status':'PASS','ambient_dimension':d,'original_rows':len(A),'original_edges':L,
        'primary_support_queries':len(c['queries']),'tie_resolution_queries':secondary,
        'total_support_query_bound':max(0,3*L-2),'locked_original_rows':locked,
        'path':serial(path),'crossing_times':serial(times),'distinct_used_edge_directions':len(directions),
        'complete_affine_shadow_certified':True,'endpoint_objective_max_bits':gen['endpoint_objective_max_bits'],
        'vertices_with_more_than_d_tight_rows':sum(len(active(A,b,x))>d for x in path),
        'optimization_or_rank_search_in_verifier':False,
        'uniform_polynomial_length_claimed':False,
        'scope':'Exact original-H common-face shadow; finite-bit genericity is written, not Lean-verified.'}


def main():
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(250000)
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--query-cap',type=int,default=10000)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text())
        raw=json.loads(a.certificate.read_text()) if a.certificate else None
        out=verify(data,raw.get('certificate',raw)) if raw is not None else construct(data,a.query_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError,OSError)as e:p.exit(2,f'No complete shadow certificate: {e}\n')
if __name__=='__main__':main()
