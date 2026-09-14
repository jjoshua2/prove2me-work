#!/usr/bin/env python3
"""Independent exact alternatives and ray/coverage certificate regression.
The generic theorem's verification status is separate from these computations.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from pathlib import Path
from copy import deepcopy
import random,hashlib,json,time
import sympy as sp

def dot(x,y): return sum((a*b for a,b in zip(x,y)),Q(0))


def feasible(C,r,k):
    """Independent exact elimination, no rank or dual-catalogue calls."""
    require(len(C)==len(r) and all(len(a)==k for a in C),'bad primal shape')
    rows=[(tuple(Q(v) for v in a),Q(b)) for a,b in zip(C,r)]
    for _ in range(k):
        P=[(a,b) for a,b in rows if a[0]>0]
        N=[(a,b) for a,b in rows if a[0]<0]
        out=[(a[1:],b) for a,b in rows if a[0]==0]
        for a,b in P:
            for c,d in N:
                out.append((tuple(a[j]/a[0]-c[j]/c[0] for j in range(1,len(a))),b/a[0]-d/c[0]))
        # Normalize by a POSITIVE factor only. Identical LHS keeps the strictest RHS.
        best={}
        for a,b in out:
            s=next((abs(v) for v in a if v),Q(1))
            a=tuple(v/s for v in a);b/=s
            if not any(a) and b<0:return False
            if a not in best or b<best[a]:best[a]=b
        rows=list(best.items())
    return all(b>=0 for a,b in rows)


def vertices(A,b):
    d=len(A[0]) if A else 0
    if d==0:return [()] if all(x>=0 for x in b) else []
    out=set()
    for ids in combinations(range(len(A)),d):
        M=sp.Matrix([A[i] for i in ids])
        if M.det()==0:continue
        x=tuple(Q(str(v)) for v in M.inv()*sp.Matrix([b[i] for i in ids]))
        if all(dot(row,x)<=rhs for row,rhs in zip(A,b)):out.add(x)
    return sorted(out)


def serialize(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serialize(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serialize(v) for v in x]
    return x

ROOT=Path(__file__).resolve().parents[1]

def require(ok,msg):
    if not ok:raise ValueError(msg)

def cov_system(B,k):
    r=len(B)
    return [[-Q(i==j) for j in range(r)] for i in range(r)]+[[-B[q][j] for q in range(r)] for j in range(k)], [Q(0)]*r+[-Q(1)]*k

def rec_system(B,k):
    return [[-Q(i==j) for j in range(k)] for i in range(k)]+B+[[Q(1)]*k,[-Q(1)]*k], [Q(0)]*(k+len(B))+[Q(1),-Q(1)]

def verify_cover(B,k,rho):
    require(len(rho)==len(B) and all(v>=0 for v in rho),'negative or malformed coverage weights')
    require(all(sum(rho[q]*B[q][j] for q in range(len(B)))>=1 for j in range(k)),'coverage misses a coordinate')

def verify_ray(B,k,v):
    require(len(v)==k and all(x>=0 for x in v),'ray not nonnegative')
    require(sum(v)==1,'ray not normalized')
    require(all(dot(row,v)<=0 for row in B),'ray violates recession inequalities')

def main():
    start=time.monotonic();rng=random.Random(236234)
    cases=[([],0),([],3),([[]],0),([[Q(0)]],1),([[Q(1)]],1),
      ([[Q(1),-Q(2)],[-Q(1),Q(1)]],2),
      ([[Q(2),-Q(1)],[-Q(1),Q(2)]],2),
      ([[Q(1),Q(1),Q(0)],[Q(0),Q(1),Q(1)]],3),
      ([[Q(1,2**160)]],1)]
    for k in range(5):
        for r in range(5):
            for _ in range(5):cases.append(([[Q(rng.randrange(-3,4),rng.randrange(1,4)) for j in range(k)] for q in range(r)],k))
    count={'systems':0,'coverage_cases':0,'recession_cases':0,'feasibility_comparisons':0,
      'constructed_coverage_witnesses':0,'constructed_recession_witnesses':0,
      'verified_unbounded_ray_points':0,'bounded_polyhedron_vertices_checked':0}
    rows=[]
    for B,k in cases:
        r=len(B);C,d=cov_system(B,k);D,b=rec_system(B,k)
        cover=feasible(C,d,r);recession=feasible(D,b,k)
        require(cover!=recession,'alternatives are not exhaustive and exclusive')
        count['systems']+=1;count['coverage_cases']+=cover;count['recession_cases']+=recession;count['feasibility_comparisons']+=2
        x=[Q(rng.randrange(0,4),2) for _ in range(k)]
        t=[dot(row,x)+Q(rng.randrange(0,4),2) for row in B]
        if cover:
            rho=vertices(C,d)[0] if r else ()
            verify_cover(B,k,rho);count['constructed_coverage_witnesses']+=1
            # Independent enumeration of the nonempty resource polyhedron.
            E=[[-Q(i==j) for j in range(k)] for i in range(k)]+B;rhs=[Q(0)]*k+t
            V=vertices(E,rhs)
            if k==0:V=[()]
            require(len(V)>0,'covered nonempty polyhedron has no reference vertices')
            require(dot(rho,t)>=sum(x),'coverage bound failed at explicit feasible point')
            for y in V:
                require(sum(y)<=dot(rho,t),'finite mass bound fails at reference vertex')
                count['bounded_polyhedron_vertices_checked']+=1
            rows.append({'B':B,'k':k,'kind':'coverage','rho':rho})
        else:
            v=vertices(D,b)[0]
            verify_ray(B,k,v);count['constructed_recession_witnesses']+=1
            for R in [-Q(5),Q(0),Q(1),Q(7),Q(100)]:
                s=max(Q(0),R-sum(x)+1);y=[xx+s*vv for xx,vv in zip(x,v)]
                require(all(yy>=0 for yy in y) and all(dot(row,y)<=tt for row,tt in zip(B,t)),'escaped point lost feasibility')
                require(sum(y)>R,'ray point did not exceed prescribed mass')
                count['verified_unbounded_ray_points']+=1
            rows.append({'B':B,'k':k,'kind':'recession','ray':v})
    # Naive per-coordinate upper bounds cannot detect coupled recession.
    B=[[Q(1),-Q(2)],[-Q(1),Q(1)]]
    require(all(any(row[j]>0 for row in B) for j in range(2)),'naive control absent')
    verify_ray(B,2,[Q(1,2),Q(1,2)])
    require(not feasible(*cov_system(B,2),2),'coupled ray had a cover')
    # Nonemptiness is essential: theta>=0, 0*theta<=-1 is empty yet has no cover.
    require(not feasible([[-Q(1)],[Q(0)]],[Q(0),-Q(1)],1),'empty-resource negative control failed')
    require(not feasible(*cov_system([[Q(0)]],1),1),'zero row covers positive mass')
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,IndexError,TypeError):rejected.append(name)
        else:raise AssertionError('invalid witness passed '+name)
    reject('negative_coverage',lambda:verify_cover([[-Q(1)]],1,[-Q(1)]))
    reject('insufficient_coverage',lambda:verify_cover([[Q(1,2)]],1,[Q(1)]))
    reject('missing_coordinate',lambda:verify_cover([[Q(1),Q(0)]],2,[Q(1)]))
    reject('zero_recession_vector',lambda:verify_ray([[Q(0)]],1,[Q(0)]))
    reject('wrong_ray_mass',lambda:verify_ray([[Q(0)]],1,[Q(2)]))
    reject('signed_fake_nonnegative_ray',lambda:verify_ray([[Q(0),Q(0)]],2,[Q(-1),Q(2)]))
    reject('wrong_recession_direction',lambda:verify_ray([[Q(1)]],1,[Q(1)]))
    # Large coverage certificate only: neither feasibility nor vertex enumeration.
    k=64;r=32;B=[[Q(j//2==q) for j in range(k)] for q in range(r)]
    verify_cover(B,k,[Q(1)]*r)
    report={'status':'PASS','scope':'rational tests, not Lean compilation',**count,
      'naive_columnwise_control':'fails, coupled ray verified','empty_feasible_set_control':'PASS',
      'large_certificate_only':{'allocation_coordinates':k,'budget_rows':r,'full_catalogue_or_graph_enumerated':False},
      'negative_controls':rejected,'negative_control_count':len(rejected),'seconds':round(time.monotonic()-start,3)}
    paths=[Path(__file__),
      ROOT/'research/publication_packets/coverage_recession_alternative/solution.lean']
    report['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (ROOT/'research/COVERAGE_RECESSION_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'fixtures').mkdir(exist_ok=True)
    (ROOT/'fixtures/coverage_recession_examples.json').write_text(json.dumps(serialize(rows),indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
