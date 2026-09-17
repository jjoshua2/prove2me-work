#!/usr/bin/env python3
"""Exact supporting regression, not Lean verification or a formalized parser.
All final vertices are independently recovered from original H inequalities.
Every tested positive support is checked for barycentric equality first.
"""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib,json
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]

def require(ok,message):
    if not ok: raise ValueError(message)

def dot(a,b): return sum((x*y for x,y in zip(a,b)),Q(0))
def vertex_table(A,b,d):
    V=set(); systems=0
    for I in combinations(range(len(A)),d):
        M=sp.Matrix([A[i] for i in I]);systems+=1
        if M.det()==0: continue
        x=tuple(Q(z) for z in M.inv()*sp.Matrix([b[i] for i in I]))
        if all(dot(a,x)<=z for a,z in zip(A,b)): V.add(x)
    return sorted(V),systems

def audit_support(points,weights,C,b,x):
    n=len(points);d=len(x)
    require(n==len(weights) and all(w>0 for w in weights),'positive support required')
    require(sum(weights)==1 and all(sum(w*v[j] for w,v in zip(weights,points))==x[j] for j in range(d)), 'wrong barycentre')
    require(all(dot(a,x)<=z for a,z in zip(C,b)), 'cut infeasibility')
    V=sp.Matrix([[1]*n]+[[v[j] for v in points] for j in range(d)])
    active=[j for j,(a,z) in enumerate(zip(C,b)) if dot(a,x)==z]
    M=sp.Matrix([[1]*n]+[[dot(C[j],v) for v in points] for j in active])
    # The vertex condition is checked independently in the outer H enumeration.
    require(M.rank()==V.rank(),'cut evaluations lost a positive-support affine direction')
    tested=0
    for t in M.nullspace():
        require(V*t==sp.zeros(d+1,1),'active-kernel motion is geometrically nonzero');tested+=1
    independent=V.rank()==n
    if independent: require(n<=len(active)+1,'cardinality bound failed')
    return len(active),independent,tested

def main():
    counts={'models':0,'original_square_systems':0,'cut_vertices':0,'positive_independent_supports':0,
            'dependent_supports':0,'active_kernel_basis_vectors':0,'cut_row_checks':0,'sharp_examples':0}
    examples=[]
    tests=[(2,[],[]),(2,[[1,1]],[Q(3,2)]),(2,[[1,2],[-1,1]],[Q(7,5),Q(1,4)]),
           (3,[[1,1,1]],[Q(7,5)]),(3,[[1,1,0],[0,1,1]],[1,1]),
           (3,[[1,2,3],[-1,-2,-3]],[Q(13,4),-Q(13,4)])]
    for d,C,b in tests:
        C=[tuple(map(Q,a)) for a in C];b=list(map(Q,b))
        eye=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
        H=[tuple(-v for v in a) for a in eye]+eye+C;rhs=[Q(0)]*d+[Q(1)]*d+b
        V,systems=vertex_table(H,rhs,d);base=list(product([Q(0),Q(1)],repeat=d))
        counts['models']+=1;counts['original_square_systems']+=systems;counts['cut_vertices']+=len(V)
        for x in V:
            for r in range(1,d+2):
                for ids in combinations(range(len(base)),r):
                    points=[base[i] for i in ids];M=sp.Matrix([[1]*r]+[[v[j] for v in points] for j in range(d)])
                    if M.rank()!=r: continue
                    try:w,params=M.gauss_jordan_solve(sp.Matrix([1]+list(x)))
                    except ValueError:continue
                    if params.rows or not all(z>0 for z in w):continue
                    weights=list(map(Q,w));a,ind,k= audit_support(points,weights,C,b,x)
                    counts['positive_independent_supports']+=1;counts['active_kernel_basis_vectors']+=k
                    counts['cut_row_checks']+=len(C)
                    # Duplicate one point and divide its weight to force dependent support.
                    points2=points+[points[0]];weights2=weights[:];weights2[0]/=2;weights2.append(weights2[0])
                    a,ind,k=audit_support(points2,weights2,C,b,x)
                    require(not ind,'duplicate support was independent')
                    counts['dependent_supports']+=1;counts['active_kernel_basis_vectors']+=k
    for d in [1,2,3,4,8,16]:
        points=[tuple(Q(i==j) for j in range(d)) for i in range(d)]+[(Q(0),)*d]
        weights=[Q(1,d+1)]*(d+1);x=(Q(1,d+1),)*d
        C=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
        b=list(x)
        a,ind,k=audit_support(points,weights,C,b,x)
        require(ind and len(points)==a+1,'sharp count not attained')
        counts['sharp_examples']+=1
        # At this positive interior simplex point, the d independent active upper cuts
        # uniquely expose x by their positive sum, so these examples are true cut vertices.
        examples.append({'dimension':d,'support_size':d+1,'active_cuts':a})
    negative=[]
    def reject(name,fn):
        try:fn()
        except ValueError:negative.append(name)
        else: raise AssertionError('unrejected invalid case '+name)
    # Removing extremality permits a zero-cut, nonzero affine direction.
    reject('without_extremality',lambda:audit_support([(Q(0),),(Q(1),)],[Q(1,2),Q(1,2)],[],[],(Q(1,2),)))
    reject('zero_weight_cannot_control_unused_point',lambda:audit_support([(Q(0),),(Q(1),)],[Q(1),Q(0)],[],[],(Q(0),)))
    reject('negative_weight',lambda:audit_support([(Q(0),),(Q(1),)],[Q(2),Q(-1)],[],[],(Q(-1),)))
    reject('wrong_sum',lambda:audit_support([(Q(0),),(Q(1),)],[Q(1),Q(1)],[],[],(Q(1),)))
    reject('infeasible_cut',lambda:audit_support([(Q(0),)],[Q(1)],[(Q(1),)],[Q(-1)],(Q(0),)))
    # Arbitrarily small inactive margins are preserved by an explicit finite epsilon.
    margins=[]
    for power in [8,40,120,240]:
        delta=Q(1,2**power);w=[Q(1,3),Q(2,3)];t=[Q(1),Q(-1)]
        slope=[Q(3),Q(-7),Q(0)];slack=[delta,2*delta,delta/3]
        e=min([w[i]/(abs(t[i])+1) for i in range(2)]+[a/(abs(z)+1) for a,z in zip(slack,slope)])/2
        require(e>0 and all(wi+sign*e*ti>0 for wi,ti in zip(w,t) for sign in [-1,1]),'weight perturbation failed')
        require(all(abs(e*z)<a for a,z in zip(slack,slope)),'inactive cut perturbation failed')
        margins.append(power)
    path=ROOT/'research/publication_packets/cut_active_support_injectivity/solution.lean'
    report={'status':'PASS','scope':'Exact supporting algebra/H-vertex tests, NOT Lean or Prove2Me verification',
        'counts':counts,'sharp_examples':examples,'rejected':negative,'tiny_inactive_margin_powers':margins,
        'solution_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    dest=ROOT/'research/CUT_ACTIVE_SUPPORT_TEST.json';dest.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
