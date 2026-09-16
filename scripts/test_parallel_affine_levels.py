#!/usr/bin/env python3
"""Exact finite controls for a separate Lean theorem, not Lean verification."""
from fractions import Fraction as Q
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import sympy as sp


def dot(a, b):
    assert len(a) == len(b)
    return sum((x*y for x,y in zip(a,b)), Q(0))


def check(V, p, q, g, lengths, T, offset):
    d=len(g)
    assert any(g) and len(p)==len(q)==len(lengths)
    assert all(x in V for x in p+q)
    assert len(set(lengths))==len(lengths) and all(x>0 for x in lengths)
    assert all(tuple(b-a for a,b in zip(x,y))==tuple(t*z for z in g)
               for x,y,t in zip(p,q,lengths))
    assert len(T)==len(offset) and all(len(row)==d for row in T)
    assert sp.Matrix(T).rank()==d
    detecting=[]
    for j,row in enumerate(T):
        c=dot(row,g)
        if not c: continue
        levels={dot(row,x)+offset[j] for x in V}
        forward={(dot(row,x)+offset[j],dot(row,y)+offset[j]) for x,y in zip(p,q)}
        backward={(b,a) for a,b in forward}
        assert len(forward)==len(p)==len(backward)
        assert not (forward & backward)
        offdiag={(a,b) for a in levels for b in levels if a!=b}
        assert forward | backward <= offdiag
        K=len(levels)
        assert len(offdiag)==K*(K-1) and 2*len(p)<=K*(K-1)
        detecting.append((j,K,2*len(p)==K*(K-1)))
    assert detecting
    return detecting


def km(bits,e=Q(1,4)):
    x=[]
    for b in bits:
        low=e*x[-1] if x else Q(0)
        x.append(1-low if b else low)
    return tuple(x)


def run():
    sharp=scalar=embedding=km_cases=0
    details=[]
    # Distinct powers-of-two differences make the exact bound sharp.
    for d in range(1,5):
        for K in range(0,10):
            V=[(Q(2**i),)+(Q(0),)*(d-1) for i in range(K)]
            pairs=list(combinations(V,2));p=[a for a,b in pairs];q=[b for a,b in pairs]
            lengths=[b[0]-a[0] for a,b in pairs];g=(Q(1),)+(Q(0),)*(d-1)
            for sign in (-1,1):
                T=[tuple(Q(sign if i==j else 0) for j in range(d)) for i in range(d)]
                T += [tuple(Q(j+1,7) for j in range(d)), (Q(0),)*d]
                offset=[Q(j-3,11) for j in range(len(T))]
                result=check(V,p,q,g,lengths,T,offset)
                assert all(s for j,k,s in result)
                sharp+=1;scalar+=len(result);embedding+=1
    for d in range(1,9):
        V=[km(bits) for bits in product((0,1),repeat=d)]
        prefixes=list(product((0,1),repeat=d-1))
        p=[km((*b,0)) for b in prefixes];q=[km((*b,1)) for b in prefixes]
        g=(Q(0),)*(d-1)+(Q(1),);lengths=[b[-1]-a[-1] for a,b in zip(p,q)]
        T=[tuple(Q(i==j)+Q((i+1)*(j+1)) for j in range(d)) for i in range(d)]
        result=check(V,p,q,g,lengths,T,[Q(5,9)]*d)
        scalar+=len(result);embedding+=1;km_cases+=1
        details.append({'dimension':d,'point_count':len(V),'parallel_pairs':len(p),
                        'coordinate_levels':[k for j,k,s in result]})
    # Countermodels for dropping individual assumptions, not failed Lean runs.
    failures=[('positive_lengths',2,2), ('distinct_lengths',2,2),
              ('nonzero_direction',1,1), ('injective_linear_part',1,1),
              ('endpoint_membership',1,1)]
    for name,N,K in failures: assert not 2*N<=K*(K-1)
    return {'status':'PASS','sharp_embedding_cases':sharp,'all_embedding_cases':embedding,
            'detecting_coordinate_checks':scalar,'Klee_Minty_cases':km_cases,'Klee_Minty_details':details,
            'countermodels':[
                {'omitted':'positivity','p':[0,1],'q':[1,0],'lambda':[1,-1],'g':1,'T':1,'V':[0,1]},
                {'omitted':'distinctness','p':[0,0],'q':[1,1],'lambda':[1,1],'g':1,'T':1,'V':[0,1]},
                {'omitted':'nonzero_g','p':[0],'q':[0],'lambda':[1],'g':0,'T':1,'V':[0]},
                {'omitted':'injectivity','p':[0],'q':[1],'lambda':[1],'g':1,'T':0,'V':[0,1]},
                {'omitted':'membership','p':[0],'q':[1],'lambda':[1],'g':1,'T':1,'V':[0]}],
            'scope':'Exact finite tests and assumption countermodels; separate from Lean compilation and authenticated Prove2Me verdict.'}

if __name__=='__main__':
    result=run()
    result['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(result,indent=2,sort_keys=True))
