#!/usr/bin/env python3
"""Exact checks of the signed-root angle lemma, independently by Gram projection.

The written lemma plus Dadush--Haehnle's existing diameter theorem covers ALL
right sides. This is an exact test, not a new shadow-route implementation.
"""
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import argparse,json,random,hashlib
import sympy as sp


def roots(d):
    out=[tuple(int(i==j) for j in range(d)) for i in range(d)]
    for i,j in combinations(range(d),2):
        for sign in (-1,1):out.append(tuple(int(k==i)+sign*int(k==j) for k in range(d)))
    return out


def orthogonal_blocks(rows,d):
    graph=[[] for _ in range(d)];pins=set()
    for a in rows:
        nz=[i for i,x in enumerate(a) if x]
        if len(nz)==1:pins.add(nz[0])
        else:
            i,j=nz;sign=-a[i]*a[j]
            graph[i].append((j,sign));graph[j].append((i,sign))
    seen=set();blocks=[]
    for i in range(d):
        if i in seen:continue
        labels={i:1};todo=[i];bad=False
        while todo:
            x=todo.pop();seen.add(x)
            if x in pins:bad=True
            for y,sg in graph[x]:
                if y in labels:
                    if labels[y]!=sg*labels[x]:bad=True
                else:labels[y]=sg*labels[x];todo.append(y)
        if not bad:blocks.append(labels)
    return blocks


def run():
    rng=random.Random(20260916);records=[];checks=independent=zero=0
    for d in (1,2,3,4,5,8):
        R=roots(d);sets=[]
        if d<=3:
            sets=[list(I) for k in range(d+1) for I in combinations(range(len(R)),k)]
        else:
            sets=[rng.sample(range(len(R)),rng.randrange(d+1)) for _ in range(100)]
        local=0;smallest=None
        for ids in sets:
            rows=[R[i] for i in ids];B=orthogonal_blocks(rows,d)
            M=sp.Matrix(rows) if rows else sp.zeros(0,d)
            basis=M.rowspace()
            U=sp.Matrix.vstack(*basis) if basis else sp.zeros(0,d)
            gram=(U*U.T).inv() if basis else None
            for a in R:
                dist=sum((Q(sum(a[i]*s for i,s in C.items())**2,len(C)) for C in B),Q(0))
                v=sp.Matrix(a);projection=U.T*gram*U*v if basis else sp.zeros(d,1)
                exact=Q(str(((v-projection).T*(v-projection))[0]))
                assert dist==exact
                checks+=1;local+=1
                if dist:
                    rel=dist/sum(x*x for x in a)
                    assert rel>=Q(1,2*d)
                    smallest=rel if smallest is None else min(smallest,rel);independent+=1
                else:zero+=1
        records.append({'dimension':d,'row_subsets_tested':len(sets),'projection_checks':local,
                        'smallest_positive_squared_relative_distance':str(smallest),
                        'proved_lower_bound':str(Q(1,2*d))})
    # Unequal pair coefficients destroy a uniform angle lower bound.
    thin=[]
    for p in (10,40,160):
        eps=Q(1,2**p);squared=eps*eps/(1+eps*eps)
        assert squared<Q(1,4)
        thin.append({'epsilon_power':p,'squared_relative_distance':str(squared),
                     'rows':[['1','0'],['1',str(eps)]]})
    return {'status':'PASS','seed':20260916,'total_projection_checks':checks,
            'positive_distance_checks':independent,'zero_distances':zero,'records':records,
            'unequal_coefficients_angle_control':thin,
            'scope':'Written global signed-root angle bound plus exact Gram checks. The cited shadow diameter theorem is classical; its algorithm is not executed here.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    r=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['total_projection_checks'])
if __name__=='__main__':main()
