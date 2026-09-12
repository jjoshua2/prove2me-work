#!/usr/bin/env python3
"""Exact finite checks of the feedback-box paper proof; not a Lean verdict."""
from __future__ import annotations
import hashlib
import json
from itertools import combinations,product
from pathlib import Path
from projective_factor_discovery import Q,dot,identity,inverse,rank,require


def feedback_vertices(M,b,w):
    d=len(w)
    require(d>0 and len(M)==d and len(b)==d and all(len(row)==d for row in M),'Dimensions')
    require(all(x>=0 for row in M for x in row),'Nonnegative feedback required')
    require(all(x>0 for x in b+w),'Strictly positive b,w required')
    require(all(dot(row,w)<wi for row,wi in zip(M,w)),'Strict contraction witness required')
    found={}
    for bits in product((0,1),repeat=d):
        A=[[Q(i==j)-M[i][j] if bits[i] else Q(i==j) for j in range(d)] for i in range(d)]
        rhs=[b[i] if bits[i] else Q(0) for i in range(d)]
        v=tuple(dot(row,rhs) for row in inverse(A))
        assert all(x>=0 and x<=bi+dot(row,v) for x,bi,row in zip(v,b,M))
        found[bits]=v
    assert len(set(found.values()))==2**d
    return found


def run():
    cases=vertices_count=edges=pairs=negative=0
    examples=[]
    for d in range(2,6):
        w=[Q(i+1) for i in range(d)];b=[Q(i+2,3) for i in range(d)]
        for family in ['cycle','dense','weighted_dense']:
            M=[[Q(1,4) if j==(i-1)%d else Q(0) for j in range(d)] for i in range(d)] if family=='cycle' else [[Q(1,4*d) for j in range(d)] for i in range(d)]
            weights=[Q(1)]*d
            if family=='weighted_dense':
                M=[[M[i][j]*w[i]/w[j] for j in range(d)] for i in range(d)];weights=w
            predicted=feedback_vertices(M,b,weights)
            A=[[-Q(i==j) for j in range(d)] for i in range(d)]+[[Q(i==j)-M[i][j] for j in range(d)] for i in range(d)]
            rhs=[Q(0)]*d+b
            enumerated={}
            for ids in combinations(range(2*d),d):
                rows=[A[i] for i in ids]
                if rank(rows)!=d:continue
                v=tuple(dot(row,[rhs[i] for i in ids]) for row in inverse(rows))
                if all(dot(row,v)<=r for row,r in zip(A,rhs)):
                    enumerated[v]={i for i,(row,r) in enumerate(zip(A,rhs)) if dot(row,v)==r}
            assert set(predicted.values())==set(enumerated)
            for left,right in combinations(predicted,2):
                u,v=predicted[left],predicted[right]
                common=enumerated[u]&enumerated[v]
                adjacent=rank([A[i] for i in common])==d-1
                assert adjacent==(sum(x!=y for x,y in zip(left,right))==1)
                edges+=int(adjacent)
            for left in predicted:
                for right in predicted:
                    current=list(left);length=0
                    for i in range(d):
                        if current[i]!=right[i]:
                            prior=tuple(current);current[i]=right[i];length+=1
                            u,v=predicted[prior],predicted[tuple(current)]
                            assert rank([A[k] for k in enumerated[u]&enumerated[v]])==d-1
                    assert tuple(current)==right and length<=d;pairs+=1
            cases+=1;vertices_count+=len(enumerated)
            examples.append({'family':family,'dimension':d,'vertices':len(enumerated),'diameter':d})
    for M,b,w in [([[Q(1)]],[Q(1)],[Q(1)]),([[-Q(1,4)]],[Q(1)],[Q(1)]),([[Q(0)]],[Q(0)],[Q(1)]),([[Q(0)]],[Q(1)],[Q(0)])]:
        try:feedback_vertices(M,b,w)
        except ValueError:negative+=1
        else:raise AssertionError('Invalid finite hypotheses accepted')
    paths=['scripts/test_contractive_feedback_boxes.py','scripts/projective_factor_discovery.py','research/CONTRACTIVE_FEEDBACK_BOXES_2026-09-12.md']
    return {'status':'PASS','scope':'Exact finite mathematical regression, not Lean or Prove2Me acceptance.',
            'examples':examples,'cases':cases,'vertices':vertices_count,'edges':edges,'ordered_routes':pairs,'negative_controls':negative,
            'sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}}

if __name__=='__main__':print(json.dumps(run(),indent=2)+'\n')
