#!/usr/bin/env python3
"""Independent exact tests of the even-gap catalogue; not Lean verification.

The order-only algorithms do not call root-polynomial or linear-system code.
The reference uses the unchanged accepted #299 rational test helper.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from collections import Counter
from pathlib import Path
from copy import deepcopy
import argparse
import hashlib
import json
import random
import test_moment_root_catalogue as ref


def validate(a, d, S):
    if type(d) is not int or not 0 <= d < len(a):
        raise ValueError('require 0 <= d < m')
    if any(not isinstance(x, Q) for x in a):
        raise ValueError('exact rational parameters required')
    if not all(x < y for x,y in zip(a,a[1:])):
        raise ValueError('strictly ordered distinct parameters required')
    if len(S) != d or len(set(S)) != d or any(type(i) is not int or not 0 <= i < len(a) for i in S):
        raise ValueError('distinct d original labels required')


def gaps(m, S):
    """Literal public condition, with no geometric or sign test."""
    chosen=set(S)
    outside=[i for i in range(m) if i not in chosen]
    return [(i,j,sum(i < s < j for s in chosen)) for i,j in combinations(outside,2)]


def even_gaps(m, S):
    return all(n % 2 == 0 for _,_,n in gaps(m,S))


def adjacent_complement(m, S):
    """Independent linear scan: between consecutive complement labels all
    intermediate labels lie in S. Pair counts add across consecutive gaps.
    This implementation equivalence is tested, not an extra Lean theorem.
    """
    chosen=set(S)
    outside=[i for i in range(m) if i not in chosen]
    return all((j-i-1)%2 == 0 for i,j in zip(outside,outside[1:]))


def record(a,d,S):
    validate(a,d,S)
    polynomial=ref.polynomial(a[i] for i in S)
    values=[ref.evaluate(polynomial,x) for x in a]
    mean=sum(values,Q(0))/len(a)
    return dict(dimension=d,parameters=list(map(str,a)),selected=list(S),
                parity_accepts=even_gaps(len(a),S),polynomial=list(map(str,polynomial)),
                nodal_values=list(map(str,values)),mean=str(mean))


def verify(saved):
    """Verify the supplied monic polynomial from its roots and degree; no
    product construction, candidate production or square-system solver.
    """
    a=list(map(Q,saved['parameters'])); d=saved['dimension']; S=saved['selected']
    validate(a,d,S)
    p=list(map(Q,saved['polynomial'])); values=list(map(Q,saved['nodal_values'])); mean=Q(saved['mean'])
    if len(p)!=d+1 or p[-1]!=1 or len(values)!=len(a):raise ValueError('degree/shape')
    if any(ref.evaluate(p,a[i])!=0 for i in S):raise ValueError('wrong roots')
    if any(ref.evaluate(p,x)!=v for x,v in zip(a,values)):raise ValueError('wrong nodal evaluations')
    if mean!=sum(values,Q(0))/len(a):raise ValueError('wrong full-label mean')
    accept=even_gaps(len(a),S)
    if type(saved['parity_accepts']) is not bool or saved['parity_accepts']!=accept:raise ValueError('wrong parity result')
    if accept != (mean!=0 and all(v/mean>=0 for v in values)):raise ValueError('parity/sign mismatch')
    for i,j,n in gaps(len(a),S):
        if (values[i]*values[j]>0)!=(n%2==0):raise ValueError('pair sign identity')
    if accept:
        x=tuple(-p[j]/mean for j in range(1,d+1))
        rows=ref.row_matrix(a,d)
        vals=[ref.dot(r,x) for r in rows]
        if any(v>1 for v in vals) or {i for i,v in enumerate(vals) if v==1}!=set(S):raise ValueError('not exact feasible tight set')
    return dict(status='PASS',labels=len(a),dimension=d,accepted=accept,mean_sign=(mean>0)-(mean<0))


def run():
    rng=random.Random(302); counts=Counter(); tables=[]; saved=[]
    # Exhaust every proper subset, with all subset sizes including zero and m-1.
    for m in range(1,11):
        parameter_maps=[list(map(Q,range(m))),
            [Q(t,7) for t in sorted(rng.sample(range(-100,101),m))],
            [Q(i*i)+Q(i,2**40) for i in range(m)]]
        reference_family=None
        for kind,a in enumerate(parameter_maps):
            family=set(); local=Counter()
            for d in range(m):
                for S in combinations(range(m),d):
                    validate(a,d,S)
                    literal=even_gaps(m,S)
                    assert literal==adjacent_complement(m,S)
                    c=ref.candidate(a,d,S)
                    numeric=c['status']=='VERTEX'
                    assert literal==numeric
                    counts['tested_subsets']+=1;local['subsets']+=1
                    p=ref.polynomial(a[i] for i in S); values=[ref.evaluate(p,x) for x in a]
                    for i,j,n in gaps(m,S):
                        assert (values[i]*values[j]>0)==(n%2==0)
                        counts['nonroot_pair_sign_checks']+=1
                    if numeric:
                        family.add(S);local['vertices']+=1;counts['accepted_subsets']+=1
                        counts['negative_mean']+=Q(c['mean'])<0
                        counts['positive_mean']+=Q(c['mean'])>0
                        counts['original_row_checks']+=ref.verify_record(a,d,c)
                    elif c['status']=='ZERO_MEAN':counts['zero_mean_rejections']+=1
                    else:counts['mixed_sign_rejections']+=1
                    # Independent original H matrix test, not root interpolation.
                    if m<=7 and d<=4:
                        A=ref.row_matrix(a,d)
                        solution,rank,inconsistent=ref.square_solve([A[i] for i in S],[Q(1)]*d)
                        geometric=solution is not None and all(ref.dot(r,solution)<=1 for r in A)
                        assert geometric==literal
                        if geometric:
                            assert tuple(map(Q,c['point']))==solution
                            assert rank==d
                        counts['independent_square_systems']+=1
                    if kind==0 and m in (1,3,5,8,10) and ((numeric and Q(c['mean'])<0) or d==0 or d==m-1):
                        if len([s for s in saved if len(s['parameters'])==m])<4:
                            saved.append(record(a,d,S))
            if reference_family is None:reference_family=family
            else:
                assert reference_family==family
                counts['spacing_invariance_comparisons']+=1
            tables.append(dict(labels=m,spacing_kind=kind,**local))
    # No enumeration of all large subsets: exact selected positive/negative cases.
    large=[]
    for d in (15,16,31,32,63,64):
        m=2*d+3; a=[Q(i) for i in range(m)]
        if d%2==0:
            supports=[tuple(range(d)),tuple([0,*range(2,d),m-1])]
        else:
            supports=[tuple(range(d)),tuple(range(m-d,m))]
        for S in supports:
            r=record(a,d,S);checked=verify(r)
            assert checked['accepted']
            large.append(checked);saved.append(r)
    # Finite-product base lemma in arbitrary signs, independent of moment geometry.
    for n in range(11):
        for _ in range(20):
            numbers=[Q(rng.choice((-1,1))*rng.randint(1,50),rng.randint(1,20)) for _ in range(n)]
            p=Q(1)
            for x in numbers:p*=x
            assert (p>0)==(sum(x<0 for x in numbers)%2==0)
            counts['generic_nonzero_product_checks']+=1
    # Check saved data without either discovery method.
    old={name:getattr(ref,name) for name in ('polynomial','candidate','square_solve')}
    def kill(*args,**kwargs):raise AssertionError('producer called by saved verification')
    try:
        for name in old:setattr(ref,name,kill)
        audited=[verify(r) for r in saved]
    finally:
        for name,value in old.items():setattr(ref,name,value)
    invalid=[]
    def reject(label,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,ZeroDivisionError):invalid.append(label);return
        raise AssertionError('accepted invalid '+label)
    r=record(list(map(Q,range(5))),2,(0,4))
    for label,edit in [
        ('false acceptance',lambda x:x.update(parity_accepts=False)),
        ('wrong mean',lambda x:x.update(mean='2')),
        ('wrong polynomial',lambda x:x['polynomial'].__setitem__(-1,'2')),
        ('wrong nodal value',lambda x:x['nodal_values'].__setitem__(1,'123')),
        ('repeated label',lambda x:x.update(selected=[0,0])),
        ('unsorted parameters',lambda x:x['parameters'].__setitem__(0,'10')),
        ('repeated parameters',lambda x:x['parameters'].__setitem__(0,'1'))]:
        c=deepcopy(r);edit(c);reject(label,lambda c=c:verify(c))
    reject('no nonroot d=m',lambda:record([Q(0),Q(1)],2,(0,1)))
    # Dropping properness gives a vacuous parity rule but zero mean.
    allroots=ref.polynomial([Q(0),Q(1)])
    assert even_gaps(2,(0,1)) and all(ref.evaluate(allroots,Q(i))==0 for i in range(2))
    # A negative-mean valid vertex and a mixed-sign invalid set.
    negative=record(list(map(Q,range(5))),2,(0,4))
    mixed=record(list(map(Q,range(5))),2,(1,3))
    assert negative['parity_accepts'] and Q(negative['mean'])<0 and not mixed['parity_accepts']
    report=dict(status='PASS',counts=dict(counts),exhaustive_models=tables,
        large_selected=large,saved_audit=dict(records=len(saved),all_pass=True,discovery_disabled=True),
        rejected=invalid,controls=dict(negative_mean_valid=negative,mixed_sign_invalid=mixed,
          full_root_set='Vacuous parity but zero mean at d=m; not a theorem instance.'),
        scope='Exact supporting finite tests; not Lean verification, polynomial full enumeration, or a route-length theorem.')
    return report,saved


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    r,s=run();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    r['dependency_sha256']=hashlib.sha256(Path(ref.__file__).read_bytes()).hexdigest()
    a.out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('exact-tests.json',r),('fixtures.json',s)]:
        (a.out/name).write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')
    print(json.dumps(r['counts'],sort_keys=True));print('saved',len(s))
if __name__=='__main__':main()
