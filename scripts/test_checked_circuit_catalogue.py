#!/usr/bin/env python3
"""Independent exact tests, including every excluded support and forged tables."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import random
import time
import sympy as sp
from checked_circuit_catalogue import generate, audit, require

ROOT = Path(__file__).resolve().parents[1]


def reference(A, n):
    """All supports of ALL sizes, using independent SymPy augmented systems."""
    out = []; checks = 0
    for m in range(1, n + 1):
        for s in combinations(range(n), m):
            checks += 1
            D = sp.Matrix([[row[j] for j in s] for row in A] + [[1] * m])
            R, pivots = D.row_join(sp.Matrix([0] * len(A) + [1])).rref()
            if m in pivots or len(pivots) != m:
                continue
            v = tuple(Q(str(R[i, m])) for i in range(m))
            if all(x > 0 for x in v):
                out.append({'support': list(s), 'positive': [str(x) for x in v]})
    return out, checks


def main():
    start = time.monotonic(); rng = random.Random(20260913)
    cases = [([], 0), ([], 4), ([[]], 0), ([[0, 0, 0, 0]], 4),
             ([[1, 1, 1, 1]], 4), ([[1, -1, 0]], 3),
             ([[1, -1, 0], [0, 1, -1]], 3),
             ([[1, -1, 0], [2, -2, 0], [0, 0, 0]], 3),
             ([[1, 1, -1, -1], [0, 1, 0, -1]], 4),
             ([[1, Q(-1)-Q(1,2**80), 0], [0, 1, -1]], 3)]
    for _ in range(45):
        n = rng.randrange(1, 8); k = rng.randrange(0, 4)
        cases.append(([[Q(rng.randrange(-3, 4), rng.randrange(1, 4)) for _ in range(n)] for _ in range(k)], n))
    total = dict(tables=0, supports=0, identities=0, dependent=0, left=0,
                 inconsistent=0, nonpositive=0, circuits=0, independent_all_supports=0)
    for A, n in cases:
        cert = generate(A, n)
        result = audit(A, n, json.loads(json.dumps(cert)))
        want, checks = reference(A, n)
        require(want == result['catalogue'], 'complete real-target catalogue disagrees with independent affine enumeration')
        for key, value in [('tables',1), ('supports',result['support_cells']), ('identities',result['identity_checks']),
                           ('dependent',result['dependent_cells']), ('left',result['left_inverse_cells']),
                           ('inconsistent',result['inconsistent_normalized_cells']),('nonpositive',result['nonpositive_normalized_cells']),
                           ('circuits',result['circuits']),('independent_all_supports',checks)]: total[key] += value
    # The verifier remains usable if every search routine is disabled.
    import checked_circuit_catalogue as module
    A = [[1,-1,0,0,1],[0,0,1,-1,0]]; n=5
    good = generate(A,n)
    old_rref,old_inv=module.rref,module.inverse
    def forbidden(*args,**kwargs):raise AssertionError('verifier called an untrusted search routine')
    module.rref=module.inverse=forbidden
    audit(A,n,good)
    module.rref,module.inverse=old_rref,old_inv
    # Inject a different valid left inverse for a support: same emitted vector.
    changed=deepcopy(good)
    single=next(c for c in changed['cells'] if c['support']==[0])
    single['left_inverse']=[['2','0','-1']]
    # D column=(1,0,1); [2,0,-1]*D=1, but the candidate violates Ax=0.
    audit(A,n,changed)
    require(changed['catalogue']==good['catalogue'],'noncanonical left inverse changed actual catalogue')
    # Equivalent row transformations preserve output but change certificate identities.
    transforms=0
    for _ in range(12):
        A=[[Q(rng.randrange(-3,4)) for _ in range(6)] for _ in range(3)]
        B=[A[1], [A[0][j]+2*A[1][j] for j in range(6)], [-3*A[2][j] for j in range(6)]]
        require(generate(A,6)['catalogue']==generate(B,6)['catalogue'],'equivalent row system changed catalogue')
        transforms+=1
    large=[]
    for n,k in [(18,3),(32,2),(64,0)]:
        A=[[Q(rng.randrange(-3,4)) for _ in range(n)] for _ in range(k)]
        c=generate(A,n,100000); r=audit(A,n,c)
        large.append({**{key:value for key,value in r.items() if key!='catalogue'},'n':n,'k':k,
                      'all_supports_if_unbounded':2**n,'original_graph_enumerated':False})
    # Invalid controls exercise coverage, signs, both certificate branches and input binding.
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):rejected.append(name)
        else:raise AssertionError('accepted invalid control: '+name)
    inverse_idx=next(i for i,c in enumerate(good['cells']) if len(c['support'])>=2 and c['kind']=='left_inverse')
    dep_idx=next(i for i,c in enumerate(good['cells']) if c['kind']=='dependent')
    tests=[
      ('missing_support',lambda c:c['cells'].pop()),
      ('duplicated_support',lambda c:c['cells'].__setitem__(2,deepcopy(c['cells'][1]))),
      ('reordered_support',lambda c:c['cells'].__setitem__(slice(0,2),list(reversed(c['cells'][:2])))),
      ('altered_inverse',lambda c:c['cells'][inverse_idx]['left_inverse'][0].__setitem__(0,'999')),
      ('zero_dependency',lambda c:c['cells'][dep_idx].update(null=['0']*len(c['cells'][dep_idx]['null']))),
      ('wrong_dependency_mass',lambda c:c['cells'][dep_idx]['null'].__setitem__(0,'123')),
      ('unknown_kind',lambda c:c['cells'][0].update(kind='trust_me')),
      ('missing_circuit',lambda c:c['catalogue'].pop()),
      ('extra_circuit',lambda c:c['catalogue'].append({'support':[0],'positive':['1']})),
      ('wrong_normalization',lambda c:c['catalogue'][0]['positive'].__setitem__(0,'2')),
      ('matrix_changed',lambda c:c['matrix'][0].__setitem__(0,'17')),
      ('dimension_changed',lambda c:c.update(n=6)),
      ('floating_entry',lambda c:c['matrix'][0].__setitem__(0,1.0)),
      ('boolean_dimension',lambda c:c.update(n=True)),
      ('unexpected_cell_payload',lambda c:c['cells'][0].update(assume_correct=True)),
    ]
    for name,mutate in tests:
        bad=deepcopy(good);mutate(bad);reject(name,lambda bad=bad:audit(A_test,5,bad))
    reject('partial_enumeration_cap',lambda:generate([[1,-1,0]],3,2))
    reject('same_sign_fake_null',lambda:audit([[1,1]],2,generate([[1,-1]],2)))
    # Save a complete small example and a deliberately incomplete table for external reproduction.
    (ROOT/'fixtures').mkdir(exist_ok=True)
    (ROOT/'fixtures/checked_five_coordinate_catalogue.json').write_text(json.dumps(good,indent=2)+'\n')
    receipt={'status':'PASS','scope':'Exact executable certificate tests, not Lean compilation.',
             **total,'equivalent_row_transforms':transforms,'search_free_verifier_test':'PASS',
             'valid_noncanonical_inverse_test':'PASS','large_cases':large,'rejected':rejected,
             'rejected_count':len(rejected),'elapsed_seconds':round(time.monotonic()-start,3),
             'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in sorted((ROOT/'scripts').glob('*.py'))}}
    (ROOT/'research/CHECKED_CIRCUIT_CATALOGUE_TESTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

A_test=[[1,-1,0,0,1],[0,0,1,-1,0]]
if __name__=='__main__':main()
