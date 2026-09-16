#!/usr/bin/env python3
"""Realize higher-defect clutters in genuine nestohedra; test energy barriers.

A nonface-upward connected building set realizes EXACTLY the prescribed
higher minimal nonfaces on its singleton facets, with only missing pairs
elsewhere. This is an application of the classical nested-complex theorem.
The Fano result is a positive barrier for EVERY EDGE-stellar flagification,
not for arbitrary larger-face subdivisions, and not a diameter lower bound.
The direct endpoint-transfer router is independent of stellar completion.
"""
from itertools import combinations
import stellar_defect_budget as stellar
from endpoint_transfer_routes import require


def steiner_triples(r):
    require(type(r) is int and r >= 2, 'binary rank must be >=2')
    n=2**r-1
    H=sorted({tuple(sorted((a-1,b-1,(a^b)-1)))
              for a in range(1,n+1) for b in range(a+1,n+1)})
    counts={E:0 for E in combinations(range(n),2)}
    for T in H:
        for E in combinations(T,2): counts[E]+=1
    require(len(H) == n*(n-1)//6 and all(c == 1 for c in counts.values()), 'not a Steiner triple system')
    return n,H


def upward_building(n, high, subset_cap=100000):
    require(type(n) is int and n >= 3 and type(subset_cap) is int and subset_cap >= 2**n,
            'upward-building enumeration cap; no implicit catalogue claim')
    H=stellar.Complex.create(n,high).higher()
    require(H and len(H) == len(high), 'nonempty higher antichain required')
    masks=[sum(1<<i for i in N) for N in H]
    B=[S for S in range(1,1<<n) if S.bit_count() == 1 or any(S&N == N for N in masks)]
    B.sort(key=lambda s:(s.bit_count(), tuple(i for i in range(n) if s>>i&1)))
    return [[i for i in range(n) if S>>i&1] for S in B]


def nested_complex(n, high, B):
    labels=[frozenset(S) for S in B if len(S) < n]
    index={S:i for i,S in enumerate(labels)}; blocks=set(map(frozenset,B))
    missing=[]
    for i,j in combinations(range(len(labels)),2):
        A,C=labels[i],labels[j]
        if not(A <= C or C <= A) and (A&C or A|C in blocks): missing.append([i,j])
    missing += [[index[frozenset([v])] for v in N] for N in high]
    K=stellar.Complex.create(len(labels),missing)
    return K,labels


def nested_test(labels,B,vertices):
    """Independent direct nested-set definition, used only on small test sets."""
    chosen=[labels[i] for i in vertices]; blocks=set(map(frozenset,B))
    if any(A&C and not(A <= C or C <= A) for A,C in combinations(chosen,2)): return False
    for size in range(2,len(chosen)+1):
        for antichain in combinations(chosen,size):
            if all(not(A&C) for A,C in combinations(antichain,2)):
                if frozenset().union(*antichain) in blocks: return False
    return True


def first_original_pair_bound(K, original_n, high, edge):
    """Verify the lower-bound mechanism after arbitrary auxiliary EDGE moves.
    The old singleton restriction must remain exactly the Steiner complex.
    Check every original triple to guard against an earlier original pair cut.
    """
    expected=set(map(frozenset,high)); ground=set(range(original_n))
    require(all(K.face(E) for E in combinations(range(original_n),2)), 'an original pair was already removed')
    require({T for T in K.missing if T <= ground} == expected, 'original singleton restriction changed')
    require(len(edge) == 2 and all(i < original_n for i in edge), 'not an original pair')
    E=frozenset(edge); common=[N for N in expected if E <= N]
    mixed=[N for N in expected if len(N&E) == 1]
    require(len(common) == 1 and len(mixed) == original_n-3, 'Steiner incidence count failed')
    J,record=stellar.account(K,list(edge))
    required={N for N in expected if not E <= N} | {(N-E)|{K.n} for N in mixed}
    require(len(required) == len(high)+original_n-4 and all(N in J.higher() for N in required),
            'persistent triples or forced newborn triples missing')
    require(J.weight() >= len(high)+original_n-4, 'compulsory positive barrier failed')
    return J,record


def fano_completion(K,original_n=7):
    # This eleven-move witness was found from the seven-label induced complex.
    # Lift its fresh labels to the full nestohedral complex; outside labels
    # participate only in missing pairs and do not alter these higher triples.
    word=[(0,1),(3,7),(6,7),(0,3),(6,10),(0,6),
          (1,3),(6,13),(1,6),(3,6),(2,4)]
    initial=K.n; weights=[K.weight()]; records=[]
    for E in word:
        edge=[i if i < original_n else initial+i-original_n for i in E]
        K,r=stellar.account(K,edge); records.append(r); weights.append(K.weight())
    require(not K.higher() and weights == [7,10,8,6,7,5,4,5,3,2,1,0], 'Fano completion changed')
    return K,{'steps':records,'weights':weights,'peak_weight':max(weights),
              'edge_subdivisions':len(records),'refined_vertices':K.n,
              'minimum_possible_peak_weight':10,'minimum_possible_move_count_claimed':False}
