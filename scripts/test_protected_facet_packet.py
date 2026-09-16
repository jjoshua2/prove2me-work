#!/usr/bin/env python3
"""Independent finite checks for the protected-facet Lean packet.

The test validates the actual injective encoding by cumulative protected labels.
It is not Lean verification and does not assert polytopality of abstract walks.
Only the Python standard library is required.
"""
from __future__ import annotations
from itertools import combinations, permutations
from pathlib import Path
import hashlib, json, random, re

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'research/publication_packets/protected_facet_state_count'


def powerset(s):
    s = sorted(s)
    return [frozenset(c) for k in range(len(s)+1) for c in combinations(s,k)]


def intervals(path, B):
    ended = set()
    previous = set()
    for state in path:
        protected = set(state) - B
        if protected & ended:
            return False
        ended |= previous - protected
        previous = protected
    return True


def analyze(V, B, d, path, allowed=None):
    V, B = set(V), set(B)
    assert type(d) is int and d >= 0
    path = list(map(frozenset,path))
    assert all(len(F)==d and F<=V for F in path), 'support/cardinality assumption'
    assert len(set(path))==len(path), 'distinct-state assumption'
    assert intervals(path,B), 'protected-interval assumption'
    signatures = set(F & B for F in path)
    C = signatures if allowed is None else set(map(frozenset,allowed))
    assert signatures <= C, 'signature registry does not cover the path'
    seen=set(); codes=[]; previous_seen=[]; good_sizes=[]
    for F in path:
        good=set(F)-B
        seen |= good
        retired=seen-good
        assert retired <= V-set(F), 'retired labels exceed original complement'
        assert len(retired)<=max(0,len(V)-d)
        assert len(retired)<=max(0,len(V-B)-(d-len(F&B)))
        assert len(seen)==len(retired)+len(good)
        previous_seen.append(set(seen)); good_sizes.append(len(good))
        codes.append((F & B,len(retired)))
    assert len(set(codes))==len(path), 'canonical signature/counter map not injective'
    e=max(0,len(V)-d)
    uniform=(e+1)*2**len(B)
    registry=(e+1)*len(C)
    weighted=sum(max(0,len(V-B)-max(0,d-len(S)))+1 for S in C)
    assert len(path)<=uniform and len(path)<=registry and len(path)<=weighted
    return {'states':len(path),'edges_if_a_nonempty_route':max(0,len(path)-1),
        'uniform_state_bound':uniform,'registry_state_bound':registry,
        'weighted_state_bound':weighted,'signatures':len(C),
        'codes':[{'exceptional':sorted(S),'retired_protected':r} for S,r in codes]}


def rejected(name, thunk, target):
    try:
        thunk()
    except AssertionError:
        target.append(name)
    else:
        raise AssertionError('invalid input accepted: '+name)


def main():
    considered=valid=nonedge_valid=exceptional_reentries=0
    for m in range(5):
        V=frozenset(range(m));Bs=powerset(V)
        for d in range(m+1):
            states=list(map(frozenset,combinations(range(m),d)))
            for n in range(len(states)+1):
                for P in permutations(states,n):
                    for B in Bs:
                        considered+=1
                        if not intervals(P,B):continue
                        a=analyze(V,B,d,P)
                        analyze(V,B,d,P,powerset(B))
                        valid+=1
                        nonedge_valid+=any(len(F&H)!=max(0,d-1) for F,H in zip(P,P[1:]))
                        exceptional_reentries+=not intervals(P,set())
    rng=random.Random(20260916);random_count=0;max_states=0;examples=[]
    for m in range(5,15):
        for _ in range(40):
            d=rng.randrange(1,m);V=set(range(m))
            B=set(rng.sample(range(m),rng.randrange(m+1)))
            F=frozenset(rng.sample(range(m),d));P=[F];used={F};ended=set()
            for step in range(60):
                nexts=[]
                for out in F:
                    for enter in V-set(F):
                        H=(F-{out})|{enter}
                        if H not in used and not ((H-B)&ended):nexts.append(H)
                if not nexts:break
                H=rng.choice(nexts);ended |= (set(F)-B)-set(H)
                F=H;used.add(F);P.append(F)
            result=analyze(V,B,d,P)
            random_count+=1;max_states=max(max_states,len(P))
            if len(examples)<4 and len(P)>=10:
                examples.append({'V':sorted(V),'B':sorted(B),'d':d,'path':[sorted(F) for F in P],'result':result})
    # Natural empty-domain cases and exception labels not in the ground set.
    edge_cases=[]
    for d in (0,1,8):
        edge_cases.append(analyze(set(),{99},d,[],[]))
    edge_cases.append(analyze(set(),set(),0,[set()]))
    edge_cases.append(analyze({0,1},{9},1,[{0},{1}]))
    # A non-simple exchange walk is not silently required by the finite theorem.
    # No adjacency assumption is used at all: arbitrary uniform distinct states
    # with protected interval membership satisfy the same count.
    V=set(range(8));B={0,1,2,3}
    P=[{0,1,4,5},{0,2,4,6},{1,2,6,7},{2,3,6,7}]
    examples.append({'V':sorted(V),'B':sorted(B),'d':4,'path':list(map(sorted,P)),
                     'result':analyze(V,B,4,P)})
    bad=[]
    rejected('protected_facet_reentry',lambda:analyze({0,1,2},set(),2,[{0,1},{1,2},{0,2}]),bad)
    rejected('repeated_complete_state',lambda:analyze({0},set(),1,[{0},{0}]),bad)
    rejected('nonuniform_states',lambda:analyze({0,1},set(),1,[{0},{0,1}]),bad)
    rejected('state_outside_original_ground',lambda:analyze({0},set(),1,[{1}]),bad)
    rejected('missing_allowed_signature',lambda:analyze({0,1},{0},1,[{0},{1}],[set()]),bad)
    # These numerical counterexamples show why the important assumptions cannot
    # be omitted, not only that the input validator checks their spelling.
    assert 3 > (3-2+1)*2**0  # three states with a protected reentry
    assert 2 > (1-1+1)*2**0  # repeated singleton state
    sol=(PACKET/'solution.lean').read_text()
    problem=json.loads((PACKET/'problem.json').read_text())
    actual=sol.split('\ntheorem solution\n',1)[1].split(' := by\n',1)[0]
    target=problem['formal_statement'].split('\ntheorem protected_facet_state_count\n',1)[1].split(' := by sorry',1)[0]
    assert actual==target, 'statement mismatch'
    assert problem['preamble']=='import Mathlib\nopen scoped BigOperators'
    assert problem['env']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|unsafe)\b',sol)
    report={'status':'PASS','scope':'independent finite semantics and statement binding, NOT Lean verification',
        'exhaustive_candidates':considered,'exhaustive_valid_cases':valid,
        'valid_cases_without_ordinary_exchange_adjacency':nonedge_valid,
        'valid_cases_with_exceptional_reentries':exceptional_reentries,
        'random_valid_exchange_paths':random_count,'largest_random_state_count':max_states,
        'edge_case_tests':len(edge_cases),'negative_controls':bad,
        'counter_bound_values':{'omit_interval':{'states':3,'false_bound':2},
                                'omit_injectivity':{'states':2,'false_bound':1}},
        'public_signature_matches':True,'solution_lines':len(sol.splitlines()),
        'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                         (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/PROTECTED_FACET_PACKET_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'research/PROTECTED_FACET_PACKET_EXAMPLES.json').write_text(json.dumps(examples,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__': main()
