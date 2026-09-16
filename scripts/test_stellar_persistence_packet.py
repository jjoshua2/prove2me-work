#!/usr/bin/env python3
"""Independent finite checks for the formal stellar persistence packet.
These checks are NOT Lean compilation or a platform verdict.
"""
from itertools import combinations
from pathlib import Path
import hashlib, json, random

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'research/publication_packets/stellar_persistence_count'

def subsets(V):
    V = sorted(V)
    return [frozenset(s) for k in range(len(V)+1) for s in combinations(V,k)]

def maximal(K):
    return [F for F in K if not any(F < G for G in K)]

def minimal_nonfaces(K,V):
    return {N for N in subsets(V) if N not in K and all(T in K for T in subsets(N) if T != N)}

def stellar_literal(K,E,z):
    out=set()
    for F in maximal(K):
        pieces=[(F-{a})|{z} for a in E] if E <= F else [F]
        for P in pieces: out.update(subsets(P))
    return out

def checked_step(K,V,E,z,A):
    assert z not in V and len(E)>=2 and E in K
    out=stellar_literal(K,E,z)
    expected=set()
    for T in subsets(V|{z}):
        if z in T:
            okay=((T-{z})|E) in K and not E <= (T-{z})
        else:
            okay=T in K and not E <= T
        if okay: expected.add(T)
    assert out == expected
    f=lambda N: ((N-E)|{z}) if E<=N else N
    images={f(N) for N in A}
    assert len(images)==len(A) and E not in images
    B=images|{E}
    assert len(B)==len(A)+1
    assert B <= minimal_nonfaces(out,V|{z})
    return out,V|{z},B

def main():
    V=frozenset(range(4));candidates=[N for N in subsets(V) if len(N)>=2]
    complexes=[];steps=0;large_faces=0;descendants=0
    for mask in range(1<<len(candidates)):
        nf={N for i,N in enumerate(candidates) if mask>>i&1}
        if any(A<B for A in nf for B in nf): continue
        K={F for F in subsets(V) if not any(N<=F for N in nf)}
        assert minimal_nonfaces(K,V)==nf
        complexes.append(K)
        for E in K:
            if len(E)<2: continue
            out,V1,A1=checked_step(K,V,E,4,nf)
            steps+=1;large_faces+=len(E)>2;descendants+=len(nf)
    rng=random.Random(273)
    chains=0;chain_steps=0;flag_terminals=0
    for _ in range(80):
        K=set(rng.choice(complexes));ground=V
        initial=minimal_nonfaces(K,ground)
        # A certified proper subfamily must work as well as the complete family.
        A={N for N in sorted(initial,key=lambda N:tuple(sorted(N))) if rng.randrange(2)}
        q=len(A);t=0
        for i in range(4):
            options=[E for E in K if len(E)>=2]
            if not options:break
            E=rng.choice(sorted(options,key=lambda E:(len(E),tuple(sorted(E)))))
            K,ground,A=checked_step(K,ground,E,max(ground)+1,A)
            t+=1
            assert len(A)==q+t and len(ground)==4+t
        if all(len(N)==2 for N in minimal_nonfaces(K,ground)):
            assert q+t<=len(ground)*(len(ground)-1)//2
            flag_terminals+=1
        chains+=1;chain_steps+=t
    sol=(PACKET/'solution.lean').read_text()
    meta=json.loads((PACKET/'problem.json').read_text())
    sig=sol.split('\ntheorem solution\n',1)[1].split(' := by\n',1)[0]
    formal=meta['formal_statement'].split('\ntheorem stellar_persistence_count\n',1)[1].split(' := by sorry',1)[0]
    assert sig==formal, 'public formal statement differs from solution signature'
    for token in ('sorry','admit','sorryAx','native_decide','unsafe'):
        assert token not in sol, 'forbidden proof token: '+token
    assert meta['preamble']=='import Mathlib'
    assert meta['env']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
    report={'status':'PASS','scope':'independent finite semantics and exact signature checks, NOT Lean verification',
      'complexes':len(complexes),'single_steps':steps,'larger_face_steps':large_faces,'old_descendants':descendants,
      'subfamily_chains':chains,'chain_steps':chain_steps,'flag_terminals':flag_terminals,
      'exact_public_signature_match':True,'proof_lines':len(sol.splitlines()),
      'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/STELLAR_PERSISTENCE_PACKET_TESTS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__': main()
