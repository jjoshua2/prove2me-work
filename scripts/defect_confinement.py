#!/usr/bin/env python3
"""Certify a small exceptional facet set for an existing original-H segment.

The old segment and its geometric input are unchanged. We check EVERY triangle
of every recursive link graph actually used in its construction. A missing
triangle is permitted only when ALL THREE labels are exceptional. This is not
a global flag recognizer and is not a mere hitting-set test.

The length theorem uses the localized Adiprasito--Benedetti induction (written
in the accompanying note), then a new finite-state count. Python is not Lean-
extracted. The original simple/bounded/full-dimensional input class is retained.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
import json
import original_facet_segments as seg


def bound(m: int, d: int, k: int) -> int:
    """Sharp subset-count expression; no numerical approximations."""
    seg.require(all(type(x) is int for x in (m,d,k)) and 0 <= d <= m and 0 <= k <= m,
                'invalid facet/dimension/exceptional count')
    g = m-k
    return sum(comb(k,s)*(g-d+s+1)
               for s in range(max(0,d-g), min(k,d)+1))-1


def erase_loops(path):
    out=[]; positions={}; erased=0
    for F in path:
        F=frozenset(F)
        if F in positions:
            j=positions[F]
            erased+=len(out)-j-1
            for old in out[j+1:]: positions.pop(old)
            out=out[:j+1]
        else:
            positions[F]=len(out);out.append(F)
    return out, erased


def count_states(path, m, d, exceptional):
    """Standalone finite argument. Checks intervals, not the AB theorem."""
    B=set(exceptional); good=set(range(m))-B
    seg.require(path and all(len(F)==d and set(F)<=set(range(m)) for F in path),
                'invalid active-set path')
    seg.require(all(len(set(F)&set(H))==d-1 for F,H in zip(path,path[1:])), 'not a facet-exchange walk')
    ended=set();last=set()
    for F in path:
        G=set(F)&good
        seg.require(not G&ended, 'a supposedly protected facet is reentered')
        ended |= last-G;last=G
    P,erased=erase_loops(path)
    seg.require(all(len(F&H)==d-1 for F,H in zip(P,P[1:])), 'loop erasure lost original adjacency')
    groups=defaultdict(list)
    for F in P: groups[frozenset(F&B)].append(frozenset(F&good))
    rows=[]
    for S,sets in sorted(groups.items(), key=lambda q:(len(q[0]),sorted(q[0]))):
        seen=set(sets[0]);witness=[]
        for G in sets[1:]:
            fresh=set(G)-seen
            seg.require(fresh,'fixed exceptional signature revisited without a new protected label')
            witness.append(min(fresh));seen|=G
        cap=len(good)-d+len(S)+1
        seg.require(len(sets)<=cap,'fixed-signature state bound failed')
        rows.append({'exceptional_active':sorted(S), 'states':len(sets),
                     'capacity':cap, 'new_good_witnesses':witness})
    U=bound(m,d,len(B));L=len(P)-1
    seg.require(L<=U<=(m-d+1)*2**len(B)-1,'parameterized bound failed')
    return {'raw_edges':len(path)-1,'loop_erased_edges':L,'erased_edges':len(path)-len(P),
            'exceptional_facets':sorted(B),'k':len(B),'facet_excess':m-d,
            'protected_facets':len(good),'signature_count':len(groups),
            'signature_ledger':rows,'binomial_bound':U,
            'simple_bound':(m-d+1)*2**len(B)-1,
            'loop_erased_active_path':[sorted(F) for F in P]}


def excluded_signature_bound(m,d,B,oracle,account,enumeration_cap=16):
    """Optional sharper count using ONLY already-certified original exclusions.
    A missing triangle in link(S) is not promoted to an empty global triple.
    The original separated_rows and exact dual witness must exclude that subset.
    Completeness of the exclusion list is unnecessary; any omitted exclusion
    merely weakens the bound. Exponential signature enumeration is explicitly capped.
    """
    k=len(B);g=m-k
    excluded={frozenset(c['separated_rows']) for c in oracle.cache.values()
              if c['kind']=='absent' and set(c['separated_rows'])<=set(B)}
    minimal=sorted((T for T in excluded if not any(U<T for U in excluded)),
                   key=lambda T:(len(T),sorted(T)))
    if k>enumeration_cap:
        return {'certified_signature_bound':account['binomial_bound'],
                'signature_refinement':'skipped above explicit 16-label enumeration cap',
                'certified_exceptional_exclusions':[sorted(T) for T in minimal]}
    cap=0;states=0
    for size in range(max(0,d-g),min(k,d)+1):
        for S in combinations(sorted(B),size):
            if any(T<=set(S) for T in minimal):continue
            states+=1;cap+=g-d+size+1
    for row in account['signature_ledger']:
        seg.require(not any(T<=set(row['exceptional_active']) for T in minimal),
                    'observed vertex violates certified original exclusion')
    seg.require(account['loop_erased_edges']<=cap-1<=account['binomial_bound'],
                'certified-signature count failed')
    return {'certified_signature_bound':cap-1,'allowed_exceptional_signatures':states,
            'signature_refinement':'already-verified original exclusions',
            'certified_exceptional_exclusions':[sorted(T) for T in minimal]}


def replay_graphs(data,certificate):
    verified=seg.verify(data,certificate)
    A,b,u,v=seg.parse(data);d=len(u);m=len(A)
    oracle=seg.Certified(A,b,certificate['intersections'])
    F=frozenset(seg.basis.active_rows(A,b,u));H=frozenset(seg.basis.active_rows(A,b,v))
    alg=seg.Segment(m,d,oracle,certificate['limits']['edges'],certificate['limits']['nodes'])
    path=alg.between(F&H,F,H)
    return A,b,u,v,alg,path,verified


def triangles(alg):
    for S,G in sorted(alg.graphs.items(), key=lambda q:(len(q[0]), sorted(q[0]))):
        for a,b,c in combinations(sorted(G),3):
            if b in G[a] and c in G[a] and c in G[b]:
                yield S,frozenset((a,b,c))


def verify(data,cert):
    seg.require(cert['format']=='facet-defect-confinement-v1','unknown confinement format')
    A,b,u,v,alg,path,original=replay_graphs(data,cert['segment'])
    B=seg.labels(cert['exceptional_facets'],len(A))
    O=seg.Certified(A,b,cert['intersections'])
    absent=[];checked=0
    for S,T in triangles(alg):
        checked+=1
        if not O.ask(S|T):
            seg.require(T<=B,'missing triangle is not wholly contained in the exceptional set')
            absent.append({'locked':sorted(S),'triangle':sorted(T)})
    # This direct check is redundant given the written localized AB proof. It
    # also rejects stale/mismatched executions independently of that argument.
    account=count_states(path,len(A),len(u),B)
    seg.require(all(set(x['triangle'])<=B for x in absent),'bad confinement readback')
    return {'status':'PASS','dimension':len(u),'original_rows':len(A),
            'visited_links':len(alg.graphs),'triangles_checked':checked,
            'missing_link_triangles':len(absent),'missing_triangle_witnesses':absent,
            **account,**excluded_signature_bound(len(A),len(u),B,O,account),
            'scope':'All used-link triangles checked against original-H witnesses; written partial-nonrevisiting and state-count argument, not Lean verification.'}


def construct(data,segment_output,exceptional=None,triangle_cap=100000,query_cap=200000,oracle=None):
    seg.require(type(triangle_cap)is int and triangle_cap>0,'invalid triangle cap')
    c=segment_output['certificate'] if 'certificate' in segment_output else segment_output
    A,b,u,v,alg,path,_=replay_graphs(data,c)
    O=seg.Discovery(A,b,u,v,20000,query_cap) if oracle is None else oracle
    # Reuse only already-checked records. No call bypasses original geometric
    # auditing. Present answers and excluded subsets reduce repeated LP work.
    for item in c['intersections']:
        S=frozenset(item['rows']);O.cache[seg.key(S)]=item
        if item['kind']=='present':
            x=tuple(map(seg.rat,item['point']))
            if x not in O.known:O.known.append(x)
        else:O.absent.append((frozenset(item['separated_rows']),item))
    all_bad=set();n=0
    for S,T in triangles(alg):
        seg.require(n<triangle_cap,'triangle audit cap; no confinement claim')
        n+=1
        if not O.ask(S|T):all_bad|=T
    B=sorted(all_bad) if exceptional is None else sorted(exceptional)
    out={'format':'facet-defect-confinement-v1','segment':c,
         'exceptional_facets':B,'intersections':list(O.cache.values())}
    report=verify(data,out)
    return {'certificate':out,'verified':report,
            'additional_discovery':{'lp_maximizations_including_rechecked_bounds':O.lp_calls,
                                    'simplex_pivots':O.solver.pivots,'total_cached_intersections':len(O.cache)},
            'condition':'execution-local triangle confinement, not global flagness or a minimal defect hitting set'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('input',type=Path);p.add_argument('segment',type=Path)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--certificate',action='store_true')
    p.add_argument('--triangle-cap',type=int,default=100000)
    a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());raw=json.loads(a.segment.read_text())
        out=verify(data,raw) if a.certificate else construct(data,raw,triangle_cap=a.triangle_cap)
        a.output.write_text(json.dumps(seg.serial(out),indent=2,sort_keys=True)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No verified exceptional-facet bound: {exc}\n')
if __name__=='__main__':main()
