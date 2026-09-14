#!/usr/bin/env python3
"""Exact event ordering, stationary compression, and whole-face route tests.
This is an independent rational regression, not extracted Lean or a compiler.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations, product
from copy import deepcopy
from pathlib import Path
import json, hashlib, random, time

ROOT=Path(__file__).resolve().parents[1]

def need(ok, message):
    if not ok: raise ValueError(message)

def rat(x):
    need(type(x) in (int,str,Q), 'only exact rational inputs')
    return Q(x)

def dot(x,y):return sum((a*b for a,b in zip(x,y)),Q(0))
def value(line,t):return line[0]+t*line[1]

def validate(lines):
    lines=[[(rat(a),rat(b)) for a,b in factor] for factor in lines]
    need(all(factor for factor in lines),'empty factor has no endpoint tuple')
    need(all(len({a for a,b in factor})==len(factor) for factor in lines),'initial scores not injective')
    for factor in lines:
        top=max(value(q,Q(1)) for q in factor)
        need(sum(value(q,Q(1))==top for q in factor)==1,'final endpoint is not unique')
    return lines

def roots(lines):
    result={Q(0),Q(1)}
    for factor in lines:
        for (a,b),(c,d) in combinations(factor,2):
            if b!=d:
                u=(c-a)/(b-d)
                if 0<u<1:result.add(u)
    return sorted(result)

def winner(factor,t):
    vals=[value(q,t) for q in factor]; maximum=max(vals)
    need(vals.count(maximum)==1,'sample has a tie')
    return vals.index(maximum)

def construct(lines):
    lines=validate(lines);cuts=roots(lines)
    times=[(l+r)/2 for l,r in zip(cuts,cuts[1:])]
    raw=[tuple(winner(f,t) for f in lines) for t in times]
    keep=[0]
    for j in range(1,len(raw)):
        if raw[j]!=raw[keep[-1]]:keep.append(j)
    transitions=[j-1 for j in keep[1:]]
    return {'cuts':cuts,'raw_times':times,'raw':raw,'keep':keep,
            'source_transitions':transitions,'walls':[cuts[j+1] for j in transitions]}

def audit(lines,cert):
    lines=validate(lines);expected=roots(lines)
    need(cert['cuts']==expected,'missing, extra or reordered root')
    ts=cert['raw_times'];raw=cert['raw'];keep=cert['keep'];qsteps=cert['source_transitions']
    need(ts==[(l+r)/2 for l,r in zip(expected,expected[1:])],'wrong interval sample')
    need(len(raw)==len(ts),'missing raw winner')
    comparisons=0
    for j,(l,r,t,p) in enumerate(zip(expected,expected[1:],ts,raw)):
        need(len(p)==len(lines) and l<t<r,'invalid state or open sample')
        for i,factor in enumerate(lines):
            need(type(p[i]) is int and 0<=p[i]<len(factor),'invalid pick')
            for q in range(len(factor)):
                if q!=p[i]:need(value(factor[q],t)<value(factor[p[i]],t),'winner not strict')
                for u in (l,r):
                    need(value(factor[q],u)<=value(factor[p[i]],u),'winner does not persist to boundary')
                    comparisons+=1
    need(keep and keep[0]==0 and all(type(j)is int for j in keep),'invalid compression indices')
    need(all(a<b for a,b in zip(keep,keep[1:])) and keep[-1]<len(raw),'indices not increasing')
    need(len(qsteps)==len(keep)-1 and len(cert['walls'])==len(qsteps),'wrong transition count')
    expected_keep=[0]
    for j in range(1,len(raw)):
        if raw[j]!=raw[expected_keep[-1]]:expected_keep.append(j)
    need(keep==expected_keep,'compression loses or invents transitions')
    need(raw[keep[0]]==tuple(winner(f,0) for f in lines),'first endpoint changed')
    need(raw[keep[-1]]==tuple(winner(f,1) for f in lines),'last endpoint changed')
    rank=lambda p:sum(sum(b<lines[i][p[i]][1] for a,b in f) for i,f in enumerate(lines))
    for j,(left,right,q,u) in enumerate(zip(keep,keep[1:],qsteps,cert['walls'])):
        need(left<=q<right and right==q+1 and raw[left]==raw[q] and raw[q]!=raw[q+1],
             'retained transition is not an original boundary')
        need(u==expected[q+1] and ts[left]<u<ts[right],'wrong retained wall')
        need(rank(raw[left])<rank(raw[right]),'slope rank does not increase')
        for i,factor in enumerate(lines):
            p0,p1=raw[left][i],raw[right][i]
            need(value(factor[p0],u)==value(factor[p1],u),'neighboring winners do not tie')
            need(all(value(s,u)<=value(factor[p0],u) for s in factor),'wall winner not maximal')
    bound=sum(len(f)-1 for f in lines)
    need(len(qsteps)<=bound,'additive switch bound failed')
    return {'raw_intervals':len(raw),'retained_transitions':len(qsteps),
            'stationary_transitions_removed':len(raw)-len(keep),'comparisons':comparisons,'bound':bound}

def independent_envelopes(lines):
    """Independent reference: solve each line's winning interval using all
    pairwise dominance inequalities. It never uses the root-sort constructor.
    """
    events={Q(0),Q(1)};states=[]
    for factor in lines:
        intervals=[]
        for p,(a,b) in enumerate(factor):
            lo,hi=Q(0),Q(1);valid=True
            for c,d in factor:
                delta=b-d;rhs=c-a
                if not delta:
                    if rhs>0:valid=False;break
                elif delta>0:lo=max(lo,rhs/delta)
                else:hi=min(hi,rhs/delta)
            if valid and lo<hi:
                intervals.append((lo,hi,p));events.update((lo,hi))
        states.append(intervals)
    events=sorted(t for t in events if 0<=t<=1)
    raw=[]
    for l,r in zip(events,events[1:]):
        t=(l+r)/2;p=[]
        for ints in states:
            hit=[q for a,b,q in ints if a<t<b]
            need(len(hit)==1,'reference interval cover failed');p.append(hit[0])
        p=tuple(p)
        if not raw or raw[-1]!=p:raw.append(p)
    return raw

def scores(factors,f,g):return [[(dot(f,p),dot(g,p)) for p in S] for S in factors]
def vecsub(x,y):return tuple(a-b for a,b in zip(x,y))
def vecsum(xs,d):
    xs=tuple(xs)
    return tuple(sum((x[j] for x in xs),Q(0)) for j in range(d))

def proportional(x,e):
    j=next((j for j,a in enumerate(e) if a),None)
    need(j is not None,'zero direction')
    t=x[j]/e[j]
    need(all(a==t*b for a,b in zip(x,e)),'independent simultaneous tie')
    return t

def geometric_audit(factors,f,g,cert,enumerate_sums=False):
    d=len(f);lines=scores(factors,f,g);stats=audit(lines,cert)
    # Check the stronger genericity condition on ALL ties, including losers.
    for u in cert['cuts'][1:-1]:
        tie=[]
        for S in factors:
            for x,y in combinations(S,2):
                e=vecsub(x,y)
                if dot(f,e)+u*dot(g,e)==0:tie.append(e)
        if tie:
            for e in tie:proportional(e,tie[0])
    pts=[vecsum((S[p] for S,p in zip(factors,cert['raw'][j])),d) for j in cert['keep']]
    tuplechecks=0
    # Extra endpoint comparisons are not discarded by interpolation. A rational
    # vector c with both endpoint scores -1 provides nonvacuous test data.
    final=tuple(a+b for a,b in zip(f,g)); comparisons=[]
    for j,l in combinations(range(d),2):
        determinant=f[j]*final[l]-f[l]*final[j]
        if determinant:
            c=[Q(0)]*d
            c[j]=(f[l]-final[l])/determinant
            c[l]=(final[j]-f[j])/determinant
            comparisons=[tuple(m*x for x in c) for m in (1,2,3)]
            break
    preserved=0
    for c in comparisons:
        need(dot(f,c)<0 and dot(final,c)<0,'invalid extra endpoint comparison')
        for u in cert['walls']:
            need(dot(f,c)+u*dot(g,c)<0,'strict common comparison was lost')
            preserved+=1
    sums=list(set(vecsum(tup,d) for tup in product(*factors))) if enumerate_sums else None
    for step,u in enumerate(cert['walls']):
        lhs=cert['raw'][cert['keep'][step]];rhs=cert['raw'][cert['keep'][step+1]]
        changed=next(i for i in range(len(factors)) if lhs[i]!=rhs[i])
        e=vecsub(factors[changed][rhs[changed]],factors[changed][lhs[changed]])
        total=Q(0)
        for i,S in enumerate(factors):
            p,q=S[lhs[i]],S[rhs[i]];eta=proportional(vecsub(q,p),e)
            need(eta>=0,'cancelling component transition');total+=eta
            h=dot(f,p)+u*dot(g,p)
            for z in S:
                score=dot(f,z)+u*dot(g,z)
                need(score<=h,'invalid supporting inequality')
                if score==h:
                    t=proportional(vecsub(z,p),e)
                    need(0<=t<=eta,'whole factor face is not the prescribed segment')
        need(total>0 and vecsub(pts[step+1],pts[step])==tuple(total*a for a in e),'stationary total or false sum')
        if sums is not None:
            objective=[a+u*b for a,b in zip(f,g)]
            bound=dot(objective,pts[step]);top=[]
            for z in sums:
                score=dot(objective,z);tuplechecks+=1
                need(score<=bound,'sum support incorrect')
                if score==bound:top.append(z)
            need(pts[step] in top and pts[step+1] in top,'exposed endpoints absent')
            for z in top:
                t=proportional(vecsub(z,pts[step]),vecsub(pts[step+1],pts[step]))
                need(0<=t<=1,'global exposed slice is higher dimensional')
    stats.update(whole_sum_comparisons=tuplechecks,vertices=pts,strict_comparisons_preserved=preserved)
    return stats

def fixed_core_audit(factors,f,g,cert,core_size=7,enumerate_sums=False):
    """Keep an exposed core vertex fixed and independently check global slices.
    The number of core points is NOT added to the factor transition budget.
    """
    d=len(f);end=tuple(a+b for a,b in zip(f,g));rng=random.Random(7300+d+core_size)
    core=[tuple(Q(0) for _ in range(d))]
    for j,l in combinations(range(d),2):
        det=f[j]*end[l]-f[l]*end[j]
        if det:
            c=[Q(0)]*d;c[j]=(f[l]-end[l])/det;c[l]=(end[j]-f[j])/det
            for _ in range(core_size-1):
                z=tuple(Q(rng.randrange(-9,10)) for _ in range(d))
                eps=Q(1)/(2*(abs(dot(f,z))+abs(dot(end,z))+1))
                q=tuple(a+eps*b for a,b in zip(c,z))
                need(dot(f,q)<0 and dot(end,q)<0,'core endpoint exposure lost')
                core.append(q)
            break
    lines=scores(factors,f,g); picks=[cert['raw'][j] for j in cert['keep']]
    path=[vecsum((S[p] for S,p in zip(factors,pk)),d) for pk in picks]
    totalchecks=0; corechecks=0
    sums=list(set(vecsum(tup,d) for tup in product(*factors))) if enumerate_sums else None
    full=list(set(tuple(a+b for a,b in zip(c,z)) for c in core for z in sums)) if sums is not None else None
    for j,u in enumerate(cert['walls']):
        h=tuple(a+u*b for a,b in zip(f,g))
        for c in core[1:]:
            need(dot(h,c)<0,'wall failed to expose the same core vertex');corechecks+=1
        if full is not None:
            beta=dot(h,path[j]);edge=vecsub(path[j+1],path[j]);seen=set()
            for z in full:
                totalchecks+=1;val=dot(h,z)
                need(val<=beta,'full core-plus-factor support bound failed')
                if val==beta:
                    q=proportional(vecsub(z,path[j]),edge)
                    need(0<=q<=1,'global full-sum wall not an edge');seen.add(z)
            need(path[j] in seen and path[j+1] in seen,'global edge endpoints missing')
    need(len(cert['walls'])<=sum(len(S)-1 for S in factors),'core size charged incorrectly')
    return {'core_points':len(core),'core_strict_comparisons':corechecks,'full_sum_comparisons':totalchecks}

def main():
    (ROOT/'research').mkdir(parents=True,exist_ok=True)
    (ROOT/'fixtures').mkdir(parents=True,exist_ok=True)
    start=time.monotonic();rng=random.Random(242243)
    total=dict(score_systems=0,raw_intervals=0,retained_transitions=0,stationary_transitions_removed=0,
               comparisons=0,geometric_systems=0,genuine_edges=0,whole_sum_comparisons=0,strict_comparisons_preserved=0,core_wall_comparisons=0,full_core_sum_comparisons=0)
    examples=[[],[[(0,0)]],[[(0,0),(1,0)]],
       [[(0,0),(-1,2)],[(0,0),(-2,4)]],
       [[(10,0),(1,-2),(0,2),(-3,9)]]]
    for _ in range(350):
        line=[]
        for i in range(rng.randrange(0,7)):
            n=rng.randrange(1,7); aa=rng.sample(range(-60,61),n)
            while True:
                row=[(Q(a),Q(rng.randrange(-80,81),rng.randrange(1,6))) for a in aa]
                vals=[a+b for a,b in row]
                if vals.count(max(vals))==1:break
            line.append(row)
        examples.append(line)
    nontrivial_stationary=0;parallel=0
    for data in examples:
        data=validate(data);cert=construct(data);s=audit(data,cert)
        need([cert['raw'][j] for j in cert['keep']]==independent_envelopes(data),'independent envelope disagreement')
        total['score_systems']+=1
        for key in ('raw_intervals','retained_transitions','stationary_transitions_removed','comparisons'):total[key]+=s[key]
        nontrivial_stationary+=s['stationary_transitions_removed']>0
    geometry=[([], (Q(1),Q(2)), (Q(-3),Q(1)))]
    # Include simultaneous PARALLEL components and redundant collinear listed points.
    geometry.append(([[(Q(0),Q(0)),(Q(1),Q(0))],[(Q(0),Q(0)),(Q(2),Q(0))]],(-Q(1),Q(0)),(Q(2),Q(0))))
    geometry.append(([[(Q(0),Q(0)),(Q(1),Q(0)),(Q(2),Q(0))]],(-Q(1),Q(0)),(Q(2),Q(0))))
    for _ in range(65):
        d=rng.randrange(2,5);factors=[]
        for _ in range(rng.randrange(1,5)):
            n=rng.randrange(1,5);S=set()
            while len(S)<n:S.add(tuple(Q(rng.randrange(-5,6)) for j in range(d)))
            factors.append(sorted(S))
        for attempt in range(100):
            f=tuple(Q(rng.randrange(-10000,10001)) for _ in range(d))
            g=tuple(-2*a+Q(rng.randrange(-10000,10001),100) for a in f)
            try:
                cert=construct(scores(factors,f,g));geometric_audit(factors,f,g,cert)
                break
            except ValueError:continue
        else:raise AssertionError('generic search cap')
        geometry.append((factors,f,g))
    for factors,f,g in geometry:
        cert=construct(scores(factors,f,g));s=geometric_audit(factors,f,g,cert,True)
        total['geometric_systems']+=1;total['genuine_edges']+=s['retained_transitions']
        total['whole_sum_comparisons']+=s['whole_sum_comparisons']
        total['strict_comparisons_preserved']+=s['strict_comparisons_preserved']
        cs=fixed_core_audit(factors,f,g,cert,7,True)
        total['core_wall_comparisons']+=cs['core_strict_comparisons']
        total['full_core_sum_comparisons']+=cs['full_sum_comparisons']
        for j in range(len(cert['walls'])):
            p,q=(cert['raw'][cert['keep'][j+t]] for t in (0,1))
            parallel+=sum(a!=b for a,b in zip(p,q))>1
    large=[]
    for r,d in ((16,8),(32,12),(64,16)):
        factors=[]
        for i in range(r):
            S=set()
            while len(S)<3:S.add(tuple(Q(rng.randrange(-10,11)) for _ in range(d)))
            factors.append(sorted(S))
        for attempt in range(100):
            f=tuple(Q(rng.randrange(-1000000,1000001)) for _ in range(d))
            g=tuple(-2*a+Q(rng.randrange(-1000000,1000001),100) for a in f)
            try:cert=construct(scores(factors,f,g));s=geometric_audit(factors,f,g,cert);break
            except ValueError:continue
        else:raise AssertionError('large generic search cap')
        core_result=fixed_core_audit(factors,f,g,cert,201,False)
        large.append({**core_result,'factors':r,'dimension':d,'raw_tuple_product':3**r,'raw_intervals':s['raw_intervals'],
          'edges':s['retained_transitions'],'bound':2*r,'strict_comparisons_preserved':s['strict_comparisons_preserved'],'whole_tuple_product_enumerated':False})
    rejected=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,IndexError,KeyError):rejected.append(name)
        else:raise AssertionError('forged case accepted: '+name)
    good_lines=[[(Q(0),Q(0)),(Q(-1),Q(4)),(Q(-5),Q(9))],[(Q(0),Q(0)),(Q(-3),Q(6))]]
    good=construct(good_lines)
    mutations=[
      ('missing_root',lambda c:c['cuts'].pop(1)),
      ('reordered_roots',lambda c:c['cuts'].reverse()),
      ('wall_moved',lambda c:c['walls'].__setitem__(0,Q(9,10))),
      ('sample_moved',lambda c:c['raw_times'].__setitem__(0,Q(0))),
      ('winner_changed',lambda c:c['raw'].__setitem__(0,(1,1))),
      ('missing_retained_state',lambda c:c['keep'].pop()),
      ('false_source_transition',lambda c:c['source_transitions'].__setitem__(0,999)),
      ('duplicated_retained_state',lambda c:c['keep'].insert(1,c['keep'][0])),
    ]
    for name,mutate in mutations:
        bad=deepcopy(good);mutate(bad);reject(name,lambda bad=bad:audit(good_lines,bad))
    reject('empty_factor',lambda:construct([[]]))
    reject('duplicate_initial_scores',lambda:construct([[(0,0),(0,2)]]))
    reject('endpoint_tie',lambda:construct([[(0,1),(1,0)]]))
    reject('float_input',lambda:construct([[(0.0,1),(1,2)]]))
    square=[[(Q(0),Q(0)),(Q(1),Q(0))],[(Q(0),Q(0)),(Q(0),Q(1))]]
    f=(-Q(1),-Q(1));g=(Q(2),Q(2));c=construct(scores(square,f,g))
    reject('independent_simultaneous_square_diagonal',lambda:geometric_audit(square,f,g,c))
    out={'status':'PASS','scope':'exact rational regression; not Lean verification',**total,
      'systems_with_stationary_events':nontrivial_stationary,'parallel_multi_factor_steps':parallel,
      'large':large,'rejected':rejected,'rejected_count':len(rejected),'seconds':round(time.monotonic()-start,3)}
    out['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
        for p in [Path(__file__)]}
    (ROOT/'research/FINITE_ENVELOPE_SEQUENCE_TESTS.json').write_text(json.dumps(out,indent=2)+'\n')
    def serial(x):
        if isinstance(x,Q):return str(x)
        if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
        if isinstance(x,(tuple,list)):return [serial(v) for v in x]
        return x
    (ROOT/'fixtures/finite_envelope_sequence.json').write_text(json.dumps(serial({'scores':good_lines,'sequence':good}),indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
