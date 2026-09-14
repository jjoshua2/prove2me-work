#!/usr/bin/env python3
"""Exact deterministic exposed-core-edge lifting; standard library only.

Input component point lists are complete finite-hull presentations, NOT a
claimed decomposition of an unrelated H-polytope. The producer never forms
their Cartesian product. The independent small-case audit does so explicitly.
No Python/JSON execution here is represented as Lean verification.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import itertools
import json
import random
from fractions import Fraction as F
from pathlib import Path


def need(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def dot(a, b):
    need(len(a) == len(b), 'dimension mismatch')
    return sum((x*y for x, y in zip(a, b)), F(0))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def scale(t, a):
    return tuple(t*x for x in a)


def total(vectors, dimension):
    out = (F(0),)*dimension
    for v in vectors:
        out = add(out, v)
    return out


def along(d, e):
    p = next((j for j, x in enumerate(e) if x), None)
    need(p is not None, 'zero edge direction')
    t = d[p]/e[p]
    return t if d == scale(t, e) else None


def validate_input(parts, core, u, v, f0):
    need(bool(parts) and 0 <= core < len(parts), 'missing core')
    n = len(u)
    need(n > 0 and len(v) == n and len(f0) == n, 'invalid dimension')
    need(all(parts), 'empty summand')
    for p in [u, v, f0, *(p for s in parts for p in s)]:
        need(len(p) == n and all(isinstance(x, F) for x in p), 'use exact rational vectors')
    need(u != v and u in parts[core] and v in parts[core], 'invalid core endpoints')
    e = sub(v, u)
    beta = dot(f0, u)
    need(dot(f0, v) == beta, 'core endpoints do not tie')
    for x in parts[core]:
        need(dot(f0, x) <= beta, 'core support bound failed')
        if dot(f0, x) == beta:
            t = along(sub(x, u), e)
            need(t is not None and 0 <= t <= 1, 'core face is not the claimed segment')
    return e


def lift(parts, core, u, v, f0):
    """Choose an annihilator moment-curve point, then a safe rational epsilon.

    Each nonparallel comparison is a nonzero polynomial. At most its degree
    many real roots exist, so degree_sum+1 distinct integers guarantee success.
    There is no random-search or caller-chosen search cap.
    """
    e = validate_input(parts, core, u, v, f0)
    n = len(e)
    pivot = next(j for j, x in enumerate(e) if x)
    coords = [j for j in range(n) if j != pivot]
    diffs = [sub(x, y) for s in parts for x, y in itertools.combinations(s, 2)]
    polynomials = []
    degree_sum = 0
    for d in diffs:
        if along(d, e) is not None:
            continue
        coeff = tuple(d[j]-e[j]*d[pivot]/e[pivot] for j in coords)
        need(any(coeff), 'quotient comparison vanished unexpectedly')
        degree_sum += max(i for i, z in enumerate(coeff) if z)
        polynomials.append(coeff)
    q = None
    for integer in range(degree_sum+1):
        h = [F(0)]*n
        for power, j in enumerate(coords):
            h[j] = F(integer)**power
            h[pivot] -= h[j]*e[j]/e[pivot]
        h = tuple(h)
        if all(dot(h, d) != 0 for d in diffs if along(d, e) is None):
            q = h
            break
    need(q is not None, 'finite polynomial avoidance bound violated')
    radii = [F(1)] + [abs(dot(f0, d))/(abs(dot(q, d))+1)
                       for d in diffs if dot(f0, d)]
    epsilon = min(radii)/2
    f = add(f0, scale(epsilon, q))
    left, right, lengths, active_counts = [], [], [], []
    for s in parts:
        maximum = max(dot(f, x) for x in s)
        active = [x for x in s if dot(f, x) == maximum]
        a = min(active, key=lambda x: x[pivot]/e[pivot])
        b = max(active, key=lambda x: x[pivot]/e[pivot])
        eta = (b[pivot]-a[pivot])/e[pivot]
        left.append(a); right.append(b); lengths.append(eta)
        active_counts.append(len(active))
    cert = dict(normal=f, perturbation=q, epsilon=epsilon, integer=integer,
                degree_sum=degree_sum, nonparallel_comparisons=len(polynomials),
                left=left, right=right, lengths=lengths,
                start=total(left,n), end=total(right,n), active_counts=active_counts)
    verify(parts,core,u,v,f0,cert)
    return cert


def verify(parts,core,u,v,f0,cert, exhaustive=False):
    """Check whole component support faces, without rerunning the producer."""
    e = validate_input(parts,core,u,v,f0)
    f, aa, bb, eta = cert['normal'], cert['left'], cert['right'], cert['lengths']
    need(len(f)==len(e) and len(aa)==len(bb)==len(eta)==len(parts), 'certificate dimensions')
    need(all(isinstance(x,F) for x in f) and all(isinstance(x,F) for x in eta), 'inexact certificate')
    need(dot(f,e)==0, 'objective does not annihilate the core edge')
    need(aa[core]==u and bb[core]==v and eta[core]==1, 'wrong core projection')
    ties = 0
    for s,a,b,t in zip(parts,aa,bb,eta):
        need(a in s and b in s and t>=0 and b==add(a,scale(t,e)), 'invalid component interval')
        beta = dot(f,a)
        need(dot(f,b)==beta, 'endpoint support mismatch')
        for x in s:
            need(dot(f,x)<=beta, 'missed support maximum')
            if dot(f,x)==beta:
                coefficient=along(sub(x,a),e)
                need(coefficient is not None and 0<=coefficient<=t, 'nonparallel or outlying whole support face')
                ties+=1
        for x,y in itertools.combinations(s,2):
            d=sub(x,y)
            need((dot(f,d)==0)==(along(d,e) is not None), 'nongeneric finite tie')
            if dot(f0,d):
                need(dot(f0,d)*dot(f,d)>0, 'original strict comparison changed sign')
    A,B=total(aa,len(e)),total(bb,len(e))
    need(A==cert['start'] and B==cert['end'] and A!=B, 'invalid total endpoints')
    need(along(sub(B,A),e)==sum(eta) and sum(eta)>=1, 'total edge collapsed')
    count=0
    if exhaustive:
        for choices in itertools.product(*parts):
            z=total(choices,len(e)); count+=1
            need(dot(f,z)<=dot(f,A), 'full-sum support violation')
            if dot(f,z)==dot(f,A):
                t=along(sub(z,A),sub(B,A))
                need(t is not None and 0<=t<=1, 'full-sum diagonal accepted')
    return dict(component_points=sum(map(len,parts)), active_points=ties,
                exhaustive_sum_tuples=count)


def V(*xs): return tuple(F(x) for x in xs)

def simplex(n):
    z=(F(0),)*n
    s=[z]+[tuple(F(i==j) for i in range(n)) for j in range(n)]
    return s,z,s[1],tuple(F(0) if j==0 else F(-1) for j in range(n))


def changed_coordinates(parts,u,v,f,rng):
    """Invertible rational shears; update the dual exactly, then translate."""
    parts=copy.deepcopy(parts)
    for _ in range(4):
        if len(u)<2: break
        i,j=rng.sample(range(len(u)),2); t=F(rng.randint(-3,3),2)
        def shear(x):
            y=list(x); y[i]+=t*y[j]; return tuple(y)
        parts=[[shear(x) for x in s] for s in parts]
        u,v=shear(u),shear(v)
        ff=list(f); ff[j]-=t*ff[i]; f=tuple(ff)
    shift=tuple(F(rng.randint(-3,3),3) for _ in u)
    parts=[[add(x,shift) for x in s] for s in parts]
    return parts,add(u,shift),add(v,shift),f


def encode(x):
    if isinstance(x,F): return str(x)
    if isinstance(x,dict): return {k:encode(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [encode(y) for y in x]
    return x


def run():
    rng=random.Random(240913)
    stats=dict(cases=0,component_points=0,active_points=0,exhaustive_sum_tuples=0,
               nonparallel_comparisons=0,grid_trials=0,rejected_controls=0)
    fixture=None
    # Arbitrary finite-hull factors, translated/sheared core, redundant points.
    for case in range(90):
        n=1+case%5
        core,u,v,f=simplex(n)
        if case%3==0: core += [scale(F(1,3),v),u]
        parts=[core]
        for _ in range(case%5):
            k=rng.randint(1,4)
            parts.append([tuple(F(rng.randint(-3,3),rng.randint(1,3)) for _ in range(n))
                          for _ in range(k)])
        if case%7==0: parts.append([u,v,scale(F(2),v)]) # parallel support segment
        parts,u,v,f=changed_coordinates(parts,u,v,f,rng)
        cert=lift(parts,0,u,v,f)
        got=verify(parts,0,u,v,f,cert,True)
        stats['cases']+=1
        for key,value in got.items(): stats[key]+=value
        stats['nonparallel_comparisons']+=cert['nonparallel_comparisons']
        stats['grid_trials']+=cert['integer']+1
    # A nonsimple pyramid core, and a nongeneric f0=0 exposing a 2D final face.
    specials=[([[V(-1,-1,0),V(1,-1,0),V(1,1,0),V(-1,1,0),V(0,0,1)],
                [V(0,0,0),V(1,0,0),V(0,1,0)], [V(0,0,0),V(0,0,1)]],
               V(-1,-1,0),V(1,-1,0),V(0,-1,-3)),
              ([[V(0,0),V(1,0)], [V(0,0),V(1,0),V(0,1)]],
               V(0,0),V(1,0),V(0,0))]
    for parts,u,v,f in specials:
        cert=lift(parts,0,u,v,f); got=verify(parts,0,u,v,f,cert,True)
        stats['cases']+=1
        for key,value in got.items(): stats[key]+=value
        stats['nonparallel_comparisons']+=cert['nonparallel_comparisons']
        stats['grid_trials']+=cert['integer']+1
    # Deliberately force integer parameters 0,...,7 to be bad.
    parts=[ [V(0,0,0),V(1,0,0),V(0,1,0)] ]
    parts += [[V(0,0,0),V(0,-j,1)] for j in range(8)]
    u,v,f=V(0,0,0),V(1,0,0),V(0,-1,0)
    cert=lift(parts,0,u,v,f)
    need(cert['integer']==8, 'root-avoidance stress case failed')
    stress=verify(parts,0,u,v,f,cert,True)
    stress_integer=cert['integer']
    fixture=encode(dict(parts=parts,core=0,u=u,v=v,initial_normal=f,certificate=cert))
    large=[]
    for n,r in [(16,8),(32,24),(48,40)]:
        core,u,v,f=simplex(n); parts=[core]
        for _ in range(r):
            parts.append([(F(0),)*n]+[tuple(F(rng.randint(-2,2),3) for _ in range(n)) for _ in range(2)])
        cert=lift(parts,0,u,v,f); got=verify(parts,0,u,v,f,cert)
        large.append(dict(dimension=n,factors=r,component_points=got['component_points'],
                          grid_trials=cert['integer']+1,proven_trial_bound=cert['degree_sum']+1,
                          nonparallel_comparisons=cert['nonparallel_comparisons'],
                          product_tuples_not_enumerated=(n+1)*3**r,
                          full_sum_enumerated=False,edge_length=str(sum(cert['lengths']))))
    def rejects(name, action):
        try: action()
        except (ValueError,KeyError,TypeError): stats['rejected_controls']+=1; return
        raise AssertionError('accepted invalid control: '+name)
    parts,u,v,f=specials[1]; good=lift(parts,0,u,v,f)
    def corrupt(key,value):
        bad=copy.deepcopy(good); bad[key]=value; return bad
    rejects('unchanged nongeneric normal',lambda:verify(parts,0,u,v,f,corrupt('normal',V(0,0))))
    rejects('wrong total endpoint',lambda:verify(parts,0,u,v,f,corrupt('end',V(100,100))))
    rejects('negative interval',lambda:verify(parts,0,u,v,f,corrupt('lengths',[F(1),F(-1)])))
    rejects('collapsed core',lambda:lift(parts,0,u,u,f))
    rejects('empty factor',lambda:lift(parts+[[]],0,u,v,f))
    rejects('wrong core index',lambda:lift(parts,10,u,v,f))
    rejects('inexact normal',lambda:lift(parts,0,u,v,(0.0,0.0)))
    rejects('non-annihilating normal',lambda:verify(parts,0,u,v,f,corrupt('normal',V(1,1))))
    rejects('wrong projection',lambda:verify(parts,0,u,v,f,corrupt('left',[v,good['left'][1]])))
    rejects('wrong lengths',lambda:verify(parts,0,u,v,f,corrupt('lengths',[F(1),F(100)])))
    square=[V(0,0),V(1,0),V(1,1),V(0,1)]
    rejects('core diagonal',lambda:lift([square],0,V(0,0),V(1,1),V(0,0)))
    rejects('false initial supporting normal',lambda:lift([square],0,V(0,0),V(1,0),V(0,1)))
    return dict(status='PASS',seed=240913,small=stats,
                root_grid_stress=dict(selected_integer=stress_integer,
                                     rejected_integers=list(range(8)),**stress),
                large=large,fixture=fixture,
                scope='Exact rational finite-instance checks; not local Lean compilation, Lean-extracted code, an original-H decomposition recognizer, or a uniform Hirsch bound.')


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path); ap.add_argument('--fixture',type=Path)
    ap.add_argument('--verify',type=Path)
    args=ap.parse_args()
    if args.verify:
        raw=json.loads(args.verify.read_text())
        def vec(xs):
            need(isinstance(xs,list) and all(isinstance(x,str) for x in xs),'rational strings required')
            return tuple(F(x) for x in xs)
        parts=[[vec(p) for p in s] for s in raw['parts']]
        cert=raw['certificate']
        for key in ['normal','start','end','lengths']:
            cert[key]=vec(cert[key])
        for key in ['left','right']:
            cert[key]=[vec(p) for p in cert[key]]
        got=verify(parts,raw['core'],vec(raw['u']),vec(raw['v']),vec(raw['initial_normal']),cert)
        print(json.dumps(dict(status='PASS',mode='independent JSON certificate readback',**got),indent=2))
        return
    result=run(); fixture=result.pop('fixture')
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    text=json.dumps(result,indent=2)+'\n'
    if args.out:
        args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(text)
    if args.fixture:
        args.fixture.parent.mkdir(parents=True,exist_ok=True)
        args.fixture.write_text(json.dumps(fixture,indent=2)+'\n')
    print(text,end='')

if __name__=='__main__': main()
