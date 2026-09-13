#!/usr/bin/env python3
"""Exact ordinary-edge sweeps of explicitly supplied finite Minkowski sums.

The input defines P=sum_s conv(vertices[s]); no global vertex enumeration,
external optimizer or approximate arithmetic is used. Source and target
objectives must select unique vertices in every summand (duplicate points are
removed). A deterministic rational perturbation breaks comparison-wall ties
without changing those endpoints. The independent verifier proves each move
exposes a segment of P, not merely a circuit or a line between feasible points.

The size bound is the number of distinct pair-difference directions in this
Minkowski representation, NOT an unconditional bound in the H-facet count.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from itertools import combinations
from math import gcd, lcm
import hashlib
import json
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int, str) or isinstance(x, Q), 'use integers or rational strings, not floats/bools')
    return Q(x)


def dot(a, b):
    require(len(a) == len(b), 'dot-product dimension mismatch')
    return sum((x*y for x, y in zip(a, b) if x and y), Q(0))


def add(a, b): return tuple(x+y for x,y in zip(a,b))
def sub(a, b): return tuple(x-y for x,y in zip(a,b))
def scale(t, a): return tuple(t*x for x in a)
def sign(t): return int(t>0)-int(t<0)


def line(v):
    """Canonical UNORIENTED rational line; collinear duplicate walls merge."""
    if not any(v):
        return None
    den = lcm(*(x.denominator for x in v))
    nums = [int(x*den) for x in v]
    div = gcd(*nums)
    nums = [x//div for x in nums]
    if next(x for x in nums if x) < 0:
        nums = [-x for x in nums]
    return tuple(nums)


def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x, (list,tuple)): return [serial(v) for v in x]
    return x


class MinkowskiInput:
    def __init__(self, data: dict[str, Any]):
        require(isinstance(data,dict), 'input must be an object')
        d = data['dimension']
        require(type(d) is int and d>0, 'positive integer dimension required')
        self.d = d
        raw = data['summands']
        require(isinstance(raw,list) and raw, 'nonempty summand list required')
        self.summands=[]
        for block in raw:
            require(isinstance(block,list) and block, 'each summand needs a nonempty vertex list')
            pts = [tuple(rat(x) for x in v) for v in block]
            require(all(len(v)==d for v in pts), 'vertex shape mismatch')
            self.summands.append(tuple(sorted(set(pts))))
        self.source = tuple(rat(x) for x in data['source_objective'])
        self.target = tuple(rat(x) for x in data['target_objective'])
        require(len(self.source)==d and len(self.target)==d, 'objective shape mismatch')
        self.directions=tuple(sorted({g for block in self.summands for u,v in combinations(block,2)
                                     if (g:=line(sub(v,u))) is not None}))
        self.start_choices=self.unique_choices(self.source)
        self.end_choices=self.unique_choices(self.target)
        self.start=self.point(self.start_choices)
        self.end=self.point(self.end_choices)
        self.digest=hashlib.sha256(json.dumps(serial({
            'dimension':d,'summands':self.summands,
            'source_objective':self.source,'target_objective':self.target}),
            sort_keys=True,separators=(',',':')).encode()).hexdigest()

    def maxima(self, normal):
        out=[]
        for block in self.summands:
            values=[dot(v,normal) for v in block]
            best=max(values)
            out.append(tuple(i for i,v in enumerate(values) if v==best))
        return tuple(out)

    def unique_choices(self, normal):
        tops=self.maxima(normal)
        require(all(len(t)==1 for t in tops), 'objective does not expose a unique summand vertex')
        return tuple(t[0] for t in tops)

    def point(self, choices):
        require(len(choices)==len(self.summands), 'choice list length mismatch')
        out=[Q(0)]*self.d
        for block,j in zip(self.summands,choices):
            require(type(j) is int and 0<=j<len(block), 'invalid summand choice')
            for k,x in enumerate(block[j]): out[k]+=x
        return tuple(out)


def genericize(P: MinkowskiInput, original, final=None):
    """Finite moment-curve search, preserving all initially strict comparisons.

Each bad equality is a nonzero polynomial of degree <=d in z. With final
supplied, at most binom(q,2) more polynomials forbid simultaneous crossings.
The search limit follows from root counting; it is not a floating tolerance.
    """
    values=[dot(g,original) for g in P.directions]
    ratios=[sum(abs(x) for x in g)/abs(v) for g,v in zip(P.directions,values) if v]
    bound=max(rat(1),4*max(rat(1),max(ratios,default=rat(1))))
    base=bound.numerator//bound.denominator+2
    q=len(P.directions)
    limit=P.d*(q+(q*(q-1)//2 if final is not None else 0))+1
    fv=None if final is None else [dot(g,final) for g in P.directions]
    if fv is not None: require(all(fv), 'final objective must already avoid every wall')
    wanted=P.unique_choices(original)
    for trial in range(1,limit+1):
        z=Q(1,base+trial)
        c=add(original,tuple(z**(i+1) for i in range(P.d)))
        cv=[dot(g,c) for g in P.directions]
        if not all(cv): continue
        if any(v and sign(v)!=sign(w) for v,w in zip(values,cv)): continue
        if final is not None:
            times=[a/(a-b) for a,b in zip(cv,fv) if a*b<0]
            if len(times)!=len(set(times)): continue
        require(P.unique_choices(c)==wanted,'endpoint changed during perturbation')
        return c,{'trials':trial,'root_count_limit':limit,'z':z}
    raise AssertionError('proved rational genericization bound exhausted')


def wall_events(P, source, target):
    events=[]
    for i,g in enumerate(P.directions):
        a=dot(g,source);b=dot(g,target)
        require(a and b, 'sweep endpoint on a comparison wall')
        if a*b<0:
            t=a/(a-b)
            require(0<t<1, 'crossing parameter outside interval')
            events.append((t,i))
    events.sort()
    require(len({t for t,_ in events})==len(events), 'simultaneous NONPARALLEL wall crossings')
    return events


def sweep(data):
    P=MinkowskiInput(data)
    target,tr=genericize(P,P.target)
    source,sr=genericize(P,P.source,target)
    events=wall_events(P,source,target)
    boundaries=[Q(0)]+[t for t,_ in events]+[Q(1)]
    choices=[P.unique_choices(add(scale(1-t,source),scale(t,target)))
             for t in ((a+b)/2 for a,b in zip(boundaries,boundaries[1:]))]
    route=[P.point(choices[0])]
    steps=[]
    for j,(t,i) in enumerate(events):
        if choices[j]==choices[j+1]: continue
        point=P.point(choices[j+1])
        require(point!=route[-1], 'nontrivial support switch cancelled in Minkowski sum')
        steps.append({'event':j,'direction':i,'parameter':t,
                      'before_choices':choices[j],'after_choices':choices[j+1]})
        route.append(point)
    cert={'input_sha256':P.digest,'source_used':source,'target_used':target,
          'events':[{'parameter':t,'direction':i} for t,i in events],
          'steps':steps,'route':route,'direction_count':len(P.directions),
          'source_perturbation':sr,'target_perturbation':tr}
    return {'certificate':serial(cert),'verified':verify(data,serial(cert))}


def verify(data,cert):
    """Recompute all comparisons and exposed segments; never calls sweep()."""
    P=MinkowskiInput(data)
    require(isinstance(cert,dict) and cert['input_sha256']==P.digest, 'input identity mismatch')
    source=tuple(rat(x) for x in cert['source_used'])
    target=tuple(rat(x) for x in cert['target_used'])
    require(len(source)==P.d and len(target)==P.d,'used objective shape')
    require(P.unique_choices(source)==P.start_choices,'source objective changes the requested vertex')
    require(P.unique_choices(target)==P.end_choices,'target objective changes the requested vertex')
    require(type(cert['direction_count']) is int and cert['direction_count']==len(P.directions),
            'false direction count')
    events=wall_events(P,source,target)
    parsed=[]
    for ev in cert['events']:
        require(type(ev['direction']) is int, 'invalid event direction')
        parsed.append((rat(ev['parameter']),ev['direction']))
    require(parsed==events,'missing, reordered or forged wall event')
    boundaries=[Q(0)]+[t for t,_ in events]+[Q(1)]
    choices=[]
    for a,b in zip(boundaries,boundaries[1:]):
        t=(a+b)/2
        choices.append(P.unique_choices(add(scale(1-t,source),scale(t,target))))
    expected_route=[P.point(choices[0])];expected_steps=[]
    support_comparisons=0;exposed_segment_checks=0
    for j,(t,k) in enumerate(events):
        normal=add(scale(1-t,source),scale(t,target))
        maxima=P.maxima(normal)
        support_comparisons+=sum(len(b) for b in P.summands)
        before,after=choices[j],choices[j+1]
        has_change=before!=after
        for block,top,left,right in zip(P.summands,maxima,before,after):
            require(left in top and right in top,'neighboring exposed vertex not maximal on event wall')
            if left==right:
                require(len(top)==1,'hidden nontrivial exposed summand face')
                continue
            g=P.directions[k];coord=next(i for i,x in enumerate(g) if x)
            a=block[left];b=block[right];delta=sub(b,a)
            require(line(delta)==g,'summand changes in a different direction')
            length=delta[coord]
            require(length,'zero exposed segment')
            for index in top:
                v=block[index];theta=(v[coord]-a[coord])/length
                require(0<=theta<=1 and v==add(a,scale(theta,delta)),
                        'exposed summand face is not the certified segment')
            require(dot(sub(target,source),delta)>0,'support switches point in inconsistent orientations')
            exposed_segment_checks+=1
        if has_change:
            a=P.point(before);b=P.point(after)
            require(a!=b and line(sub(b,a))==P.directions[k], 'total exposed face is not a nonzero segment')
            require(dot(target,sub(b,a))>0 and dot(P.target,sub(b,a))>=0,
                    'edge fails target-objective monotonicity')
            # All other walls are nonzero, all maximizing summand differences
            # are parallel, and endpoints are the extremal choices. Hence the
            # exposed Minkowski face is EXACTLY [a,b], an ordinary edge.
            expected_steps.append((j,k,t,before,after))
            expected_route.append(b)
    actual_steps=[]
    for s in cert['steps']:
        require(type(s['event']) is int and type(s['direction']) is int, 'step indices must be integers')
        before=tuple(s['before_choices']);after=tuple(s['after_choices'])
        require(all(type(i) is int for i in before+after),'choice labels must be integers')
        actual_steps.append((s['event'],s['direction'],rat(s['parameter']),before,after))
    require(actual_steps==expected_steps,'incorrect exposed-edge sequence')
    route=[tuple(rat(x) for x in v) for v in cert['route']]
    require(route==expected_route,'forged route coordinates')
    require(route[0]==P.start and route[-1]==P.end,'changed requested endpoints')
    require(len(route)-1<=len(events)<=len(P.directions),'wall-count budget failed')
    result={'status':'PASS','ambient_dimension':P.d,'summands':len(P.summands),
            'listed_summand_points':sum(map(len,P.summands)),
            'distinct_directions':len(P.directions),'comparison_events':len(events),
            'ordinary_edges':len(route)-1,'vertices_constructed':len(route),
            'exposed_summand_segments':exposed_segment_checks,
            'support_comparisons':support_comparisons,
            'scope':'Exact rational exposed-face checks on the supplied Minkowski sum; not Lean/platform acceptance.'}
    # For genuine segment summands, every separating generator line changes
    # one tope bit and every step changes exactly one line: equality is optimal.
    is_zonotope=all(len(block)<=2 for block in P.summands)
    if is_zonotope:
        require(len(expected_steps)==len(events),'zonotope failed exact sign-distance identity')
        result['zonotope_shortest_distance']=len(events)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path);parser.add_argument('--certificate',type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    try:
        data=json.loads(args.input.read_text())
        result=verify(data,json.loads(args.certificate.read_text())) if args.certificate else sweep(data)
        text=json.dumps(serial(result),indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:
        parser.exit(2,f'Certificate rejected: {exc}\n')

if __name__=='__main__': main()
