#!/usr/bin/env python3
"""Lift a supplied ordinary-edge route of an implicit H-polytope through a
finite Minkowski refinement. No base vertex/direction enumeration is used.

Input fields: A,b,base_route,summands,source_weights,target_weights. The last two
are nonnegative multipliers of ORIGINAL rows exposing the endpoint base
vertices; their positively weighted rows must have full rank. They specify the
actual refined endpoints by unique maximization in every explicit summand.

The constructor keeps the base route, chooses supporting objectives on its
edges, and crosses the explicit summands' comparison walls inside the base
vertex cones. If the base route has L edges and the added direction dictionary
has q lines, the result has at most L+(L+1)q ORDINARY edges. Every support slice,
not just every endpoint difference, is checked by the independent verifier.
This is polynomial in the supplied explicit route and rational input; finding
a short route in an arbitrary implicit base polytope is not solved here.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from typing import Any


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def rat(x: Any) -> Q:
    require(type(x) in (int, str) or isinstance(x, Q), 'exact rational strings/integers required')
    return Q(x)


def serial(x):
    if isinstance(x, Q): return str(x)
    if isinstance(x, dict): return {str(k): serial(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)): return [serial(v) for v in x]
    return x


def dot(a, b):
    require(len(a) == len(b), 'dot-product shape')
    return sum((x*y for x, y in zip(a, b) if x and y), Q(0))


def add(a, b): return tuple(x+y for x, y in zip(a, b))
def sub(a, b): return tuple(x-y for x, y in zip(a, b))
def scale(t, x): return tuple(t*a for a in x)
def interp(a, b, t): return add(scale(1-t, a), scale(t, b))


@lru_cache(maxsize=8192)
def rank(rows):
    a = [list(row) for row in rows]
    if not a: return 0
    k = 0
    for j in range(len(a[0])):
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None: continue
        a[k], a[p] = a[p], a[k]
        v = a[k][j]; a[k] = [x/v for x in a[k]]
        for i in range(k+1, len(a)):
            v = a[i][j]
            if v: a[i] = [x-v*y for x, y in zip(a[i], a[k])]
        k += 1
        if k == len(a): break
    return k


def line(v):
    if not any(v): return None
    denominator = lcm(*(x.denominator for x in v))
    z = [int(x*denominator) for x in v]
    common = gcd(*z); z = [x//common for x in z]
    if next(x for x in z if x) < 0: z = [-x for x in z]
    return tuple(z)


class Model:
    def __init__(self, data):
        self.A = tuple(tuple(map(rat, a)) for a in data['A'])
        self.b = tuple(map(rat, data['b']))
        require(self.A and self.A[0], 'nonempty positive-dimensional H-input')
        self.d = len(self.A[0]); self.m = len(self.A)
        require(len(self.b) == self.m and all(len(a) == self.d for a in self.A), 'H-row shape')
        self.path = tuple(tuple(map(rat, v)) for v in data['base_route'])
        require(self.path and all(len(v) == self.d for v in self.path), 'base-route shape')
        require(len(set(self.path)) == len(self.path), 'base route must have no repeated vertex')
        self.L = len(self.path)-1
        self.active = []
        self.base_row_checks = 0
        for v in self.path:
            evaluations = [dot(a, v) for a in self.A]; self.base_row_checks += self.m
            require(all(x <= b for x, b in zip(evaluations, self.b)), 'infeasible base vertex')
            active = frozenset(i for i, (x, b) in enumerate(zip(evaluations, self.b)) if x == b)
            require(rank(tuple(self.A[i] for i in sorted(active))) == self.d, 'base point is not a vertex')
            self.active.append(active)
        self.edge_rows = []
        for j, (u, v) in enumerate(zip(self.path, self.path[1:])):
            common = sorted(self.active[j] & self.active[j+1]); g = sub(v, u)
            require(rank(tuple(self.A[i] for i in common)) == self.d-1, 'supplied base segment is not an edge')
            require(any(dot(self.A[i], g) < 0 for i in self.active[j]), 'missing initial endpoint blocker')
            require(any(dot(self.A[i], g) > 0 for i in self.active[j+1]), 'missing final endpoint blocker')
            self.edge_rows.append(common)
        self.summands = []
        for block in data['summands']:
            pts = tuple(sorted(set(tuple(map(rat, v)) for v in block)))
            require(pts and all(len(v) == self.d for v in pts), 'empty/wrong-dimensional summand')
            self.summands.append(pts)
        self.directions = tuple(sorted({g for block in self.summands for u,v in combinations(block,2)
                                        if (g := line(sub(v,u))) is not None}))
        self.q = len(self.directions)
        self.source_weights = self.parse_weights(data['source_weights'], self.active[0], self.d)
        self.target_weights = self.parse_weights(data['target_weights'], self.active[-1], self.d)
        self.source = self.normal(self.source_weights); self.target = self.normal(self.target_weights)
        self.start_choices = self.unique(self.source); self.end_choices = self.unique(self.target)
        self.start = add(self.path[0], self.sum_point(self.start_choices))
        self.end = add(self.path[-1], self.sum_point(self.end_choices))
        canonical = {'A':self.A,'b':self.b,'base_route':self.path,'summands':self.summands,
                     'source_weights':self.source_weights,'target_weights':self.target_weights}
        self.digest = hashlib.sha256(json.dumps(serial(canonical),sort_keys=True,separators=(',',':')).encode()).hexdigest()

    def parse_weights(self, raw, allowed, expected_rank):
        weights = tuple(map(rat, raw))
        require(len(weights) == self.m and all(w >= 0 for w in weights), 'invalid support multipliers')
        support = [i for i,w in enumerate(weights) if w]
        require(set(support) <= set(allowed), 'positive multiplier on a nontight original row')
        require(rank(tuple(self.A[i] for i in support)) == expected_rank, 'support multipliers have wrong rank')
        return weights

    def normal(self, weights):
        return tuple(sum((w*a[j] for w,a in zip(weights,self.A) if w and a[j]),Q(0)) for j in range(self.d))

    def maxima(self, c):
        out=[]
        for block in self.summands:
            values=[dot(c,v) for v in block]; maximum=max(values)
            out.append(tuple(i for i,x in enumerate(values) if x == maximum))
        return tuple(out)

    def unique(self, c):
        tops=self.maxima(c)
        require(all(len(t)==1 for t in tops), 'objective does not specify a unique refined vertex')
        return tuple(t[0] for t in tops)

    def sum_point(self, choices):
        require(len(choices)==len(self.summands),'summand choice count')
        out=(Q(0),)*self.d
        for block,j in zip(self.summands,choices):
            require(type(j)is int and 0<=j<len(block),'invalid summand choice')
            out=add(out,block[j])
        return out

    def crossings(self, a, b):
        events=[]
        for j,g in enumerate(self.directions):
            x,y=dot(a,g),dot(b,g)
            if x*y<0: events.append((x/(x-y),j))
        events.sort()
        require(len(set(t for t,_ in events))==len(events),'simultaneous nonparallel wall events')
        return events


def endpoint_normal(P, weights, allowed, other=None):
    original=P.normal(weights); wanted=P.unique(original); ids=sorted(allowed)
    bounds=[Q(2)]
    for g in P.directions:
        v=dot(original,g)
        if v: bounds.append(4*sum(abs(dot(P.A[i],g)) for i in ids)/abs(v))
    base=int(max(bounds))+2
    count=len(ids)*(P.q+(P.q*(P.q-1)//2 if other is not None else 0))+1
    for attempt in range(1,count+1):
        z=Q(1,base+attempt); candidate=list(weights)
        for power,i in enumerate(ids,1): candidate[i]+=z**power
        c=P.normal(candidate)
        if any(dot(c,g)==0 for g in P.directions): continue
        if P.unique(c)!=wanted: continue
        try:
            if other is not None: P.crossings(c,other)
        except ValueError: continue
        return {'weights':candidate,'normal':c,'trials':attempt,'trial_bound':count}
    raise AssertionError('finite endpoint genericization bound exhausted')


def edge_normal(P, j, previous, target=None):
    ids=P.edge_rows[j]; edge=line(sub(P.path[j+1],P.path[j]))
    comparisons=P.q+(1+int(target is not None))*P.q*(P.q-1)//2
    limit=len(ids)*comparisons+1
    for attempt in range(1,limit+1):
        z=Q(1,attempt+2); weights=[Q(0)]*P.m
        for power,i in enumerate(ids,1): weights[i]=1+z**power
        c=P.normal(weights)
        if any(dot(c,g)==0 and g!=edge for g in P.directions): continue
        try:
            P.crossings(previous,c)
            if target is not None: P.crossings(c,target)
        except ValueError: continue
        return {'weights':weights,'normal':c,'trials':attempt,'trial_bound':limit}
    raise AssertionError('finite edge genericization bound exhausted')


def build(data):
    P=Model(data)
    if P.d==1:
        # With one variable, the two specified extrema are either equal or
        # the two ends of the sum interval; no objective-space detour is needed.
        cert={'input_sha256':P.digest,'kind':'one_dimensional','route':[P.start] if P.start==P.end else [P.start,P.end]}
        return {'certificate':serial(cert),'verified':verify(data,serial(cert))}
    final=endpoint_normal(P,P.target_weights,P.active[-1])
    first=endpoint_normal(P,P.source_weights,P.active[0],final['normal'] if not P.L else None)
    nodes=[first]
    for j in range(P.L):
        nodes.append(edge_normal(P,j,nodes[-1]['normal'],final['normal'] if j==P.L-1 else None))
    nodes.append(final)
    cert={'input_sha256':P.digest,'kind':'normal_itinerary','objectives':nodes}
    generated=trace(P,nodes)
    cert.update({'events':generated['events'],'route':generated['route'],
                 'added_direction_count':P.q,'base_edge_count':P.L,'budget':P.L+(P.L+1)*P.q})
    cert=serial(cert)
    return {'certificate':cert,'verified':verify(data,cert)}


def trace(P, nodes):
    """Reconstruct the actual finite itinerary and support witnesses. Used by
    verification too, but never searches for normals or relies on a vertex graph.
    """
    normals=[tuple(map(rat,n['normal'])) for n in nodes]
    cells=[]; events_between=[]; interior_total=0
    for j,(a,b) in enumerate(zip(normals,normals[1:])):
        events=P.crossings(a,b); interior_total+=len(events)
        times=[Q(0)]+[t for t,_ in events]+[Q(1)]
        for k,(s,t) in enumerate(zip(times,times[1:])):
            c=interp(a,b,(s+t)/2); choices=P.unique(c); p=add(P.path[j],P.sum_point(choices))
            if cells:
                if k==0:
                    events_between.append({'kind':'base','leg':j,'t':Q(0),'normal':a,
                        'weights':nodes[j]['weights']})
                else:
                    time,direction=events[k-1]
                    weights=interp(tuple(map(rat,nodes[j]['weights'])),tuple(map(rat,nodes[j+1]['weights'])),time)
                    events_between.append({'kind':'wall','leg':j,'t':time,'direction':direction,
                        'normal':interp(a,b,time),'weights':weights})
            cells.append({'base':j,'choices':choices,'point':p,'normal':c})
    route=[cells[0]['point']]; retained=[]; support_checks=0; expanded_edges=0
    for before,after,event in zip(cells,cells[1:],events_between):
        normal=tuple(map(rat,event['normal'])); left=P.path[before['base']]; right=P.path[after['base']]
        expected_rank=P.d if left==right else P.d-1
        tight=[i for i,(a,b) in enumerate(zip(P.A,P.b)) if dot(a,left)==b==dot(a,right)]
        weights=P.parse_weights(event['weights'],tight,expected_rank)
        require(P.normal(weights)==normal,'support functional not tied to original H-rows')
        tops=P.maxima(normal); deltas=[sub(right,left)] if left!=right else []
        for block,maximum,x,y in zip(P.summands,tops,before['choices'],after['choices']):
            require(x in maximum and y in maximum,'adjacent summand choices not exposed at event')
            support_checks+=len(block)
            u,v=block[x],block[y]
            if u==v:
                require(len(maximum)==1,'hidden positive-dimensional summand face')
                continue
            delta=sub(v,u); coordinate=next(i for i,t in enumerate(delta) if t)
            for k in maximum:
                value=(block[k][coordinate]-u[coordinate])/delta[coordinate]
                require(0<=value<=1 and block[k]==add(u,scale(value,delta)), 'exposed summand face is not the asserted interval')
            deltas.append(delta)
        if before['point']==after['point']:
            require(not deltas,'nontrivial exposed changes cancel')
            continue
        require(deltas,'nontrivial route without a changing support face')
        direction=line(deltas[0]); comparison=sub(after['normal'],before['normal'])
        require(all(line(g)==direction and dot(comparison,g)>0 for g in deltas), 'exposed sum is not one consistently oriented segment')
        total=sub(after['point'],before['point'])
        require(line(total)==direction,'total edge direction inconsistent')
        if event['kind']=='base' and len(deltas)>1: expanded_edges+=1
        route.append(after['point'])
        retained.append({'kind':event['kind'],'leg':event['leg'],'t':event['t'],
                         'before_choices':before['choices'],'after_choices':after['choices']})
    require(route[0]==P.start and route[-1]==P.end,'refined requested endpoints changed')
    require(sum(e['kind']=='base' for e in retained)==P.L,'base edge disappeared or was counted twice')
    require(len(route)-1<=P.L+interior_total<=P.L+(P.L+1)*P.q,'lifted event budget failed')
    return {'route':route,'events':retained,'added_comparison_events':interior_total,
            'explicit_support_point_checks':support_checks,'expanded_parallel_base_edges':expanded_edges}


def verify(data, cert):
    """Does not invoke build(), normal search, support optimization over P,
    full vertex enumeration, or a claimed adjacency oracle for the sum.
    """
    P=Model(data)
    require(cert['input_sha256']==P.digest,'problem identity or endpoint data changed')
    if P.d==1:
        require(cert['kind']=='one_dimensional','wrong one-dimensional kind')
        route=[P.start] if P.start==P.end else [P.start,P.end]
        require([tuple(map(rat,v)) for v in cert['route']]==route,'invalid interval route')
        return {'status':'PASS','dimension':1,'base_edges':P.L,'added_directions':P.q,
                'ordinary_edges':len(route)-1,'bound':P.L+(P.L+1)*P.q,
                'scope':'Exact interval endpoint/support check; not a Lean verdict.'}
    require(cert['kind']=='normal_itinerary','unknown certificate kind')
    nodes=cert['objectives']; require(len(nodes)==P.L+2,'incomplete normal itinerary')
    for j,node in enumerate(nodes):
        if j==0: allowed=P.active[0]; desired=P.d
        elif j==len(nodes)-1: allowed=P.active[-1];desired=P.d
        else: allowed=P.edge_rows[j-1];desired=P.d-1
        weights=P.parse_weights(node['weights'],allowed,desired);c=tuple(map(rat,node['normal']))
        require(len(c)==P.d and P.normal(weights)==c,'forged support normal')
        if j in (0,len(nodes)-1):
            require(all(dot(c,g) for g in P.directions),'nongeneric endpoint comparison')
            require(P.unique(c)==(P.start_choices if j==0 else P.end_choices),'endpoint perturbation changes the refined vertex')
        else:
            edge=line(sub(P.path[j],P.path[j-1]))
            require(all(dot(c,g) or g==edge for g in P.directions),'uncontrolled nonparallel event at base-edge normal')
    got=trace(P,nodes)
    require([tuple(map(rat,v)) for v in cert['route']]==got['route'],'forged output coordinates')
    require(cert['events']==serial(got['events']),'omitted/reordered/forged edge events')
    for key,value in [('added_direction_count',P.q),('base_edge_count',P.L),('budget',P.L+(P.L+1)*P.q)]:
        require(type(cert[key])is int and cert[key]==value,'forged '+key)
    return {'status':'PASS','dimension':P.d,'base_rows':P.m,'base_edges':P.L,
            'added_summands':len(P.summands),'listed_summand_points':sum(map(len,P.summands)),
            'added_directions':P.q,'ordinary_edges':len(got['route'])-1,'bound':cert['budget'],
            'added_comparison_events':got['added_comparison_events'],
            'explicit_support_point_checks':got['explicit_support_point_checks'],
            'base_feasibility_row_checks':P.base_row_checks,
            'expanded_parallel_base_edges':got['expanded_parallel_base_edges'],
            'scope':'Exact exposed ORIGINAL-H base faces and Minkowski edge certificates. Base route supplied, not inferred from a diameter oracle.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--certificate',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    try:
        data=json.loads(args.input.read_text())
        out=verify(data,json.loads(args.certificate.read_text())) if args.certificate else build(data)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:p.exit(2,f'No certificate: {e}\n')
if __name__=='__main__':main()
