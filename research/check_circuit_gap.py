#!/usr/bin/env python3
"""Exact 2-D counterexamples to dimension-only circuit-to-edge overhead.
No Lean verification or polynomial-Hirsch counterexample is claimed.
"""
from fractions import Fraction as F
from itertools import combinations
from collections import deque
from pathlib import Path
import json


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))


def example(k):
    r=F(2*k+1,2)
    top=[(-r+j, r*r-(-r+j)**2) for j in range(2*k+2)]
    vertices=top+[(x,-y) for x,y in reversed(top[1:-1])]
    rows=[]
    for p,q in zip(vertices, vertices[1:]+vertices[:1]):
        dx,dy=q[0]-p[0],q[1]-p[1]
        normal=(-dy,dx)
        rows.append((normal,dot(normal,p)))
    assert all(b>0 for a,b in rows)
    found=set()
    for (a,b),(c,e) in combinations(rows,2):
        det=a[0]*c[1]-a[1]*c[0]
        if not det:
            continue
        x=((b*c[1]-a[1]*e)/det,(a[0]*e-b*c[0])/det)
        if all(dot(v,x)<=bound for v,bound in rows):
            found.add(x)
    assert found==set(vertices)
    active=[{i for i,(a,b) in enumerate(rows) if dot(a,x)==b} for x in vertices]
    graph=[[] for _ in vertices]
    for i,j in combinations(range(len(vertices)),2):
        if active[i]&active[j]:
            graph[i].append(j);graph[j].append(i)
    assert all(len(neighbors)==2 for neighbors in graph)
    witnesses=[]
    for i,(a,b) in enumerate(rows):
        ends=[vertices[j] for j,S in enumerate(active) if i in S]
        assert len(ends)==2
        p=tuple((x+y)/2 for x,y in zip(*ends))
        limits=[(bj-dot(aj,p))/(1+abs(dot(aj,a))) for j,(aj,bj) in enumerate(rows) if j!=i]
        assert all(t>0 for t in limits)
        t=min(limits)/2
        z=tuple(x+t*y for x,y in zip(p,a))
        assert dot(a,z)>b
        assert all(dot(aj,z)<=bj for j,(aj,bj) in enumerate(rows) if j!=i)
        witnesses.append([str(x) for x in z])
    u,v=top[0],top[-1]
    g=tuple(y-x for x,y in zip(u,v))
    killed=[i for i,(a,b) in enumerate(rows) if dot(a,g)==0]
    assert killed and all(rows[i][0][0]==0 and rows[i][0][1]!=0 for i in killed)
    # Any nonzero direction with row support inside supp(A g) must have h_y=0,
    # so it is proportional to g and has exactly the same row support.
    assert g[0]!=0 and g[1]==0
    blocking=[i for i,(a,b) in enumerate(rows) if dot(a,v)==b and dot(a,g)>0]
    assert blocking
    assert not (active[0]&active[len(top)-1])
    dist={0:0};queue=deque([0])
    while queue:
        i=queue.popleft()
        for j in graph[i]:
            if j not in dist:dist[j]=dist[i]+1;queue.append(j)
    distance=dist[len(top)-1]
    assert distance==2*k+1==len(rows)//2
    return {'k':k,'rows':len(rows),'dimension':2,'vertices':len(found),
            'circuit_steps':1,'graph_distance':distance,'strict_center':['0','0'],
            'u':[str(x) for x in u],'v':[str(x) for x in v],
            'horizontal_facet_rows':killed,'maximality_blocking_rows':blocking,
            'irredundancy_witnesses':witnesses}

if __name__=='__main__':
    report={'status':'exact rational diagnostics, not Lean proofs',
            'conclusion':'No overhead depending only on dimension can refine all circuit steps. This does not rule out polynomial row-count overhead.',
            'examples':[example(k) for k in [1,2,4,8,16]]}
    target=Path(__file__).with_name('circuit_gap_certificates.json')
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps([{k:v for k,v in e.items() if k!='irredundancy_witnesses'} for e in report['examples']],indent=2))
