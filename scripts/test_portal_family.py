#!/usr/bin/env python3
"""Exact infinite-family regression: metric-shortest facet paths cost 6+2k,
while the true distance and a one-extra-region-edge route remain exactly five.
The infinite proof is in the research note; these tests do not replace it.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
from portal_debt_router import Model,dot,rank,distances,jsonable,require


def cut_vertex(A,b,bal,verts,x):
    d=len(x);active=[i for i,(a,t) in enumerate(zip(A,b)) if dot(a,x)==t]
    require(len(active)==d,'cut must isolate a simple vertex')
    normal=[sum((A[i][j] for i in active),Q(0)) for j in range(d)]
    top=dot(normal,x);runner=max(dot(normal,y) for y in verts if y!=x)
    require(runner<top,'supporting normal does not isolate the vertex')
    bound=(top+runner)/2;out=[y for y in verts if y!=x]
    for y in verts:
        if y==x:continue
        ay={i for i,(a,t) in enumerate(zip(A,b)) if dot(a,y)==t}
        if len(set(active)&ay)==d-1:
            t=(top-bound)/(top-dot(normal,y))
            require(0<t<1,'bad cut parameter')
            out.append(tuple((1-t)*xx+t*yy for xx,yy in zip(x,y)))
    eps=min(bal[i] for i in active)/2
    for i in active:bal[i]-=eps
    bal.append(eps);A.append(normal);b.append(bound)
    require(len(out)==len(verts)+d-1,'simple vertex truncation count')
    return sorted(out)


def family(base,k):
    m=Model(base);A=[row[:] for row in m.A];b=m.b[:]
    bal=[Q(x) for x in base['positive_balance']];verts=m.vertices[:]
    for _ in range(k):
        endpoints=sorted(x for x in verts if x[1]==0 and x[2]==0)
        require(len(endpoints)==2,'shared ridge is not an edge')
        # Truncate both endpoints once; their replacements remain distinct.
        for x in endpoints:verts=cut_vertex(A,b,bal,verts,x)
    interior=[sum((v[j] for v in verts),Q(0))/len(verts) for j in range(3)]
    return {'A':A,'b':b,'positive_balance':bal,'interior':interior}


def audit_instance(base,k):
    data=family(base,k);m=Model(data)
    uc=(Q(1,8),Q(0),Q(3,4));vc=(Q(1,4),Q(1,2),Q(0))
    u=m.vertices.index(uc);v=m.vertices.index(vc)
    _,pts,facets=m.face(u,v);regions,g,ds,dt=m.regions(u,v)
    require(ds[-2]==3,'two-facet geodesic disappeared')
    facetpairs=[(a,b) for a in m.active[u] for b in m.active[v] if facets[a]&facets[b]]
    require(facetpairs==[(1,2)],'unexpected alternative shortest facet pair')
    ga={x:m.graph[x]&facets[1] for x in facets[1]};gb={x:m.graph[x]&facets[2] for x in facets[2]}
    da=distances(ga,u);db=distances(gb,v);costs=[]
    for z in sorted(facets[1]&facets[2]):
        require(da[z]==3+k and db[z]==3+k,'polygonal endpoint distance formula')
        costs.append({'portal':z,'left':da[z],'right':db[z]})
    require(distances(m.graph,u)[v]==5,'ambient distance is not five')
    route=m.route(u,v,'relaxed');geo=m.route(u,v,'recursive')
    require(route['length']==5 and route['facet_slack']==1,'one-extra-edge route failed')
    require(geo['length']==6+2*k and geo['local_debt']==1 and geo['debt']==3+2*k,'strict geodesic/debt formula')
    require(m.n==10+2*k and len(m.vertices)==16+4*k,'family size formula')
    result={'k':k,'facets':m.n,'vertices':len(m.vertices),'graph_distance':5,
            'optimal_geodesic_repair':geo['length'],'one_extra_region_edge_route':route['length'],
            'root_debt':geo['local_debt'],'total_geodesic_debt':geo['debt'],
            'geodesic_portals':costs}
    return result,{'input':data,'vertices':m.vertices,'u':u,'v':v,
                   'comparison':result,'geodesic':geo,'relaxed':route}


def main():
    root=Path(__file__).resolve().parents[1]
    base=json.loads((root/'fixtures/portal_debt_barrier_input.json').read_text())['input']
    rows=[]
    for k in (0,1,2,4,8,12,20):
        result,packet=audit_instance(base,k);rows.append(result);print(json.dumps(result),flush=True)
        if k==20:(root/'fixtures/amplified_geodesic_barrier.json').write_text(json.dumps(jsonable(packet),indent=2,sort_keys=True)+'\n')
    summary={'status':'PASS','scope':'Exact rational finite regressions for the separately proved infinite family.',
             'instances':rows,'verified_full_polytope_vertex_lists':len(rows),
             'explicit_route_certificates':2*len(rows)}
    (root/'research/PORTAL_FAMILY_CHECK_2026-09-12.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n')

if __name__=='__main__':main()
