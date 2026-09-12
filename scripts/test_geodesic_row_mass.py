#!/usr/bin/env python3
"""Finite regressions plus exact rational polytope examples, not Lean verification."""
from __future__ import annotations
from collections import deque
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import random
import time
from geodesic_row_mass import audit, require, shortest_path


def dot(a, b): return sum((x*y for x, y in zip(a, b)), Q(0))

def rank(rows):
    a = [list(r) for r in rows]
    if not a: return 0
    k=0
    for j in range(len(a[0])):
        p=next((i for i in range(k,len(a)) if a[i][j]),None)
        if p is None: continue
        a[k],a[p]=a[p],a[k]; v=a[k][j]; a[k]=[x/v for x in a[k]]
        for i in range(k+1,len(a)):
            v=a[i][j]
            if v: a[i]=[x-v*y for x,y in zip(a[i],a[k])]
        k+=1
        if k==len(a): break
    return k


def solve(rows,rhs):
    n=len(rows); a=[list(r)+[b] for r,b in zip(rows,rhs)]
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None: return None
        a[j],a[p]=a[p],a[j]; v=a[j][j]; a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j]
                if v: a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return tuple(r[-1] for r in a)


def vertices(A,b):
    d=len(A[0]); out={}
    for base in combinations(range(len(A)),d):
        x=solve([A[i] for i in base],[b[i] for i in base])
        if x is not None and all(dot(a,x)<=bi for a,bi in zip(A,b)):
            out[x]={i for i,(a,bi) in enumerate(zip(A,b)) if dot(a,x)==bi}
    return out


def affine_dim(points):
    pts=list(points)
    if not pts: return -1
    return rank([[x-y for x,y in zip(p,pts[0])] for p in pts[1:]])


def edge_graph(A,vs):
    d=len(A[0]); pts=list(vs); g=[set() for _ in pts]
    for i,x in enumerate(pts):
        for j in range(i):
            if rank([A[k] for k in vs[x]&vs[pts[j]]])==d-1:
                g[i].add(j);g[j].add(i)
    return pts,g


def stacked_truncations(n):
    A=[[Q(-1),Q(0),Q(0)],[Q(0),Q(-1),Q(0)],
       [Q(0),Q(0),Q(-1)],[Q(1),Q(1),Q(1)]]
    b=[Q(0),Q(0),Q(0),Q(1)]
    vs=vertices(A,b); chosen={1,2,3}; steps=0
    while len(A)<n:
        x=next(p for p,s in vs.items() if s==chosen)
        normal=[sum((A[j][i] for j in chosen),Q(0)) for i in range(3)]
        top=dot(normal,x); others=[p for p in vs if p!=x]
        runner=max(dot(normal,p) for p in others)
        require(runner<top,'truncation does not isolate one simple vertex')
        bound=(top+runner)/2
        neighbors=[p for p in others if len(vs[p]&chosen)==2]
        require(len(neighbors)==3,'simple vertex must have three incident edges')
        idx=len(A); new=dict(vs); del new[x]
        for y in neighbors:
            t=(top-bound)/(top-dot(normal,y))
            require(0<t<1,'edge-cut parameter out of range')
            z=tuple((1-t)*xx+t*yy for xx,yy in zip(x,y))
            new[z]=(chosen&vs[y])|{idx}
        A.append(normal);b.append(bound);vs=new
        for p,act in vs.items():
            require(all(dot(a,p)<=bi for a,bi in zip(A,b)),'generated infeasible vertex')
            actual={i for i,(a,bi) in enumerate(zip(A,b)) if dot(a,p)==bi}
            require(actual==act and rank([A[i] for i in act])==3,'active basis mismatch')
        chosen={idx-2,idx-1,idx};steps+=1
    return A,b,vs,steps


def carrier(A,b,vs,x,y):
    common=vs[x]&vs[y]
    points={p for p in vs if common<=vs[p]}
    h=affine_dim(points)
    faces=set()
    if h:
        for j in range(len(A)):
            face=frozenset(p for p in points if j in vs[p])
            if face and affine_dim(face)==h-1: faces.add(face)
    M=len(faces)
    require(2*h<=M,'separated vertex-pair carrier size failed')
    return h,M,M-h


def geometric_path(A,b,vs,target,endpoint,neighbor,available_override=None,old_override=None):
    pts=list(vs); d=len(A[0]); n=len(A)
    available=([i for i in range(n) if dot(A[i],target)<b[i]]
               if available_override is None else list(available_override))
    require(all(any(a) for a in A),'test assumes nonzero describing rows')
    s=len(available); e=n-d
    # Every cut label exists, even when its row face is empty/redundant.
    regions=[{p for p in pts if i in vs[p]} for i in available]
    old=len(regions);regions.append({target,neighbor} if old_override is None else set(old_override))
    start=len(regions);regions.append({target})
    end=len(regions);regions.append({endpoint})
    g=[set() for _ in regions]
    for i in range(len(g)):
        for j in range(i):
            if regions[i]&regions[j]: g[i].add(j);g[j].add(i)
    path=shortest_path(g,start,end)
    portals=[sorted(regions[i]&regions[j])[0] for i,j in zip(path,path[1:])]
    selected=[];deltas=[];dims=[];counts=[];direct_cost=[]
    for k,i in enumerate(path):
        if i>=s: continue
        require(0<k<len(path)-1,'cut cannot be a singleton endpoint label')
        x,y=portals[k-1],portals[k]
        h,M,delta=carrier(A,b,vs,x,y)
        selected.append(i);deltas.append(delta);dims.append(h);counts.append(M)
        facepoints={p:vs[p] for p in vs if (vs[x]&vs[y])<=vs[p]}
        fp,fg=edge_graph(A,facepoints)
        direct_cost.append(len(shortest_path(fg,fp.index(x),fp.index(y)))-1)
    data={'vertex_count':len(g),'edges':[[i,j] for i in range(len(g)) for j in sorted(g[i]) if i<j],
          'path':path,'available':list(range(s)),'selected':selected,'excess':e,'carrier_excesses':deltas}
    result=audit(data)
    require(sum(dims)<=sum(deltas) and sum(counts)<=2*sum(deltas),'intrinsic sums failed')
    for i,delta in zip(selected,deltas):
        t=sum(i==j or i in g[j] for j in range(s))
        # Independently verify that every absent row is slack throughout the carrier.
        k=path.index(i);x,y=portals[k-1],portals[k];common=vs[x]&vs[y]
        for j in range(s):
            if j!=i and i not in g[j]:
                require(all(dot(A[available[j]],p)<b[available[j]] for p in vs if common<=vs[p]),
                        'noncontact row is not strict on actual carrier')
        require(delta+s<=e+t,'geometric pointwise estimate failed')
    result.update({'ambient_dimension':d,'rows':n,'vertices':len(vs),
                   'carrier_dimensions':dims,'carrier_row_counts':counts,
                   'actual_assembled_edge_cost':1+sum(direct_cost),
                   'carrier_diameter_costs':direct_cost})
    if dims:
        H=max(dims);m=len(selected)*(e-s)+3*s
        require(1+sum(direct_cost)<=1+2*m*2**max(H-3,0),'dimension-cap route bound failed')
        result['dimension_cap_budget']=1+2*m*2**max(H-3,0)
    return data,result


def basis_star_audit(A,b,vs,target,endpoint):
    d=len(A[0]); active=sorted(vs[target])
    basis=next(ids for ids in combinations(active,d) if rank([A[i] for i in ids])==d)
    av=[i for i in range(len(A)) if i not in basis]
    require(len(av)==len(A)-d,'basis complement size')
    center=tuple(sum((x[j] for x in vs),Q(0))/len(vs) for j in range(d))
    require(all(dot(a,center)<bi for a,bi in zip(A,b)),'center is not strictly feasible')
    cap=1+max(sum((b[i]-dot(A[i],x) for i in basis),Q(0)) for x in vs)
    qverts=[target]
    for j in range(d):
        rhs=[b[i]-cap*int(k==j) for k,i in enumerate(basis)]
        y=solve([A[i] for i in basis],rhs)
        require(y is not None,'retained basis is singular')
        qverts.append(y)
    for x in vs:
        slack=[b[i]-dot(A[i],x) for i in basis]
        require(all(t>=0 for t in slack) and sum(slack)<cap,'parent outside compact star')
    for y in qverts:
        slack=[b[i]-dot(A[i],y) for i in basis]
        require(all(t>=0 for t in slack) and sum(slack)<=cap,'invalid star vertex')
    if endpoint==target:
        y=qverts[1]
    else:
        candidates=[(i,y) for i in av if i in vs[endpoint] for y in qverts[1:] if dot(A[i],y)>=b[i]]
        require(bool(candidates),'endpoint lift to star not found')
        _,y=candidates[0]
    direction=tuple(a-c for a,c in zip(y,target));j=next(j for j,v in enumerate(direction) if v)
    old=[]
    for x in vs:
        t=(x[j]-target[j])/direction[j]
        if 0<=t<=1 and all(xx==v+t*z for xx,v,z in zip(x,target,direction)): old.append(x)
    require(target in old and len(old)<=2,'old-edge region is invalid')
    if len(old)==2:
        require(rank([A[i] for i in vs[old[0]]&vs[old[1]]])==d-1,'clipped old segment not an edge')
    data,result=geometric_path(A,b,vs,target,endpoint,target,av,old)
    result.update({'basis_star':True,'target_active_rows':len(active),
                   'retained_basis':list(basis),'available_rows_tight_at_target':len(set(av)&vs[target]),
                   'old_edge_vertex_count':len(old),'cut_rank':rank([A[i] for i in av])})
    return data,result

def graph_tests():
    counts={'graphs':0,'ordered_geodesics':0,'available_vertex_windows':0,'incidence_audits':0}
    for n in range(1,6):
        all_edges=list(combinations(range(n),2))
        for mask in range(1<<len(all_edges)):
            g=[set() for _ in range(n)]
            edges=[]
            for k,(i,j) in enumerate(all_edges):
                if (mask>>k)&1: g[i].add(j);g[j].add(i);edges.append([i,j])
            counts['graphs']+=1
            for u in range(n):
                for v in range(n):
                    try: p=shortest_path(g,u,v)
                    except ValueError: continue
                    counts['ordered_geodesics']+=1
                    for z in range(n):
                        ix=[i for i,t in enumerate(p) if t==z or t in g[z]]
                        require(len(ix)<=3 and (not ix or max(ix)-min(ix)<=2),'geodesic star window')
                        counts['available_vertex_windows']+=1
                    # All available subsets on five representative endpoint choices;
                    # all path positions that are available are selected.
                    if u==0:
                        for amask in range(1<<n):
                            av=[i for i in range(n) if (amask>>i)&1]
                            sel=[i for i in p if i in av]
                            loads=[sum(i==j or i in g[j] for j in av) for i in sel]
                            audit({'vertex_count':n,'edges':edges,'path':p,'available':av,
                                   'selected':sel,'excess':len(av),'carrier_excesses':loads})
                            counts['incidence_audits']+=1
    return counts


def main():
    root=Path(__file__).resolve().parents[1];start_time=time.monotonic()
    (root/'fixtures').mkdir(exist_ok=True)
    (root/'research').mkdir(exist_ok=True)
    counts=graph_tests(); examples=[]; total_calls=0; trunc_steps=0
    for n in (8,12,18,30,48):
        A,b,vs,steps=stacked_truncations(n);trunc_steps+=steps
        if n<=12: require(vs==vertices(A,b),'independent full enumeration disagrees')
        target=(Q(0),Q(0),Q(0));pts,pg=edge_graph(A,vs)
        nbrs=pg[pts.index(target)]; neighbor=pts[min(nbrs)]
        endpoint=next(p for p,active in vs.items() if {n-3,n-2,n-1}<=active)
        data,res=geometric_path(A,b,vs,target,endpoint,neighbor)
        total_calls+=len(res['carrier_dimensions']);examples.append(res)
        if n==48:
            (root/'fixtures/stacked_48_row_incidence.json').write_text(json.dumps(data,indent=2)+'\n')
            geom={'A':[[str(x) for x in row] for row in A],'b':[str(x) for x in b],
                  'vertices':[[str(x) for x in p] for p in pts],
                  'target':[str(x) for x in target],'endpoint':[str(x) for x in endpoint],
                  'neighbor':[str(x) for x in neighbor]}
            (root/'fixtures/stacked_48_geometry.json').write_text(json.dumps(geom,indent=2)+'\n')
    rng=random.Random(206)
    for d,q in ((3,5),(3,7),(4,6),(4,8),(5,7)):
        A=[[-Q(i==j) for j in range(d)] for i in range(d)]
        A += [[Q(rng.randrange(1,20),rng.randrange(2,10)) for j in range(d)] for _ in range(q)]
        b=[Q(0)]*d+[Q(1)]*q;vs=vertices(A,b);target=(Q(0),)*d
        pts,pg=edge_graph(A,vs); nbrs=pg[pts.index(target)]
        neighbor=pts[min(nbrs)]
        for endpoint in (pts[-1],pts[len(pts)//2]):
            data,res=geometric_path(A,b,vs,target,endpoint,neighbor)
            res['cut_rank']=rank(A[d:]);examples.append(res);total_calls+=len(res['carrier_dimensions'])
    # Nonsimple targets: deleted cuts may be tight at the target, but the
    # independent interior center is strict. The star retains only d rows.
    A=[[Q(0),Q(0),Q(-1)],[Q(1),Q(0),Q(1)],[-Q(1),Q(0),Q(1)],
       [Q(0),Q(1),Q(1)],[Q(0),-Q(1),Q(1)]]
    b=[Q(0),Q(1),Q(1),Q(1),Q(1)];vs=vertices(A,b);target=(Q(0),Q(0),Q(1))
    for endpoint in vs:
        data,res=basis_star_audit(A,b,vs,target,endpoint)
        examples.append(res);total_calls+=len(res['carrier_dimensions'])
    for d in (3,4,6):
        A=[list(map(Q,s)) for s in product((-1,1),repeat=d)];b=[Q(1)]*len(A)
        pts=[tuple(Q(sign*int(i==j)) for i in range(d)) for j in range(d) for sign in (-1,1)]
        vs={p:{i for i,(a,bi) in enumerate(zip(A,b)) if dot(a,p)==bi} for p in pts}
        for endpoint in (pts[1],pts[-1]):
            data,res=basis_star_audit(A,b,vs,pts[0],endpoint)
            examples.append(res);total_calls+=len(res['carrier_dimensions'])
            if d==6:
                (root/'fixtures/nonsimple_6d_basis_star_incidence.json').write_text(json.dumps(data,indent=2)+'\n')
    # Three contacts are attainable, and chordless without metric minimality fails.
    sharp={'vertex_count':4,'edges':[[0,1],[1,2],[0,3],[1,3],[2,3]],'path':[0,1,2],
           'available':[0,1,2,3],'selected':[0,1,2],'excess':4,'carrier_excesses':[3,4,3]}
    require(audit(sharp)['total_contact_load']==10,'three-window sharpness')
    counts['availability_defect_cases']=0
    for mask in range(8):
        sel=[i for i in range(3) if (mask>>i)&1]
        for defect in range(6):
            x=deepcopy(sharp);x['selected']=sel;x['excess']=4+defect
            x['carrier_excesses']=[sharp['carrier_excesses'][i]+defect for i in sel]
            audit(x);counts['availability_defect_cases']+=1
    x=deepcopy(sharp);x['excess']=3;x['carrier_excesses']=[2,3,2]
    require(audit(x)['subtraction_free_lhs']==19,'s>e subtraction-free boundary')
    bad=[]
    nongeo={'vertex_count':9,'edges':[[i,i+1] for i in range(7)]+[[8,i] for i in range(8)],
            'path':list(range(8)),'available':list(range(9)),'selected':list(range(8)),
            'excess':9,'carrier_excesses':[1]*8}
    bad.append(nongeo)
    for key,value in [('carrier_excesses',[100,100,100]),('path',[0,1,0,1,2]),
                      ('selected',[0,0]),('available',[0,1,2,3,3]),('excess',True),
                      ('selected',[0,1,3]),('vertex_count',3)]:
        x=deepcopy(sharp);x[key]=value;bad.append(x)
    rejects=0
    for x in bad:
        try: audit(x)
        except (ValueError,TypeError,KeyError): rejects+=1
        else: raise AssertionError('negative control accepted')
    # The numerical bounds still permit exponential independent recursion.
    recurrence=[0,1,2,3]
    for e in range(4,41):
        require(2*(e-1)<=3*e-2,'aggregate resource budget')
        require((e-1)+2<=e+2,'old selected-degree resource budget')
        recurrence.append(1+2*recurrence[-1])
    receipt={'status':'PASS','scope':'Exact finite/integer/rational regressions; NOT Lean or platform acceptance.',
             **counts,'geometric_certificate_instances':len(examples),'actual_selected_carriers':total_calls,
             'certified_single_vertex_truncations':trunc_steps,'negative_controls_rejected':rejects,
             'examples':examples,'independent_call_majorant':{str(e):recurrence[e] for e in (10,20,40)},
             'elapsed_seconds':round(time.monotonic()-start_time,3)}
    source_paths=[
        'Solutions/PolynomialGeodesicRowIncidence.lean',
        'Solutions/PolynomialAllCutCarrierMass.lean',
        'Solutions/PolynomialGeodesicMassRouting.lean',
        'Solutions/PolynomialBasisStarMass.lean',
        'scripts/geodesic_row_mass.py', 'scripts/test_geodesic_row_mass.py',
    ]
    receipt['source_sha256']={name:hashlib.sha256((root/name).read_bytes()).hexdigest()
                              for name in source_paths}
    (root/'research/GEODESIC_ROW_MASS_CHECK_2026-09-12.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    summary={k:v for k,v in receipt.items() if k!='examples'}
    summary['examples']=[{k:v for k,v in ex.items() if k in (
        'ambient_dimension','rows','vertices','available','selected','selected_runs',
        'carrier_mass','old_selected_only_bound','new_mass_bound','total_contact_load',
        'actual_assembled_edge_cost','basis_star','target_active_rows',
        'available_rows_tight_at_target','cut_rank')} for ex in examples]
    (root/'research/GEODESIC_ROW_MASS_SUMMARY_2026-09-12.json').write_text(
        json.dumps(summary,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k not in ('examples','source_sha256')},indent=2))
    print('Geometric examples:')
    for x in examples:
        print({k:x[k] for k in ('ambient_dimension','rows','vertices','selected','carrier_mass',
                               'old_selected_only_bound','new_mass_bound','actual_assembled_edge_cost')})

if __name__=='__main__':main()
