#!/usr/bin/env python3
"""Smaller exact certificate: 2,002 chamber bases and 6,400 sign/orbit checks.

Standard library only. Requires q28_certificate.json for the already-computed
20 representative vectors, but independently enumerates the chamber's vertices
and checks that its eligible vertices are exactly those representatives.

This produces proof data, not a Lean kernel verification.
"""
from __future__ import annotations
from collections import Counter
from itertools import combinations
from math import gcd
from functools import reduce
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
C=[[18,0,0,0,1],[0,0,30,0,1],[0,0,0,30,1],
   [0,5,0,25,1],[0,0,18,18,1],[0,0,18,0,-1],
   [0,30,0,0,-1],[30,0,0,0,-1],[25,0,0,5,-1],[18,18,0,0,-1],
   [-1,0,0,0,0],[0,-1,0,0,0],[0,0,-1,0,0],[0,0,0,-1,0]]
B=[1]*10+[0]*4

def det(m):
    a=[r[:] for r in m]; prev=1;sgn=1;n=len(a)
    for k in range(n-1):
        p=next((p for p in range(k,n) if a[p][k]),None)
        if p is None:return 0
        if p!=k:a[p],a[k]=a[k],a[p];sgn=-sgn
        piv=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                x=a[i][j]*piv-a[i][k]*a[k][j]
                assert x%prev==0
                a[i][j]=x//prev
            a[i][k]=0
        prev=piv
    return sgn*a[-1][-1]

def dot(a,b):return sum(x*y for x,y in zip(a,b))

def main():
    base_data=json.loads((HERE/'q28_certificate.json').read_text())
    A=base_data['A']; orbits=base_data['sign_orbits']; records=[]; points={}; status=Counter()
    for ix in combinations(range(14),5):
        m=[C[i][:] for i in ix]; d=det(m); r={'basis':list(ix),'determinant':d}
        if d==0:
            r['status']='singular';records.append(r);status['singular']+=1;continue
        ns=[]
        for j in range(5):
            mm=[row[:] for row in m]
            for k,i in enumerate(ix):mm[k][j]=B[i]
            ns.append(det(mm))
        if d<0:d=-d;ns=[-x for x in ns]
        g=reduce(gcd,ns,d);ns=[x//g for x in ns];d//=g
        assert all(dot(C[i],ns)==B[i]*d for i in ix)
        r['numerators']=ns;r['denominator']=d
        violation=next((i for i in range(14) if dot(C[i],ns)>B[i]*d),None)
        if violation is not None:
            r['status']='infeasible';r['violated_row']=violation;status['infeasible']+=1
        else:
            r['status']='feasible';status['feasible']+=1;points[tuple(ns+[d])]=True
        records.append(r)
    chamber=[]
    for p in sorted(points):
        active=[i for i,a in enumerate(A) if dot(a,p[:5])==p[5]]
        chamber.append({'numerators':list(p[:5]),'denominator':p[5],'original_active_rows':active})
    kept={tuple(v['numerators']+[v['denominator']]) for v in chamber if len(v['original_active_rows'])>=5}
    expected={tuple(v['numerators']+[v['denominator']]) for v in orbits}
    assert kept==expected and len(kept)==20 and len(chamber)==60
    # Sign changes preserve the original system, as witnessed by row permutations.
    def flip(a,s):return [(-a[j] if s>>j&1 else a[j]) if j<4 else a[j] for j in range(5)]
    for s in range(16):assert sorted(flip(a,s) for a in A)==sorted(A)
    def active(o,s):return {i for i,a in enumerate(A) if dot(a,flip(o['numerators'],s))==o['denominator']}
    active_cache=[[active(o,s) for s in range(16)] for o in orbits]
    levels=[o['level_from_u'] for o in orbits]; nchecks=0
    QE={tuple(e) for e in base_data['sign_quotient_edges']}
    for i in range(20):
        for j in range(20):
            for s in range(16):
                nchecks+=1
                common=len(active_cache[i][0]&active_cache[j][s])
                if abs(levels[i]-levels[j])>1: assert common<=3
                if common>=4: assert i==j or tuple(sorted([i,j])) in QE
    summary={'basis_count':len(records),'basis_status_counts':dict(status),
      'chamber_vertex_count':len(chamber),'chamber_vertices_with_at_least_five_original_active_rows':len(kept),
      'sign_orbit_checks':nchecks,'level_step_certificate_valid':True}
    result={'status':'Exact external certificate; not Lean checked','chamber_A':C,'chamber_b':B,
      'summary':summary,'chamber_vertices':chamber,'basis_certificate':records}
    (HERE/'q28_chamber_certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
