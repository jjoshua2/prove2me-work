#!/usr/bin/env python3
"""Independent replacement checks for the committed #205 fixtures.

The four original checker files are unavailable here. This script does not
reconstruct their missing bytes or claim their original test counts. It checks
all input rows, ordinary edges and Schur identities in the retained fixtures.
"""
from __future__ import annotations
from copy import deepcopy
import hashlib,json
from itertools import product
from pathlib import Path
from projective_factor_discovery import Q,dot,identity,inverse,matmul,rank,rational,require
from test_contractive_feedback_boxes import feedback_vertices

def vec(xs):return [rational(x) for x in xs]
def mat(xs):return [vec(x) for x in xs]
def mv(A,x):return [dot(r,x) for r in A]

def normal_form(data,cert):
    A,b,p=mat(data['A']),vec(data['b']),vec(data['anchor']);d=len(p)
    require(len(A)==len(b)==2*d and all(len(r)==d for r in A),'Complete 2d-row input required')
    T,Ti,C=mat(cert['coordinate_matrix']),mat(cert['inverse_coordinates']),mat(cert['feedback'])
    beta,w,scales=vec(cert['widths']),vec(cert['weight']),vec(cert['upper_scales'])
    low,up=cert['lower_rows'],cert['upper_rows']
    require(len(low)==len(up)==d and sorted(low+up)==list(range(2*d)),'All rows must be partitioned')
    require(all(type(i) is int for i in low+up),'Integer row indices required')
    require(all(len(B)==d and all(len(r)==d for r in B) for B in [T,Ti,C]),'Matrix shape')
    require(matmul(T,Ti)==identity(d) and matmul(Ti,T)==identity(d),'Coordinate inverse')
    require(len(beta)==len(w)==len(scales)==d and min(beta+w+scales)>0,'Positive vector witnesses')
    require(all(x>=0 for row in C for x in row),'Nonnegative feedback')
    require(all(dot(C[i],w)<w[i] for i in range(d)),'Strict weighted contraction')
    transformed=matmul(A,Ti);shift=[b[i]-dot(A[i],p) for i in range(2*d)]
    for i in range(d):
        require(transformed[low[i]]==[-Q(i==j) for j in range(d)] and shift[low[i]]==0,'Lower row identity')
        require(transformed[up[i]]==[scales[i]*(Q(i==j)-C[i][j]) for j in range(d)],'Upper row identity')
        require(shift[up[i]]==scales[i]*beta[i],'Upper offset identity')
    return A,b,p,T,Ti,C,beta,w

def ordinary_route(A,b,points):
    d=len(A[0]);points=mat(points);active=[]
    for x in points:
        require(len(x)==d and all(dot(r,x)<=bi for r,bi in zip(A,b)),'Infeasible route point')
        ids={i for i,(r,bi) in enumerate(zip(A,b)) if dot(r,x)==bi}
        require(rank([A[i] for i in ids])==d,'Route point not a vertex')
        active.append(ids)
    for i in range(len(points)-1):
        require(points[i]!=points[i+1],'Repeated point is not an edge in this fixture')
        require(rank([A[k] for k in active[i]&active[i+1]])==d-1,'Step is not an ordinary edge')
    return len(points),len(points)-1

def schur(data,cert,face):
    _,_,_,_,_,C,b,w=normal_form(data,cert);d=len(b)
    U,L,F=face['fixed_upper'],face['fixed_lower'],face['free'];f=len(F)
    require(sorted(U+L+F)==list(range(d)),'Face coordinate partition')
    start,target=face['start'],face['target']
    require(len(start)==len(target)==d and all(x in (0,1) for x in start+target),'Binary endpoints')
    require(U==[i for i in range(d) if start[i]==target[i]==1],'Actual shared upper rows')
    require(L==[i for i in range(d) if start[i]==target[i]==0],'Actual shared lower rows')
    R=inverse([[Q(i==j)-C[i][j] for j in U] for i in U]) if U else []
    response=matmul(R,[[C[i][j] for j in F] for i in U]) if U else []
    offset=mv(R,[b[i] for i in U]) if U else []
    require(response==mat(face['upper_response']) and offset==vec(face['upper_offset']),'Schur solve identities')
    CF=[[C[i][j]+sum((C[i][k]*response[t][s] for t,k in enumerate(U)),Q(0)) for s,j in enumerate(F)] for i in F]
    bf=[b[i]+sum((C[i][k]*offset[t] for t,k in enumerate(U)),Q(0)) for i in F]
    scales=vec(face['row_scales']);got=mat(face['feedback']);widths=vec(face['widths']);weight=vec(face['weight'])
    require(len(scales)==f and min(scales)>0,'Schur row scales')
    require(got==[[Q(i==j)-(Q(i==j)-CF[i][j])/scales[i] for j in range(f)] for i in range(f)],'Reduced feedback')
    require(widths==[bf[i]/scales[i] for i in range(f)],'Reduced widths')
    child=feedback_vertices(got,widths,weight)
    parent=feedback_vertices(C,b,w)
    wanted={v for bits,v in parent.items() if all(bits[i]==1 for i in U) and all(bits[i]==0 for i in L)}
    mapped=set()
    for y in child.values():
        x=[Q(0)]*d
        for i,yi in zip(F,y):x[i]=yi
        for t,i in enumerate(U):x[i]=offset[t]+dot(response[t],y)
        mapped.add(tuple(x))
    require(mapped==wanted,'Whole common-face vertex image')
    return len(mapped)

def run():
    root=Path('research');data=json.loads((root/'coupled_cycle_6d_input.json').read_text());receipt=json.loads((root/'coupled_cycle_6d_certificate.json').read_text())
    A,b,p,T,Ti,C,beta,w=normal_form(data,receipt['certificate'])
    vertices,edges=ordinary_route(A,b,receipt['routing']['route']['vertices'])
    mapped=schur(data,receipt['certificate'],receipt['carrier']['certificate'])
    cut=json.loads((root/'monotone_cut_4d_route.json').read_text())
    A,b,p,T,Ti,_,_,_=normal_form(cut['parent_input'],cut['parent_certificate'])
    cr,cb=vec(cut['cut']['normal']),rational(cut['cut']['bound'])
    require(all(x>=0 for x in matmul([cr],Ti)[0]),'Cut is not monotone in box coordinates')
    points=cut['route']['vertices'];require(vec(points[0])==vec(cut['start']) and vec(points[-1])==vec(cut['target']),'Cut route endpoints')
    cv,ce=ordinary_route(A+[cr],b+[cb],points)
    require(ce<=len(p)+2,'One-cut budget')
    negative=0
    for which in range(3):
        bad=deepcopy(receipt['certificate'])
        if which==0:bad['weight'][0]='-1'
        if which==1:bad['upper_rows'][0]=bad['lower_rows'][0]
        if which==2:bad['inverse_coordinates'][0][0]='2'
        try:normal_form(data,bad)
        except ValueError:negative+=1
        else:raise AssertionError('Corrupt normal form accepted')
    bad=deepcopy(receipt['carrier']['certificate']);bad['upper_offset'][0]='99'
    try:schur(data,receipt['certificate'],bad)
    except ValueError:negative+=1
    else:raise AssertionError('Corrupt Schur model accepted')
    paths=['scripts/verify_coupled_box_fixtures.py','scripts/projective_factor_discovery.py','scripts/test_contractive_feedback_boxes.py','research/coupled_cycle_6d_input.json','research/coupled_cycle_6d_certificate.json','research/monotone_cut_4d_route.json']
    return {'status':'PASS','scope':'New independent fixture audit, not a rerun of missing original checkers or a Lean verdict.',
            'normal_forms':2,'route_vertices':vertices+cv,'ordinary_edges':edges+ce,'same_face_vertices':mapped,'negative_controls':negative,
            'sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}}
if __name__=='__main__':print(json.dumps(run(),indent=2)+'\n')
