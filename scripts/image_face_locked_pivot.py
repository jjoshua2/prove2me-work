#!/usr/bin/env python3
"""Adaptive minimal-common-IMAGE-face restriction of the accepted #248 selector.

No image facet list, graph, or neighboring vertex is supplied. Midpoint-fibre
certificates construct the least convex face containing current and target.
An edge selected inside that face is transferred to the original image. The
fixed target objective is retained, and every acquired target face is locked.
This is NOT a polynomial bound: arbitrarily long constant-face phases remain.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as Q
from pathlib import Path
import image_tangent_pivot as T
from exact_farkas_lp import ExactLP, Unbounded, rat, serial, dot, require, verify_dual, dense_dual


def face_system(A,b,J):
    return A+tuple(T.mul(-1,A[j]) for j in J), b+tuple(-b[j] for j in J)


def discover_common_face(A,b,G,u,v,source,target,cap=20000):
    """#247 zero-fibre-slack construction, without its unnecessary pair-edge query.
    The current and target source lifts are witnesses, not assumed source vertices.
    """
    n=len(A[0]);m=len(A);p=len(G);mid=T.mul(Q(1,2),T.add(u,v))
    x=T.mul(Q(1,2),T.add(source,target));C,d=T.fibre(A,b,G,mid)
    require(T.feasible(C,d,x),'midpoint lift is not feasible')
    lp=ExactLP(C,d,x,cap);points=[x];J=[];duals=[]
    for j,a in enumerate(A):
        try:
            out=lp.maximize(T.mul(-1,a));slack=b[j]+rat(out['value'])
            require(slack>=0,'negative maximum slack')
            if slack==0:J.append(j);duals.append({'row':j,'dual':out['dual']})
            else:points.append(T.vec(out['point'],n))
        except Unbounded as e:
            points.append(T.add(e.point,e.direction))
    anchor=tuple(sum(z[i] for z in points)/len(points) for i in range(n))
    normal=[Q(0)]*p;weights=[Q(1)]*len(J)
    for q in duals:
        z=dense_dual(q['dual'],len(C))
        for i,j in enumerate(J):weights[i]+=z[j]
        for l in range(p):normal[l]-=z[m+l]-z[m+p+l]
    out=serial({'anchor':anchor,'rows':J,'zero_duals':duals,'normal':normal,'weights':weights})
    verify_common_face(A,b,G,u,v,out)
    return out


def verify_common_face(A,b,G,u,v,c):
    """Finite arithmetic audit of EXACT minimal-face witness; no optimizer/rank."""
    n=len(A[0]);m=len(A);p=len(G);mid=T.mul(Q(1,2),T.add(u,v));x=T.vec(c['anchor'],n)
    J=c['rows'];require(type(J)is list and all(type(j)is int and 0<=j<m for j in J)
        and J==sorted(set(J)),'invalid selected rows')
    require(T.im(G,x)==mid and T.feasible(A,b,x),'invalid strict midpoint anchor')
    require(all((dot(a,x)==t)==(i in J) for i,(a,t) in enumerate(zip(A,b))),
        'midpoint anchor not strict off selected rows')
    C,d=T.fibre(A,b,G,mid);normal=[Q(0)]*p;weights=[Q(1)]*len(J);seen=set()
    for q in c['zero_duals']:
        j=q['row'];require(type(j)is int and j in J and j not in seen,'invalid/repeated forced row');seen.add(j)
        require(verify_dual(C,d,T.mul(-1,A[j]),q['dual'])==-b[j],'not a zero-slack optimum')
        z=dense_dual(q['dual'],len(C))
        require(all(not z[i] or i in J for i in range(m)),'noncomplementary fibre dual')
        for i,k in enumerate(J):weights[i]+=z[k]
        for l in range(p):normal[l]-=z[m+l]-z[m+p+l]
    require(seen==set(J),'missing forced-row proof')
    require(T.vec(c['normal'],p)==tuple(normal) and T.vec(c['weights'],len(J))==tuple(weights),
        'not the derived positive exposing combination')
    for i in range(n):
        require(sum(normal[l]*G[l][i] for l in range(p))==sum(weights[j]*A[k][i] for j,k in enumerate(J)),
            'invalid face exposure column')
    beta=sum(weights[j]*b[k] for j,k in enumerate(J))
    require(dot(normal,u)==beta==dot(normal,v),'common face does not contain both endpoints')
    return J


def construct(data,edge_cap=200,pivot_cap=20000):
    A,b,G,u,v=T.read(data);target=T.discover_vertex(A,b,G,v,cap=pivot_cap)
    yt=T.vec(target['anchor'],len(A[0]));bounds=T.compact_image(A,b,G,yt,pivot_cap)
    current=u;steps=[]
    if u==v:T.verify_vertex(A,b,G,u,target)
    source=T.vec(T.discover_vertex(A,b,G,u,cap=pivot_cap)['anchor'],len(A[0])) if u!=v else yt
    while current!=v:
        require(len(steps)<edge_cap,'route cap: no polynomial bound/completion claimed')
        f=discover_common_face(A,b,G,current,v,source,yt,pivot_cap)
        J=verify_common_face(A,b,G,current,v,f);C,d=face_system(A,b,J)
        require(T.feasible(C,d,yt),'global target lift not on common face')
        # The original target certificate is valid on the subset. Its SAME
        # normal/anchor are used; no changing-objective monotonicity shortcut.
        step=T.select_step(C,d,G,current,v,target,pivot_cap)
        steps.append({'face':f,'edge':step});current=T.vec(step['to'],len(G))
        source=T.vec(step['ray_optimum']['point'],len(A[0])+1)[:-1]
    c=serial({'problem_sha256':T.hash_input(A,b,G,u,v),'target_vertex':target,
        'image_boundedness':bounds,'steps':steps})
    return {'certificate':c,'verified':verify(data,c)}


def verify(data,c):
    A,b,G,u,v=T.read(data);require(c['problem_sha256']==T.hash_input(A,b,G,u,v),'changed problem')
    T.verify_vertex(A,b,G,v,c['target_vertex']);T.verify_compact(A,b,G,c['image_boundedness'])
    current=u;seen={u};previous=set();reports=[];row_chain=[];strict_locks=0
    for item in c['steps']:
        step=item['edge'];require(T.vec(step['from'],len(G))==current,'broken original-image route')
        J=verify_common_face(A,b,G,current,v,item['face']);js=set(J)
        require(previous<=js,'an acquired common face was lost')
        strict_locks+=bool(reports and previous<js);previous=js;row_chain.append(J)
        C,d=face_system(A,b,J)
        require(T.feasible(C,d,T.vec(c['target_vertex']['anchor'],len(A[0]))),'target lift excluded')
        r=T.verify_step(C,d,G,v,c['target_vertex'],step);current=T.vec(step['to'],len(G))
        require(current not in seen,'repeated image vertex');seen.add(current);reports.append(r)
    require(current==v,'target not reached')
    return {'status':'PASS','original_image_edges':len(reports),'strict_common_face_drops':strict_locks,
        'common_original_row_chain':row_chain,'all_original_edges':True,'fixed_target_objective':True,
        'acquired_target_faces_preserved':True,'edge_reports':reports,
        'scope':'Actual minimal-image-face locking and edge transfer. No polynomial bound on a constant-face phase; not Lean-extracted JSON.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--edge-cap',type=int,default=200);a=p.parse_args()
    try:
        d=json.loads(a.input.read_text());out=verify(d,json.loads(a.certificate.read_text())) if a.certificate else construct(d,a.edge_cap)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as e:p.exit(2,f'No completed locked route: {e}\n')
if __name__=='__main__':main()
