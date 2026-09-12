#!/usr/bin/env python3
"""Ordinary-edge routes in packing polytopes via low-dimensional support faces.

For Q={x>=0:Ax<=b}, A>=0,b>=0, every vertex has at most rank(A)
positive coordinates. Coordinate support faces give origin routes without a
box certificate or global vertex enumeration. In rank two the pair bound is
q+2, independent of d. All entries are exact rational numbers; face enumeration
is capped. This executable is not a Lean proof or a universal polynomial bound.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Any
from hirsch_exact_geometry import *


def model(data:dict[str,Any])->dict[str,Any]:
    a,b=matrix(data['A']),vector(data['b']);d=len(a[0]) if a else 0
    require(d>0 and len(a)==len(b),'Positive-dimensional A/b required')
    require(all(v>=0 for row in a for v in row) and all(v>=0 for v in b),'Packing signs required')
    require(all(any(row[j]>0 for row in a) for j in range(d)), 'A column is unbounded')
    # For nonnegative rows, column coverage proves finite coordinate bounds.
    lower=[[-v for v in row]for row in eye(d)]
    return {'A':a,'b':b,'d':d,'q':len(a),'rank':rank(a), 'full_A':lower+a,'full_b':[Q(0)]*d+b}


def budget(h:int,q:int)->int:
    if h==0:return 0
    if h==1:return 1
    if h==2:return (q+2)//2
    return (q+h)*2**max(h-3,0)


def support(m:dict,x:Vector)->list[int]:
    act=verify_vertex(m['full_A'],m['full_b'],x)
    S=[i for i,v in enumerate(x)if v>0]
    activecuts=[i for i in range(m['q'])if m['d']+i in act]
    require(rank([[m['A'][i][j]for j in S]for i in activecuts])==len(S),'Active cuts do not span support')
    require(len(S)<=m['rank'],'Support exceeds cut rank')
    return S


def origin_route(m:dict,x:Vector,max_bases:int)->dict:
    S=support(m,x);h=len(S)
    if not S:return {'support':S,'vertices':[x],'local_vertices_enumerated':1,'budget':0}
    a=[[-v for v in row]for row in eye(h)]+[[row[j]for j in S]for row in m['A']]
    b=[Q(0)]*h+m['b'];vv=vertices(a,b,max_bases=max_bases);g=graph(a,vv)
    path=shortest_path(g,tuple(x[j]for j in S),(Q(0),)*h)
    lifted=[]
    for y in path:
        z=[Q(0)]*m['d']
        for j,v in zip(S,y):z[j]=v
        lifted.append(z)
    require(len(path)-1<=budget(h,m['q']),'Support-face budget failed')
    return {'support':S,'vertices':lifted,'local_vertices_enumerated':len(vv),'budget':budget(h,m['q'])}


def route(data:dict[str,Any],max_local_bases:int=200000)->dict:
    m=model(data);x,y=vector(data['start']),vector(data['target'])
    require(len(x)==len(y)==m['d'],'Endpoint shape')
    left,right=origin_route(m,x,max_local_bases),origin_route(m,y,max_local_bases)
    points=left['vertices']+list(reversed(right['vertices']))[1:]
    # Rank-one packing polytopes are simplices; distinct vertices are adjacent.
    if m['rank']==1:
        points=[x]if x==y else [x,y]
    c={'left':left,'right':right,'vertices':points}
    return {'certificate':c,'verified':verify(data,c)}


def verify(data:dict[str,Any],c:dict)->dict:
    m=model(data);x,y=vector(data['start']),vector(data['target']);hs=[]
    for key,p in [('left',x),('right',y)]:
        S=support(m,p);part=c[key];hs.append(len(S))
        require(part['support']==S,'Changed coordinate support')
        points=[vector(v)for v in part['vertices']]
        require(points and points[0]==p and points[-1]==[Q(0)]*m['d'],'Wrong origin endpoints')
        require(part['budget']==budget(len(S),m['q']) and len(points)-1<=part['budget'],'Wrong local bound')
        for v in points:
            require(all(v[j]==0 for j in range(m['d'])if j not in S),'Route leaves its support face')
            verify_vertex(m['full_A'],m['full_b'],v)
        for a,b in zip(points,points[1:]):verify_edge(m['full_A'],m['full_b'],a,b)
    points=[vector(v)for v in c['vertices']]
    expected=[vector(v)for v in c['left']['vertices']]+[vector(v)for v in reversed(c['right']['vertices'])][1:]
    if m['rank']==1:expected=[x]if x==y else [x,y]
    require(points==expected and points[0]==x and points[-1]==y,'Wrong assembled walk')
    for a,b in zip(points,points[1:]):verify_edge(m['full_A'],m['full_b'],a,b)
    bound=1 if m['rank']==1 else 2*budget(m['rank'],m['q'])
    require(len(points)-1<=bound,'Rank bound failed')
    return {'dimension':m['d'],'cuts':m['q'],'cut_rank':m['rank'], 'endpoint_support_sizes':hs,
            'ordinary_edges':len(points)-1,'global_rank_budget':bound,'global_vertices_enumerated':0,
            'scope':'Exact original-row edge checks, not shortest-path optimality or Lean/platform verification.'}


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('input',type=Path)
    parser.add_argument('--output',type=Path);parser.add_argument('--max-local-bases',type=int,default=200000)
    args=parser.parse_args()
    try:
        out=route(json.loads(args.input.read_text()),args.max_local_bases)
        text=json.dumps(jsonable(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError)as exc:parser.exit(2,f'Not certified: {exc}\n')

if __name__=='__main__':main()
