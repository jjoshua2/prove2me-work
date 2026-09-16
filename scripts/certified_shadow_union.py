#!/usr/bin/env python3
"""Switch between a finite set of certified ORIGINAL-H shadow routes.

The producer explores only the union of the supplied computed paths, not the
full polytope graph. The output may be shorter than EVERY constituent shadow.
Its distance-potential certificate proves optimality in that discovered union,
NOT in the entire polytope. There is no universal polynomial union-size claim.
Black's single-coherent-path lower bound is not a bound on such spliced paths,
but each constituent route can still be expensive to discover in the worst case.
"""
from collections import deque
from pathlib import Path
import argparse, json
import certified_rational_shadow as shadow

require,rat,serial=shadow.require,shadow.rat,shadow.serial


def union_graph(paths):
    G={}
    for path in paths:
        for x in path:G.setdefault(x,set())
        for x,y in zip(path,path[1:]):G[x].add(y);G[y].add(x)
    return G


def construct(data,rotations,query_cap=10000,pivot_cap=20000):
    A,b,u,v=shadow.parse(data);d=len(u)
    require(type(rotations)is list and rotations and all(len(p)==2 and
        all(type(j)is int and 0<=j<d for j in p) for p in rotations),'invalid finite rotation schedule')
    require(len(set(map(tuple,rotations)))==len(rotations),'duplicate rotation schedule')
    runs=[shadow.construct(data,query_cap,pivot_cap,tuple(p)) for p in rotations]
    paths=[[tuple(map(rat,x))for x in r['verified']['path']]for r in runs]
    G=union_graph(paths);D={u:0};parent={};queue=deque([u])
    while queue:
        x=queue.popleft()
        for y in sorted(G[x]):
            if y not in D:D[y]=D[x]+1;parent[y]=x;queue.append(y)
    require(set(D)==set(G),'union disconnected')
    p=[v]
    while p[-1]!=u:p.append(parent[p[-1]])
    p.reverse()
    c=serial({'format':'certified-shadow-union-v1','problem_sha256':shadow.digest(A,b,u,v),
        'shadows':[r['certificate']for r in runs],'path':p,
        'distance_potential':[{'point':x,'distance':D[x]}for x in sorted(G)]})
    return {'certificate':c,'verified':verify(data,c),
        'discovery':{'basis_rotations':rotations,'shadows':[r['discovery']for r in runs],
            'BFS_only_on_discovered_union':True,'entire_polytope_graph_enumerated':False}}


def verify(data,c):
    A,b,u,v=shadow.parse(data)
    require(c['format']=='certified-shadow-union-v1'and c['problem_sha256']==shadow.digest(A,b,u,v),'changed union input')
    require(type(c['shadows'])is list and c['shadows'],'no certified shadows')
    reports=[shadow.verify(data,p)for p in c['shadows']]
    paths=[[tuple(map(rat,x))for x in r['path']]for r in reports];G=union_graph(paths)
    path=[tuple(map(rat,x))for x in c['path']]
    require(path and path[0]==u and path[-1]==v and len(path)==len(set(path)),'wrong union route endpoints or repetition')
    require(all(x in G for x in path)and all(y in G[x]for x,y in zip(path,path[1:])),'unseen chord or edge in union route')
    labels={}
    for row in c['distance_potential']:
        x=tuple(map(rat,row['point']));n=row['distance']
        require(x in G and x not in labels and type(n)is int and n>=0,'invalid union distance label')
        labels[x]=n
    require(set(labels)==set(G)and labels[u]==0 and labels[v]==len(path)-1,'incomplete or inconsistent distance potential')
    require(all(abs(labels[x]-labels[y])<=1 for x in G for y in G[x]),'distance potential jumps over an edge')
    # Telescoping this 1-Lipschitz potential along ANY union path gives the
    # matching lower bound. The checker needs no BFS or optimizer.
    L=len(path)-1;lengths=[len(p)-1 for p in paths]
    require(L<=min(lengths),'union route longer than a constituent')
    return {'status':'PASS','ambient_dimension':len(u),'original_rows':len(A),'shadows':len(paths),
        'individual_shadow_edges':lengths,'sum_discovered_shadow_edges':sum(lengths),
        'union_vertices':len(G),'union_edges':sum(map(len,G.values()))//2,
        'selected_original_edges':L,'strictly_shorter_than_every_sampled_shadow':L<min(lengths),
        'shortest_in_discovered_union':True,'shortest_in_entire_polytope_claimed':False,
        'primary_support_queries':sum(r['primary_support_queries']for r in reports),
        'tie_resolution_queries':sum(r['tie_resolution_queries']for r in reports),
        'locked_original_rows':reports[0]['locked_original_rows'],'path':serial(path),
        'BFS_or_LP_in_verifier':False,
        'scope':'Shortest certified route inside the explored union only; no uniform polynomial discovery or route bound.'}


def main():
    import sys
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(250000)
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--certificate',type=Path);p.add_argument('--query-cap',type=int,default=10000);a=p.parse_args()
    try:
        data=json.loads(a.input.read_text());raw=json.loads(a.certificate.read_text())if a.certificate else None
        out=verify(data,raw.get('certificate',raw))if raw is not None else construct(data,data['basis_rotations'],a.query_cap)
        a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
    except(ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError)as e:p.exit(2,f'No complete shadow-union certificate: {e}\n')
if __name__=='__main__':main()
