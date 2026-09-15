#!/usr/bin/env python3
"""Small flag subdivisions give ORIGINAL-edge routes past nonflag defects.

For a partition of original facet labels, barycentrically subdivide each
induced block, compatibly in every simplex of the polar boundary. The result
is flag IFF every original minimal nonface meets at most two blocks. With M
nonempty block faces, the classical flag-normal theorem supplies <=M-d steps.
The carrier union sends adjacent refined facets to equal or adjacent original
facets, never to a projected chord. Consecutive equal carriers are erased and
all remaining edges are independently audited on the original H inequalities.

Default block discovery completely checks minimal nonfaces up to size d+1;
its search can be exponential and is capped. This is not a universal efficient
small-block decomposition or a new proof of the classical flag theorem.
"""
from __future__ import annotations
from itertools import combinations
from math import comb
from pathlib import Path
import argparse, hashlib, json
import original_facet_segments as old

Q,require,rat,serial,dot=old.Q,old.require,old.rat,old.serial,old.dot


def partitions(raw,m):
    require(type(raw)is list and raw,'nonempty partition required')
    out=[old.labels(B,m) for B in raw]
    require(all(out) and sum(map(len,out))==m and set().union(*out)==set(range(m)),
            'blocks must partition every original label')
    return sorted(out,key=lambda B:tuple(sorted(B)))


def nonfaces(m,d,O,cap):
    """Complete minimal-nonface certificate, no sampled flagness inference.
    Facet intersections in a simple d-polytope have size <=d. Any minimal
    nonface has size <=d+1; known empty subsets certify all supersets.
    The raw combination-count cap is explicit, even if many are pruned.
    """
    require(type(cap)is int and cap>0,'positive classification cap required')
    work=sum(comb(m,r) for r in range(1,min(d+1,m)+1))
    require(work<=cap,'complete defect-classification cap; no flag certificate')
    missing=[];asked=0
    for r in range(1,min(d+1,m)+1):
        for C in combinations(range(m),r):
            S=frozenset(C)
            if any(W<=S for W in missing):continue
            asked+=1
            if not O.ask(S):missing.append(S)
    require(all(len(S)>=2 for S in missing),'an alleged facet is empty')
    return missing,{'classification_subsets':work,'classification_questions':asked}


def choose_blocks(m,missing):
    """Deterministic heuristic; NOT minimum refinement-cost optimization.
    Merge the two smallest blocks met by a higher missing face whenever that
    face still meets >=3 blocks. Each merge reduces the block count by one.
    """
    blocks=[frozenset([i]) for i in range(m)];events=[]
    for W in sorted(missing,key=lambda S:(len(S),tuple(sorted(S)))):
        while True:
            hit=sorted([B for B in blocks if B&W],key=lambda B:(len(B),tuple(sorted(B))))
            if len(hit)<=2:break
            U,V=hit[:2];blocks=[B for B in blocks if B not in (U,V)]+[U|V]
            events.append({'missing':sorted(W),'left':sorted(U),'right':sorted(V)})
    blocks=sorted(blocks,key=lambda B:tuple(sorted(B)))
    return blocks,events


class Refinement:
    def __init__(self,m,d,O,blocks):
        self.m,self.d,self.O,self.blocks=m,d,O,blocks
        self.vertices=[];self.block_id=[];self.local_face_counts=[]
        for k,B in enumerate(blocks):
            count=0
            for size in range(1,min(d,len(B))+1):
                for C in combinations(sorted(B),size):
                    S=frozenset(C)
                    if O.ask(S):
                        self.vertices.append(S);self.block_id.append(k);count+=1
            self.local_face_counts.append(count)
        self.index={S:i for i,S in enumerate(self.vertices)}
        self.cache={};self.calls=0
    def ask(self,S):
        S=frozenset(S);self.calls+=1
        if S in self.cache:return self.cache[S]
        require(all(type(i)is int and 0<=i<len(self.vertices) for i in S),'bad refined vertex')
        for i,j in combinations(S,2):
            if self.block_id[i]==self.block_id[j] and not (
                    self.vertices[i]<=self.vertices[j] or self.vertices[j]<=self.vertices[i]):
                self.cache[S]=False;return False
        U=frozenset().union(*(self.vertices[i] for i in S))
        value=self.O.ask(U);self.cache[S]=value;return value
    def lift(self,F,common=frozenset()):
        ans=set()
        for B in self.blocks:
            prefix=frozenset()
            for i in sorted(F&B&common)+sorted((F&B)-common):
                prefix=prefix|{i};ans.add(self.index[prefix])
        require(len(ans)==self.d and self.ask(ans),'invalid lifted endpoint chain')
        return frozenset(ans)
    def carrier(self,F):
        require(len(F)==self.d and self.ask(F),'not a full refined simplex')
        U=frozenset().union(*(self.vertices[i] for i in F))
        require(len(U)==self.d,'refined facet has wrong original carrier dimension')
        return U


def structure(m,d,O,raw_blocks,classification_cap):
    missing,work=nonfaces(m,d,O,classification_cap)
    automatic,events=choose_blocks(m,missing)
    blocks=automatic if raw_blocks is None else partitions(raw_blocks,m)
    require(all(sum(bool(B&W) for B in blocks)<=2 for W in missing),
            'minimal nonface still meets three blocks; subdivision is not flag')
    R=Refinement(m,d,O,blocks)
    return R,missing,events,work


def audit_original(A,b,raw,path):
    vertices={}
    for p in raw:
        q={'point':list(map(rat,p['point'])),'active':p['active'],
           'directions':[list(map(rat,v)) for v in p['directions']]}
        x,J,D=old.basis.audit_basis(A,b,q);F=frozenset(J)
        require(F not in vertices,'duplicate original vertex certificate')
        vertices[F]=(tuple(x),J,D)
    require(set(vertices)==set(path),'missing or irrelevant carrier vertex')
    for F,H in zip(path,path[1:]):
        require(len(F&H)==len(A[0])-1,'carrier step is not an original ridge exchange')
        x,J,D=vertices[F];y,_,_=vertices[H];j=J.index(next(iter(F-H)))
        t,_=old.basis.maximal_step(A,b,x,D[j])
        require(t>0 and tuple(a+t*v for a,v in zip(x,D[j]))==y,'not a maximal ORIGINAL edge')
    return vertices


def project(R,refined):
    path=[];stationary=0
    for F in refined:
        U=R.carrier(F)
        if not path or U!=path[-1]:path.append(U)
        else:stationary+=1
    for F,H in zip(refined,refined[1:]):
        require(len(F&H)==R.d-1,'not a refined ridge step')
        U,V=R.carrier(F),R.carrier(H)
        require(U==V or len(U&V)==R.d-1,'subdivision carrier became a chord')
    return path,stationary


def run(data,classification_cap=500000,query_cap=500000,pivot_cap=20000):
    A,b,u,v=old.parse(data);m,d=len(A),len(u)
    pu=old.basis.basis_packet(A,b,u);pv=old.basis.basis_packet(A,b,v)
    F,H=frozenset(pu['active']),frozenset(pv['active'])
    O=old.Discovery(A,b,u,v,pivot_cap,query_cap)
    R,missing,events,work=structure(m,d,O,data.get('blocks'),classification_cap)
    M=len(R.vertices);start,end=R.lift(F,F&H),R.lift(H,F&H)
    cap=max(1,M-d);nodes=(4*d+4)*(cap+1)
    alg=old.Segment(M,d,R,cap,nodes);path=alg.between(start&end,start,end)
    out,stationary=project(R,path)
    lock=start&end
    if d>len(lock):
        for j in range(M):
            if j not in lock:R.ask(lock|{j})
    vp={}
    for B in out:
        if B not in vp:
            vp[B]=old.basis.basis_packet(A,b,O.point(B))
            require(frozenset(vp[B]['active'])==B,'nonsimple original carrier')
    cert={'format':'defect-block-subdivision-v1','problem_sha256':old.input_hash(A,b,u,v),
        'classification_cap':classification_cap,'boundedness':O.bounds,
        'blocks':[sorted(B) for B in R.blocks],
        'minimal_nonfaces':[sorted(W) for W in missing],
        'refined_vertices':[sorted(W) for W in R.vertices],
        'refined_path':[sorted(B) for B in path],'path':[sorted(B) for B in out],
        'vertices':list(vp.values()),'intersections':list(O.cache.values())}
    report=verify(data,serial(cert))
    return {'certificate':serial(cert),'verified':report,
        'discovery':{**work,'original_LP_maximizations':O.lp_calls,'LP_pivots':O.solver.pivots,
                     'partition_merges':events},
        'scope':'Research implementation. Classical flag-normal theorem used; no Lean/platform verdict.'}


def verify(data,c):
    A,b,u,v=old.parse(data);m,d=len(A),len(u)
    require(c['format']=='defect-block-subdivision-v1' and
            c['problem_sha256']==old.input_hash(A,b,u,v),'changed original problem')
    old.audit_bounds(A,b,c['boundedness']);O=old.Certified(A,b,c['intersections'])
    R,missing,events,work=structure(m,d,O,data.get('blocks'),c['classification_cap'])
    require(c['blocks']==[sorted(B) for B in R.blocks],'partition differs from input/discovery')
    require(c['minimal_nonfaces']==[sorted(W) for W in missing],'incomplete or incorrect defect list')
    require(c['refined_vertices']==[sorted(W) for W in R.vertices],'wrong refined registry')
    F=frozenset(old.basis.active_rows(A,b,u));H=frozenset(old.basis.active_rows(A,b,v))
    require(len(F)==len(H)==d,'original endpoints not simple vertices')
    start,end=R.lift(F,F&H),R.lift(H,F&H);M=len(R.vertices)
    alg=old.Segment(M,d,R,max(1,M-d),(4*d+4)*(max(1,M-d)+1))
    path=alg.between(start&end,start,end)
    require(c['refined_path']==[sorted(B) for B in path],'wrong refined combinatorial segment')
    ledger=old.ledger(path,M,d)
    require(ledger['nonrevisiting'] and len(path)-1<=M-d,'flag route violates proved count')
    out,stationary=project(R,path)
    require(c['path']==[sorted(B) for B in out],'wrong compressed carrier route')
    vp=audit_original(A,b,c['vertices'],out)
    require(vp[out[0]][0]==u and vp[out[-1]][0]==v,'original endpoints changed')
    L=len(out)-1
    require(all(F&H<=U for U in out),'route left the endpoints common original face')
    lock=start&end
    link_vertices=sum(R.ask(lock|{j}) for j in range(M) if j not in lock) if d>len(lock) else 0
    local_bound=link_vertices-(d-len(lock))
    require(len(path)-1<=local_bound,'flag link count failed')
    require(L+stationary==len(path)-1 and L<=M-d,'carrier contraction count failed')
    bound=sum(2**len(B)-1 for B in R.blocks)-d
    return {'status':'PASS','dimension':d,'original_facets':m,
        'block_sizes':[len(B) for B in R.blocks],'max_block_size':max(map(len,R.blocks)),
        'higher_minimal_nonfaces':sum(len(W)>=3 for W in missing),
        'refined_vertex_count':M,'block_face_counts':R.local_face_counts,
        'refined_edges':len(path)-1,'stationary_carrier_steps':stationary,
        'original_edges':L,'diameter_bound':M-d,'coarse_partition_bound':bound,
        'common_original_facets_preserved':sorted(F&H),'face_restricted_bound':local_bound,
        'original_reentry_debt':old.ledger(out,m,d)['reentry_debt'],
        'partition_condition_fully_checked':True,'original_intersection_certificates':len(O.cache),
        'refined_faces_queried':len(R.cache),'refined_link_graphs':len(alg.graphs),
        'original_graph_supplied':False,'refined_facets_enumerated':False,
        'scope':'Exact original-edge certificate; complete defect search may be exponential. No universal small-block guarantee.'}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--certificate',type=Path)
    ap.add_argument('--classification-cap',type=int,default=500000);args=ap.parse_args()
    try:
        data=json.loads(args.input.read_text())
        out=verify(data,json.loads(args.certificate.read_text())) if args.certificate else run(data,args.classification_cap)
        args.output.write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as e:
        ap.exit(2,f'No complete defect-block route certificate: {e}\n')
if __name__=='__main__':main()
