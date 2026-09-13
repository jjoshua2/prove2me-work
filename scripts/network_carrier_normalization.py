#!/usr/bin/env python3
"""Contract the actual endpoint face and remove redundant difference rows.

Every removed inequality has a nonnegative (all-ones) directed-path implication
certificate. No convex hull, approximate LP, or supplied Minkowski model is used.
The output routes the irredundant intrinsic model, then checks its original-H
lift. The recognition is for coordinate-difference rows (positive scaling okay).
"""
from __future__ import annotations
import argparse,heapq,json,hashlib
from pathlib import Path
from network_potential_router import Network,Q,construct,verify,rat,require,serial


def quotient(P):
    common=P.active(P.start)&P.active(P.target)
    labels=P.labels(common);reps=sorted(set(labels));number={r:i for i,r in enumerate(reps)}
    group=[number[r]for r in labels]
    offsets=[P.target[i]-P.target[labels[i]]for i in range(P.n)]
    arcs=[];origin=[];loops=[]
    for k,(a,b,c)in enumerate(P.arcs):
        bound=c-offsets[b]+offsets[a]
        if group[a]==group[b]:
            require(bound>=0,'inconsistent contracted loop');loops.append(k)
        else:arcs.append([group[a],group[b],bound]);origin.append(k)
    data={'nodes':len(reps),'arcs':arcs,'source':[P.start[i]for i in reps],'target':[P.target[i]for i in reps]}
    require(data['source'][0]==data['target'][0]==0,'quotient gauge')
    mid=[(x+y)/2 for x,y in zip(data['source'],data['target'])]
    require(all(mid[b]-mid[a]<c for a,b,c in arcs),'quotient lacks promised strict midpoint')
    return data,{'groups':group,'representatives':reps,'offsets':serial(offsets),'nonloop_original_rows':origin,'constant_rows':loops}


def alternative(arcs,active,skip,n,mid):
    r,s,_=arcs[skip];out=[[]for _ in range(n)]
    for k in active:
        if k!=skip:
            a,b,c=arcs[k];w=c-mid[b]+mid[a]
            require(w>0,'expected positive reduced costs')
            out[a].append((b,w,k))
    D={r:Q(0)};prev={};heap=[(Q(0),r)]
    while heap:
        d,a=heapq.heappop(heap)
        if D[a]!=d:continue
        if a==s:break
        for b,w,k in out[a]:
            nd=d+w
            if b not in D or nd<D[b]:D[b]=nd;prev[b]=(a,k);heapq.heappush(heap,(nd,b))
    if s not in D:return None
    path=[];b=s
    while b!=r:a,k=prev[b];path.append(k);b=a
    path.reverse();return path


def normalize_and_route(data):
    P=Network(data);reduced,meta=quotient(P)
    arcs=reduced['arcs'];n=reduced['nodes'];active=set(range(len(arcs)));removals=[]
    mid=[(x+y)/2 for x,y in zip(reduced['source'],reduced['target'])]
    for i in range(len(arcs)):
        path=alternative(arcs,active,i,n,mid)
        if path is not None and sum((arcs[k][2]for k in path),Q(0))<=arcs[i][2]:
            removals.append({'row':i,'path':path});active.remove(i)
    keep=sorted(active);minimal={**reduced,'arcs':[arcs[k]for k in keep]}
    result=construct(minimal)
    cert={'input_sha256':P.digest,'quotient':meta,'removals':removals,'retained_rows':keep,
          'pivot_certificate':result['certificate']}
    return {'certificate':cert,'verified':verify_normalized(data,cert)}


def verify_normalized(data,cert):
    P=Network(data);require(cert['input_sha256']==P.digest,'changed original network')
    reduced,meta=quotient(P);require(cert['quotient']==meta,'false quotient or affine offsets')
    arcs=reduced['arcs'];active=set(range(len(arcs)))
    for removal in cert['removals']:
        i=removal['row'];path=removal['path']
        require(type(i)is int and i in active,'invalid removed row')
        require(path and all(type(k)is int and k in active-{i}for k in path),'invalid implication path')
        r,s,c=arcs[i];at=r;total=Q(0)
        for k in path:
            a,b,v=arcs[k];require(a==at,'broken implication path');at=b;total+=v
        require(at==s and total<=c,'path does not imply removed inequality')
        active.remove(i)
    keep=cert['retained_rows'];require(keep==sorted(active),'forged final retained rows')
    # Minimality is checked independently by shortest-path tests. Soundness of
    # the route only needs implications; minimality is needed for calling M
    # the intrinsic facet count in the aggregate carrier-mass theorem.
    mid=[(x+y)/2 for x,y in zip(reduced['source'],reduced['target'])]
    for i in keep:
        path=alternative(arcs,active,i,reduced['nodes'],mid)
        require(path is None or sum((arcs[k][2]for k in path),Q(0))>arcs[i][2],
                'retained description is not irredundant')
    minimal={**reduced,'arcs':[arcs[k]for k in keep]}
    got=verify(minimal,cert['pivot_certificate'])
    off=list(map(rat,meta['offsets']));group=meta['groups'];route=[]
    common=P.active(P.start)&P.active(P.target)
    for z in got['route']:
        z=list(map(rat,z));x=tuple(z[group[i]]+off[i]for i in range(P.n))
        P.check_point(x);P.tree(P.active(x));require(common<=P.active(x),'lift left actual endpoint face');route.append(x)
    require(route[0]==P.start and route[-1]==P.target,'lift endpoints mismatch')
    for x,y in zip(route,route[1:]):
        require(len(set(P.labels(P.active(x)&P.active(y))))==2,'lifted step is not an original ordinary edge')
    h=reduced['nodes']-1;M=len(keep);delta=M-h
    require(delta>=0 and h<=delta and M<=2*delta,'intrinsic endpoint-carrier size bound')
    require(got['ordinary_edges']<=h*M,'intrinsic network budget failed')
    return {'status':'PASS','ordinary_edges':got['ordinary_edges'],'zero_pivots':got['zero_pivots'],
            'original_rows':P.m,'constant_rows':len(meta['constant_rows']),'nonconstant_rows':len(arcs),
            'removed_redundant_rows':len(cert['removals']),'intrinsic_dimension':h,'intrinsic_facets':M,
            'intrinsic_excess':delta,'h_times_M_bound':h*M,'dimension_bound':h*(h+1)*(h+2)//6,
            'route':serial(route),'scope':'Exact original H-face and implication certificates; not Lean or platform acceptance.'}



def balanced_H_coordinates(data):
    """Recover a positive diagonal chart from gain-consistent two-variable rows.
    For a_i*x_i+a_j*x_j<=b, demand a_i*s_i=-a_j*s_j. The ratio equations
    are solved by graph traversal and checked around EVERY cycle. A failed
    cycle is an unsupported model, not evidence about graph diameter.
    """
    A=[list(map(rat,r))for r in data['A']];b=list(map(rat,data['b']))
    require(A and A[0] and len(A)==len(b),'H input dimensions')
    d=len(A[0]);require(all(len(r)==d for r in A),'ragged H matrix')
    source=list(map(rat,data['source']));target=list(map(rat,data['target']))
    require(len(source)==len(target)==d,'H endpoint dimensions')
    adjacency=[[]for _ in range(d)]
    for row in A:
        nz=[(i,a)for i,a in enumerate(row)if a]
        require(len(nz)in (1,2),'unsupported H row: need one or two nonzeros')
        if len(nz)==2:
            (i,a),(j,c)=nz;require(a*c<0,'two-variable coefficients must have opposite signs')
            adjacency[i].append((j,-a/c));adjacency[j].append((i,-c/a))
    scale=[None]*d
    for root in range(d):
        if scale[root]is not None:continue
        scale[root]=Q(1);todo=[root]
        while todo:
            i=todo.pop()
            for j,ratio in adjacency[i]:
                value=scale[i]*ratio
                if scale[j]is None:scale[j]=value;todo.append(j)
                else:require(scale[j]==value,'inconsistent multiplicative gain cycle')
    arcs=[]
    for row,rhs in zip(A,b):
        nz=[(i+1,a*scale[i])for i,a in enumerate(row)if a]
        if len(nz)==1:
            i,a=nz[0];u,v=(0,i)if a>0 else(i,0);factor=abs(a)
        else:
            (i,a),(j,c)=nz;require(a+c==0,'recovered chart fails a row identity')
            u,v=(i,j)if a<0 else(j,i);factor=abs(a)
        arcs.append([u,v,rhs/factor])
    network={'nodes':d+1,'arcs':arcs,'source':[Q(0)]+[x/t for x,t in zip(source,scale)],
             'target':[Q(0)]+[x/t for x,t in zip(target,scale)]}
    raw={'A':A,'b':b,'source':source,'target':target}
    digest=hashlib.sha256(json.dumps(serial(raw),sort_keys=True,separators=(',',':')).encode()).hexdigest()
    return network,scale,digest


def construct_H(data):
    net,scale,digest=balanced_H_coordinates(data)
    out=normalize_and_route(net)
    cert={'H_sha256':digest,'diagonal_scale':serial(scale),'network_certificate':out['certificate']}
    return {'certificate':cert,'verified':verify_H(data,cert)}


def verify_H(data,cert):
    net,scale,digest=balanced_H_coordinates(data)
    require(cert['H_sha256']==digest and cert['diagonal_scale']==serial(scale),'H input or coordinate chart changed')
    out=verify_normalized(net,cert['network_certificate'])
    route=[[rat(x)*t for x,t in zip(y[1:],scale)]for y in out['route']]
    A=[list(map(rat,r))for r in data['A']];b=list(map(rat,data['b']))
    for x in route:
        require(all(sum((a*v for a,v in zip(row,x)),Q(0))<=rhs for row,rhs in zip(A,b)),
                'lifted diagonal-chart point fails an original H inequality')
    require(route[0]==list(map(rat,data['source'])) and route[-1]==list(map(rat,data['target'])),'changed H endpoints')
    return {**out,'route':serial(route),'diagonal_scale':serial(scale),'H_input_sha256':digest}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('input',type=Path)
    ap.add_argument('--certificate',type=Path);ap.add_argument('--output',type=Path);a=ap.parse_args()
    try:
        data=json.loads(a.input.read_text())
        out=(verify_H(data,json.loads(a.certificate.read_text()))if a.certificate else construct_H(data))if 'A'in data else (verify_normalized(data,json.loads(a.certificate.read_text()))if a.certificate else normalize_and_route(data))
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if a.output:a.output.write_text(text)
        else:print(text,end='')
    except(ValueError,KeyError,TypeError,IndexError,OSError)as e:ap.exit(2,f'Certificate rejected: {e}\n')
if __name__=='__main__':main()
