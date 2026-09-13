#!/usr/bin/env python3
"""Exact resonance-free normal-cone certificates for coherent gain blocks.

Every binary row is a directed potential inequality a*x_head-b*x_tail<=rhs,
a,b>0. Balanced blocks may be dense; isolated coherent cycles may have arbitrarily
near-balanced, unrelated gains. Coherent cycle orientations make their inverse blow-up cancel from a
normal-cone width witness. Input rows are not perturbed or deleted.

The structural certificate proves a bound for ALL nonsingular bases by the
companion graph argument. A separate rational verifier checks each supplied
cone witness without trusting that argument or the constructor. The reused
shadow sampler has no newly asserted polynomial pivot/runtime guarantee.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from collections import deque
from pathlib import Path
import hashlib,json
from gain_lattice_certificate import parse_rows,rat,dot,serial,require,gain_inverse


def digest(A):
    return hashlib.sha256(json.dumps(serial(A),separators=(',',':')).encode()).hexdigest()


class DSU:
    def __init__(self,n):self.p=list(range(n))
    def find(self,x):
        while self.p[x]!=x:self.p[x]=self.p[self.p[x]];x=self.p[x]
        return x
    def join(self,a,b):
        a,b=self.find(a),self.find(b)
        if a==b:return False
        self.p[a]=b;return True


def edges(A):
    """Use one representative per positive-proportional binary normal."""
    seen={};out={}
    for r,a in enumerate(A):
        nz=[i for i,v in enumerate(a)if v]
        if len(nz)<2:continue
        i,j=nz
        require(a[i]*a[j]<0,'binary coefficients are not opposite-signed')
        tail,head=(i,j)if a[i]<0 else(j,i)
        gain=-a[tail]/a[head];key=(tail,head,gain)
        if key not in seen:seen[key]=r;out[r]=(tail,head,gain)
    return out


def tree_path(G,start,end):
    parent={start:None};todo=deque([start])
    while todo and end not in parent:
        i=todo.popleft()
        for j,r in G[i]:
            if j not in parent:parent[j]=(i,r);todo.append(j)
    require(end in parent,'forest does not connect a chord')
    verts=[end];rows=[];v=end
    while v!=start:
        u,r=parent[v];rows.append(r);verts.append(u);v=u
    return verts[::-1],rows[::-1]


def forest_data(A):
    E=edges(A);d=len(A[0]);uf=DSU(d);F=[];chords=[];G=[[]for _ in range(d)]
    for r,(u,v,g)in E.items():
        if uf.join(u,v):F.append(r);G[u].append((v,r));G[v].append((u,r))
        else:chords.append(r)
    return E,F,chords,G


def forest_scale(d,E,F):
    G=[[]for _ in range(d)]
    for r in F:
        u,v,g=E[r];G[u].append((v,g));G[v].append((u,1/g))
    s=[None]*d
    for root in range(d):
        if s[root]is not None:continue
        s[root]=Q(1);todo=[root]
        while todo:
            u=todo.pop()
            for v,g in G[u]:
                if s[v]is None:s[v]=s[u]*g;todo.append(v)
    return s


def cycle_value(E,rs,vs):
    product=Q(1);coherent=True
    for r,u,v in zip(rs,vs,vs[1:]):
        x,y,g=E[r]
        require((u,v)in((x,y),(y,x)),'cycle row does not join its claimed vertices')
        if (u,v)==(x,y):product*=g
        else:product/=g;coherent=False
    return product,coherent


def certify_structure(Araw):
    A=parse_rows(Araw);d=len(A[0]);E,F,chords,G=forest_data(A);s=forest_scale(d,E,F)
    cycles=[]
    for r in chords:
        u,v,_=E[r];vs,rs=tree_path(G,v,u);rs.append(r);vs.append(v)
        cycles.append({'rows':rs,'vertices':vs})
    Gamma=Q(1)
    for item in cycles:
        g,_=cycle_value(E,item['rows'],item['vertices']);Gamma*=max(g,1/g)
    cert={'matrix_sha256':digest(A),'diagonal':s,'forest_rows':F,'cycles':cycles,'transport_product':Gamma}
    cert=serial(cert);return {'certificate':cert,'verified':verify_structure(Araw,cert)}


def verify_structure(Araw,c):
    """No forest-discovery or route-search call. Check every supplied cycle.

    Balanced fundamental cycles can overlap arbitrarily. Every unbalanced
    fundamental cycle must be coherently directed and edge-disjoint from ALL
    other fundamental cycles. Its block is therefore just that single cycle.
    """
    A=parse_rows(Araw);E=edges(A);d=len(A[0]);s=list(map(rat,c['diagonal']))
    require(c['matrix_sha256']==digest(A),'changed matrix')
    require(len(s)==d and all(x>0 for x in s),'invalid diagonal')
    F=c['forest_rows'];require(isinstance(F,list)and len(F)==len(set(F))and all(type(r)is int and r in E for r in F),'invalid forest rows')
    uf=DSU(d)
    for r in F:
        u,v,g=E[r];require(uf.join(u,v),'forest has a cycle');require(g*s[u]==s[v],'forest gain not normalized')
    require(all(uf.find(u)==uf.find(v)for u,v,_ in E.values()),'forest does not span the support components')
    chords=set(E)-set(F);covered=set();gains=[];rowsets=[]
    for item in c['cycles']:
        rs=item['rows'];vs=item['vertices']
        require(isinstance(rs,list)and len(rs)>=2 and len(rs)==len(set(rs)),'invalid cycle rows')
        require(all(type(r)is int and r in E for r in rs),'unknown cycle row')
        require(isinstance(vs,list)and len(vs)==len(rs)+1 and vs[0]==vs[-1]and len(set(vs[:-1]))==len(rs),'cycle not simple/closed')
        require(all(type(v)is int and 0<=v<d for v in vs),'invalid cycle vertex')
        ch=set(rs)&chords;require(len(ch)==1 and not(covered&ch),'not a fundamental-cycle cover')
        covered|=ch
        g,coherent=cycle_value(E,rs,vs)
        require(g==1 or coherent,'unbalanced cycle is not coherently directed')
        gains.append(g);rowsets.append(set(rs))
    require(covered==chords,'missing chord/cycle')
    for i,g in enumerate(gains):
        if g!=1:
            require(all(not(rowsets[i]&rows)for j,rows in enumerate(rowsets)if j!=i),
                    'unbalanced cycle overlaps another fundamental cycle')
    Gamma=Q(1)
    for g in gains:Gamma*=max(g,1/g)
    require(rat(c['transport_product'])==Gamma,'false transport product')
    return {'status':'PASS','dimension':d,'rows':len(A),'distinct_binary_normals':len(E),
            'directed_cycles':sum(g!=1 for g in gains),'balanced_fundamental_cycles':sum(g==1 for g in gains),
            'cycle_gains':list(map(str,gains)),'transport_product':str(Gamma),'bounded_transport':Gamma<=2,
            'normal_width_squared_lower':str(1/(4*Gamma**4*d**3)),
            'classical_cubic_bound':256*d**3 if Gamma<=2 else None,
            'scope':'Exact structural certificate; analytic diameter uses the cited wide-normal-cone theorem.'}


def normalized_rows(A,c):
    s=list(map(rat,c['diagonal']));out=[]
    for a in A:
        b=tuple(x*t for x,t in zip(a,s));m=max(map(abs,b),default=Q(0))or Q(1)
        out.append(tuple(x/m for x in b))
    return out


def cone_witness(Araw,structure,basis):
    A=parse_rows(Araw);info=verify_structure(A,structure);N=normalized_rows(A,structure);d=len(N[0])
    require(len(basis)==d and len(set(basis))==d and all(type(r)is int and 0<=r<len(A)for r in basis),'invalid basis')
    B=[N[r]for r in basis];inv,_=gain_inverse(B)
    E,F,chords,G=forest_data(B);s=forest_scale(d,E,F)
    uf=DSU(d)
    for u,v,_ in E.values():uf.join(u,v)
    parts={}
    for j in range(d):parts.setdefault(uf.find(j),[]).append(j)
    for ns in parts.values():
        small=min(s[i]for i in ns)
        for i in ns:s[i]/=small
    Gamma=rat(info['transport_product']);require(max(s)/min(s)<=Gamma,'basis tree gauge exceeds transport bound')
    alpha=[]
    for row in B:
        vals=tuple(x*t for x,t in zip(row,s));nz=[j for j,x in enumerate(vals)if x]
        require(nz,'zero basis row')
        m=vals[next(j for j in nz if vals[j]>0)] if len(nz)==2 else abs(vals[nz[0]])
        alpha.append(tuple(x/m for x in vals))
    center=[Q(0)]*d
    for ns in parts.values():
        node=set(ns);ids=[j for j,a in enumerate(B)if any(a[i]for i in ns)]
        bins=[j for j in ids if j in E];unary=[j for j in ids if j not in E]
        require(len(ids)==len(ns),'basis component not square')
        if unary:
            require(len(unary)==1 and len(bins)==len(ns)-1,'invalid tree/pin basis component')
            for j in ids:
                for i in ns:center[i]+=alpha[j][i]
        else:
            cs=[r for r in chords if E[r][0]in node];require(len(cs)==1,'invalid unicyclic basis component')
            closing=cs[0];u,v,_=E[closing];verts,rs=tree_path(G,v,u);rs.append(closing)
            require(all(E[r][:2]==(x,y)for r,x,y in zip(rs,verts+[v],(verts+[v])[1:])),'noncoherent basis cycle')
            gain=-alpha[closing][u];require(gain!=1,'balanced cycle in independent basis')
            require(max(1,gain)<=Gamma,'cycle magnitude exceeds transport product')
            summed=tuple(sum((alpha[r][i]for r in rs),Q(0))for i in range(d))
            require(summed==tuple((1-gain)*int(i==u)for i in range(d)),'cycle cancellation identity failed')
            center[u]+=1 if gain<1 else -1
            for j in ids:
                if j not in rs:
                    for i in ns:center[i]+=alpha[j][i]
    center=tuple(v/t for v,t in zip(center,s))
    width=1/(4*Gamma**4*d**3)
    c={'basis':list(basis),'center':center,'width_squared':width}
    c=serial(c);verify_cone(Araw,structure,c);return c


def verify_cone(Araw,structure,c):
    """Direct dual-frame inequalities, independent of the cycle-center construction."""
    A=parse_rows(Araw);info=verify_structure(A,structure);N=normalized_rows(A,structure);d=len(N[0]);Gamma=rat(info['transport_product'])
    ids=c['basis'];require(len(ids)==d and len(set(ids))==d and all(type(r)is int and 0<=r<len(A)for r in ids),'invalid cone basis')
    inv,_=gain_inverse([N[r]for r in ids]);center=tuple(map(rat,c['center']))
    require(len(center)==d and dot(center,center)>0,'zero/wrong cone center')
    w=rat(c['width_squared']);require(w==1/(4*Gamma**4*d**3),'false cone width')
    actual=[]
    for j in range(d):
        u=tuple(inv[i][j]for i in range(d));a=dot(u,center);uu=dot(u,u)
        require(a>0,'center not strictly inside basis normal cone')
        require(a*a>=w*uu*dot(center,center),'dual-frame ball inequality failed')
        actual.append(a*a/(uu*dot(center,center)))
    return {'minimum_verified_squared_margin':str(min(actual)),
            'largest_inverse_entry':str(max(abs(x)for row in inv for x in row)),
            'width_squared_lower':str(w)}


def construct_route(data):
    from gain_shadow_extension import construct,GainModel
    require('gain_base'not in data,'do not supply a gain lattice base to this resonance-free constructor')
    A=parse_rows(data['A']);structure=certify_structure(A)['certificate'];parent=verify_structure(A,structure)
    out=construct(data);model=GainModel(data);cert=out['certificate'];intrinsic=None;witnesses=[]
    if model.h:
        intrinsic=certify_structure(model.A)['certificate'];face=verify_structure(model.A,intrinsic)
        require(rat(face['transport_product'])<=rat(parent['transport_product']),'face contraction increases cycle transport')
        bases={tuple(cert['source_basis']),tuple(cert['target_basis']),tuple(cert['final_basis'])}
        bases|={tuple(s['basis'])for s in cert['basis_steps']}
        for B in sorted(bases):witnesses.append(cone_witness(model.A,intrinsic,B))
    packet={'structure':structure,'intrinsic_structure':intrinsic,'route_certificate':cert,'visited_cone_witnesses':witnesses}
    return {'certificate':packet,'verified':verify_route(data,packet)}


def verify_route(data,packet):
    from gain_shadow_extension import verify,GainModel
    parent=verify_structure(data['A'],packet['structure']);route=verify(data,packet['route_certificate']);model=GainModel(data,discover=False)
    if model.h:
        face=verify_structure(model.A,packet['intrinsic_structure'])
        require(rat(face['transport_product'])<=rat(parent['transport_product']),'invalid inherited transport')
        c=packet['route_certificate'];wanted={tuple(c['source_basis']),tuple(c['target_basis']),tuple(c['final_basis'])}
        wanted|={tuple(s['basis'])for s in c['basis_steps']}
        got=set();largest=Q(0);margin=None
        for w in packet['visited_cone_witnesses']:
            B=tuple(w['basis']);require(B not in got,'duplicate cone witness');got.add(B)
            v=verify_cone(model.A,packet['intrinsic_structure'],w);largest=max(largest,rat(v['largest_inverse_entry']))
            z=rat(v['minimum_verified_squared_margin']);margin=z if margin is None else min(margin,z)
        require(got==wanted,'missing/extra visited cone certificate')
        bound=256*model.h**3 if rat(face['transport_product'])<=2 else None
    else:
        require(packet['intrinsic_structure']is None and not packet['visited_cone_witnesses'],'spurious point cone witnesses')
        face=None;bound=0;largest=Q(0);margin=None
    return {'status':'PASS','dimension':model.d,'intrinsic_dimension':model.h,'rows':model.m,
            'edges':route['edges'],'basis_pivots':route['pivots'],'stationary_pivots':route['stationary_pivots'],
            'original_row_checks':route['row_checks'],'cycles':parent['directed_cycles'],'balanced_fundamental_cycles':parent['balanced_fundamental_cycles'],
            'transport_product':parent['transport_product'],'face_transport_product':None if face is None else face['transport_product'],
            'largest_visited_normalized_inverse':str(largest),'minimum_actual_squared_cone_margin':None if margin is None else str(margin),
            'classical_safe_diameter':bound,'sample_within_bound':None if bound is None else route['edges']<=bound,
            'scope':'Exact original-H edges and cone witnesses. Diameter existence uses a classical theorem; no sampler runtime guarantee.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path)
    p.add_argument('--certificate',type=Path);args=p.parse_args()
    try:
        data=json.loads(args.input.read_text());out=verify_route(data,json.loads(args.certificate.read_text()))if args.certificate else construct_route(data)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,TypeError,KeyError,ZeroDivisionError,OSError)as exc:p.exit(2,f'No certificate: {exc}\n')
if __name__=='__main__':main()
