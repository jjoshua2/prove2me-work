#!/usr/bin/env python3
"""Count ORIGINAL route vertices after deleting the unlocked target rows.

Consumes an unchanged #253 certificate. No new route, LP, inverse, or graph
search is used in audit. The cyclic-polytope bound invokes the classical Upper
Bound Theorem via the accompanying written proof, not a Lean-verified library.
Simplicity, boundedness and full dimension are the original route's input class.
"""
from __future__ import annotations
from math import comb
from pathlib import Path
import argparse, json
import two_face_acquisition as route
import simple_tangent_policy_audit as base
Q, require, dot = base.Q, base.require, base.dot


def cyclic_vertices(facets: int, dimension: int) -> int:
    """Maximal vertices of a dimension-polytope with at most facets facets."""
    require(type(facets) is int and type(dimension) is int and 1 <= dimension < facets,
            'invalid upper-bound parameters')
    k = dimension // 2
    if dimension % 2:
        return 2 * comb(facets-k-1, k)
    return comb(facets-k, k) + comb(facets-k-1, k-1)


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n): a, b = b, a+b
    return a


def global_bound(excess: int, missing: int) -> int:
    require(type(excess) is int and type(missing) is int and 0 <= missing <= excess,
            'missing target facets exceed original excess')
    if missing <= 1: return missing
    # On the last retained polygon the unchanged rule is shortest, INCLUDING
    # its final edge in the one-dimensional phase.
    return (excess+2)//2 + sum(cyclic_vertices(excess+1,h) for h in range(3,missing+1))


def _basis_index(certificate):
    packets = [certificate['target_basis']]
    for phase in certificate['phases']:
        for dc in phase['decisions']:
            packets.append(dc['basis'])
            for face in dc['faces']: packets.extend(face['corners'])
    out = {}
    for packet in packets:
        key = tuple(packet['point'])
        if key in out: require(out[key] == packet, 'inconsistent repeated original basis')
        out[key] = packet
    return out


def _phase_path(A,b,target,phase):
    path = [phase['anchor']]
    for dc in phase['decisions']:
        arc,_ = route.audit_decision(A,b,phase['objective'],target,dc)
        path.extend(arc)
    return path


def _cell(A,b,T,phase,path,bases):
    anchor,J,D = base.audit_basis(A,b,bases[tuple(phase['anchor'])])
    locked = phase['locked']; N = [j for j in range(len(A)) if j not in T]
    free = [j for j in J if j not in locked]
    columns = [D[J.index(j)] for j in free]; h = len(free)
    C = [[dot(A[j],v) for v in columns] for j in N]
    rhs = [b[j]-dot(A[j],anchor) for j in N]
    coordinates = [[b[j]-dot(A[j],x) for j in free] for x in path[:-1]]
    R = 1 + max((sum(z) for z in coordinates), default=Q(0))
    return {'locked':locked, 'non_target_rows':N, 'free_origin_rows':free,
        'columns':columns, 'inequalities':C, 'rhs':rhs,
        'cap':R, 'cap_row':[Q(1)]*h, 'vertices':path[:-1],
        'coordinates':coordinates, 'phase_endpoint':path[-1]}


def produce(A,b,u,v,certificate):
    """Only serializes coordinates from an ALREADY verified route."""
    route.verify(A,b,u,v,certificate)
    bases = _basis_index(certificate); T = certificate['target_basis']['active']
    cells = []
    for phase in certificate['phases']:
        path = route.loop_erase(_phase_path(A,b,certificate['target_basis'],phase))
        cells.append(_cell(A,b,T,phase,path,bases))
    return {'format':'target-deleted-phase-v1', 'problem_sha256':route.digest(A,b,u,v), 'cells':cells}


def audit(A,b,u,v,certificate,account):
    """Search-free exact checks of cap geometry and UBT count transport.

    No image projection: original edges are verified by #253, and caps are
    used ONLY to count their distinct original pre-acquisition vertices.
    """
    checked = route.verify(A,b,u,v,certificate)
    require(account['format']=='target-deleted-phase-v1' and
        account['problem_sha256']==route.digest(A,b,u,v), 'account bound to different input')
    d=len(u); e=len(A)-d; T=certificate['target_basis']['active']; bases=_basis_index(certificate)
    require(len(account['cells'])==len(certificate['phases']), 'missing phase')
    records=[]; joined=[u]; cap_checks=rank_checks=0
    for phase,cell in zip(certificate['phases'],account['cells']):
        raw = _phase_path(A,b,certificate['target_basis'],phase)
        path = route.loop_erase(raw)
        require(cell==_cell(A,b,T,phase,path,bases), 'changed deletion, cap, chart or loop-erased route')
        locked=set(cell['locked']); N=cell['non_target_rows']; h=d-len(locked)
        require(1<=h<=e and set(locked)<=set(T) and len(N)==e, 'incorrect retained dimension or row count')
        anchor=phase['anchor']; free=cell['free_origin_rows']; columns=cell['columns']
        C,rhs,R=cell['inequalities'],cell['rhs'],cell['cap']
        require(len(free)==h and set(free).isdisjoint(T) and R>0,'invalid phase chart')
        for i,j in enumerate(free):
            row=C[N.index(j)]; require(row==[-Q(i==k) for k in range(h)] and rhs[N.index(j)]==0,
                'missing nonnegative coordinate row')
        # Small positive coordinates give a STRICT point of the deleted capped
        # system. This certifies full dimension, not just a local vertex count.
        delta=R/(2*h)
        for row,t,j in zip(C,rhs,N):
            if j in free: continue
            require(t>0, 'nonactive original row not strictly slack at phase anchor')
            if sum(row)>0: delta=min(delta,t/(2*sum(row)))
        interior=[delta]*h
        require(delta>0 and sum(interior)<R and all(dot(row,interior)<t for row,t in zip(C,rhs)),
                'deleted capped polytope lacks the claimed strict interior')
        for x,z in zip(cell['vertices'],cell['coordinates']):
            xp,active,Dx=base.audit_basis(A,b,bases[tuple(x)])
            require(set(active)&set(T)==locked, 'a supposedly pre-acquisition vertex touches a new target facet')
            require(all(a>=0 for a in z) and sum(z)<R and all(dot(row,z)<=t for row,t in zip(C,rhs)),
                    'vertex lost or cap not strict')
            require(all(x[k]==anchor[k]+sum(z[i]*columns[i][k] for i in range(h)) for k in range(d)),
                    'affine chart does not reconstruct original point')
            # Invertibility of its h active NON-target rows in the phase chart:
            # coordinate-map applied to the original stored inverse columns.
            K=[j for j in active if j not in locked]
            E=[[-dot(A[j],Dx[active.index(k)]) for j in free] for k in K]
            require(len(K)==h, 'wrong target-deleted active rank')
            for i,k in enumerate(K):
                for j,ell in enumerate(K):
                    require(dot(C[N.index(ell)],E[i])==-int(i==j), 'false restricted original-row inverse')
                    rank_checks+=1
            cap_checks+=1
        bound=cyclic_vertices(e+1,h)
        require(len(path)-1==len(cell['vertices'])<=bound, 'phase exceeds cyclic-polytope vertex bound')
        require(joined[-1]==path[0], 'phase paths do not concatenate')
        joined.extend(path[1:])
        records.append({'retained_dimension':h,'raw_edges':len(raw)-1,
            'loop_erased_edges':len(path)-1,'capped_facets_at_most':e+1,
            'cyclic_vertex_bound':bound,'cap':str(R),'strict_interior_delta':str(delta)})
    require(joined==checked['loop_erased_path'], 'phase erasure differs from original global loop erasure')
    require(len({tuple(x)for x in joined})==len(joined), 'repeated vertex across target-locking phases')
    r=d-len(set(base.active_rows(A,b,u))&set(T)); total=global_bound(e,r)
    tail=sum(x['loop_erased_edges']for x in records if x['retained_dimension']<=2)
    require(tail<=((e+2)//2 if r>=2 else r),'last polygon route not shortest')
    require(len(joined)-1<=total,'new full route bound failed')
    old=sum(comb(e+1,j)for j in range(2,r))+r*((e+2)//2)
    return {'status':'PASS','original_dimension':d,'original_rows':len(A),'facet_excess':e,
        'missing_target_facets':r,'original_raw_edges':checked['committed_edges'],
        'certified_loop_erased_edges':len(joined)-1,'new_cyclic_phase_bound':total,
        'old_subset_bound':old,'distinct_original_vertices_checked':cap_checks,
        'restricted_inverse_identities':rank_checks,'phases':records,
        'scope':'Original simple bounded H-polytopes; classical UBT invoked in written proof. No Lean, shortest-route, or polynomial all-dimensional guarantee.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('route',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    try:
        inp=json.loads(a.input.read_text());A,b,u,v=route.parse(inp['A'],inp['b'],inp['start'],inp['target'])
        cert=route.decode(json.loads(a.route.read_text()));acc=produce(A,b,u,v,cert)
        a.output.write_text(json.dumps(base.serial({'account':acc,'verified':audit(A,b,u,v,cert,acc)}),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No checked target-deletion account: {exc}\n')
if __name__=='__main__':main()
