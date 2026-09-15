#!/usr/bin/env python3
"""Complete ORIGINAL two-face exploration, not fixed-radius graph lookahead.

Input A,b,start,target is a simple bounded full-dimensional H-polytope. The
producer reconstructs every eligible two-face through each decision vertex;
all acquired target rows remain fixed. A complete polygon has at most m-d+2
edges. Its certificate verifies both incident directions at every vertex and
an injective original-row label on its edges. No ambient vertex graph is input.

Take the shortest first target-acquisition arc in the certified face union;
if none exists, choose a strictly phase-improving arc. Phases reset only at
acquisition. The number of fallback decisions is NOT proved polynomial.
Exact rational arithmetic and the old search-free original-row auditor are
used throughout; this is not Lean-extracted software or a nonsimple router.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from math import comb
from pathlib import Path
import argparse, hashlib, json
import simple_tangent_policy_audit as base

require, rat, serial, dot = base.require, base.rat, base.serial, base.dot


def parse(A,b,start,target):
    A=[[rat(z) for z in a] for a in A]; b=list(map(rat,b))
    x=list(map(rat,start)); y=list(map(rat,target))
    require(A and x and len(A)==len(b) and len(y)==len(x) and
            all(len(a)==len(x) for a in A),'wrong input dimensions')
    return A,b,x,y


def digest(A,b,x,y):
    return hashlib.sha256(json.dumps(serial([A,b,x,y]),separators=(',',':')).encode()).hexdigest()


def signature(A,b,anchor,x,T):
    return tuple(-Q(b[j]-dot(A[j],x))/(b[j]-dot(A[j],anchor))
                 for j in T if b[j]-dot(A[j],anchor)>0)


def phase_objective(A,b,x,target):
    y,T,_=base.audit_basis(A,b,target)
    J=sorted(set(base.active_rows(A,b,x)) & set(T))
    missing=[j for j in T if j not in J]
    require(missing,'no missing target row at a nonterminal phase')
    f=[sum((Q(A[j][k])/(b[j]-dot(A[j],x)) for j in missing),Q(0))
       for k in range(len(x))]
    require(dot(f,[v-u for u,v in zip(x,y)])==len(missing),'bad phase normalization')
    return f,J


def neighbors(A,b,bs,locked):
    """Arithmetic auditor computes ALL allowed ray endpoints from stored columns."""
    x,J,D=base.audit_basis(A,b,bs)
    require(set(locked)<=set(J),'locked equalities are not active')
    out=[]
    for k,row in enumerate(J):
        if row in locked: continue
        length,blocker=base.maximal_step(A,b,x,D[k])
        require(length>0,'zero step in a purported simple model')
        z=[u+length*v for u,v in zip(x,D[k])]
        K=base.active_rows(A,b,z)
        require(base.feasible(A,b,z) and len(K)==len(x),'non-simple or infeasible endpoint')
        require(set(J)-{row}<=set(K) and row not in K,'not an ordinary adjacent endpoint')
        out.append({'selected':k,'released':row,'length':length,'blocker':blocker,'to':z})
    return out


def trace_face(A,b,source,fixed,basis_cache):
    """Producer traces one polygon once, starting with the smaller released row."""
    d=len(source); bound=len(A)-d+2
    def packet(x):
        key=tuple(x)
        if key not in basis_cache: basis_cache[key]=base.basis_packet(A,b,x)
        return basis_cache[key]
    x=list(source); previous=None; visited=set(); corners=[]
    for _ in range(bound):
        require(tuple(x) not in visited,'two-face repeats before its closure')
        visited.add(tuple(x)); bs=packet(x); corners.append(bs)
        choices=neighbors(A,b,bs,fixed)
        require(len(choices)==2,'two-face must have two tangent rays')
        if previous is None: nxt=choices[0]['to']
        else:
            forward=[o for o in choices if o['to']!=previous]
            require(len(forward)==1,'previous vertex not the other face neighbor')
            nxt=forward[0]['to']
        if nxt==list(source):
            require(len(corners)>=3,'two-face polygon has fewer than three corners')
            cert={'fixed_rows':list(fixed),'corners':corners}
            return cert  # The containing decision is audited before commitment.
        previous,x=x,nxt
    raise ValueError('two-face exceeded original-row bound or failed to close')


def audit_face(A,b,source,fixed,cert):
    """No inverse, LP, rank, polygon constructor or whole-graph oracle."""
    d=len(source); bound=len(A)-d+2
    require(type(cert['fixed_rows']) is list and all(type(i) is int for i in cert['fixed_rows']) and
            cert['fixed_rows']==list(fixed) and len(set(fixed))==d-2,'incorrect face labels')
    C=cert['corners'];q=len(C)
    require(3<=q<=bound,'polygon length outside original-facet bound')
    require(C[0]['point']==list(source),'face starts at wrong decision point')
    V=[tuple(c['point']) for c in C]
    require(len(set(V))==q,'repeated face vertex')
    active=[]; outgoing=[]
    for j,bs in enumerate(C):
        x,J,_=base.audit_basis(A,b,bs);active.append(set(J))
        options=neighbors(A,b,bs,fixed)
        require(len(options)==2 and {tuple(o['to']) for o in options}==
                {V[(j-1)%q],V[(j+1)%q]},'incomplete or false two-face boundary')
        if j==0: require(tuple(options[0]['to'])==V[1],'noncanonical face orientation')
        outgoing.append(next(o for o in options if tuple(o['to'])==V[(j+1)%q]))
    labels=[]
    for j in range(q):
        common=active[j]&active[(j+1)%q]
        require(len(common)==d-1 and set(fixed)<=common,'edge lacks original common face rows')
        label=common-set(fixed)
        require(len(label)==1,'edge needs exactly one additional original support row')
        labels.append(next(iter(label)))
    require(len(set(labels))==q,'same original inequality labels two polygon edges')
    return {'vertices':V,'labels':labels,'forward':outgoing,'edge_bound':bound}


def first_hit_paths(A,b,f,target,root,face):
    T=set(target['active']);J=set(base.active_rows(A,b,root))&T
    C=face['corners'];q=len(C);arcs=[];improving=[]
    for sign in (1,-1):
        path=[]; last=root; monotone=True
        for t in range(1,q):
            k=(sign*t)%q; z=C[k]['point'];path.append(z)
            gain=dot(f,[v-u for u,v in zip(last,z)])
            monotone=monotone and gain>0
            if monotone: improving.append({'kind':'face_gain','fixed_rows':face['fixed_rows'],
                'sign':sign,'count':t,'path':list(path)})
            if (set(base.active_rows(A,b,z))&T)-J:
                arcs.append({'kind':'face_acquisition','fixed_rows':face['fixed_rows'],
                             'sign':sign,'count':t,'path':list(path)})
                break
            last=z
    return arcs,improving


def choose(A,b,f,target,root,opts,faces):
    T=target['active'];current=set(base.active_rows(A,b,root))&set(T)
    direct=[o for o in opts if (set(base.active_rows(A,b,o['to']))&set(T))-current]
    def quality(path):
        end=path[-1]
        return (dot(f,[v-u for u,v in zip(root,end)]),signature(A,b,root,end,T),
                tuple(signature(A,b,root,z,T) for z in path))
    if direct:
        o=max(direct,key=lambda o:quality([o['to']]))
        return {'kind':'edge_acquisition','selected':o['selected'],'path':[o['to']]}
    acquisition=[];gain=[]
    for face in faces:
        a,g=first_hit_paths(A,b,f,target,root,face);acquisition+=a;gain+=g
    if acquisition:
        return max(acquisition,key=lambda o:(-len(o['path']),)+quality(o['path']))
    # The exact target tangent decomposition guarantees at least one positive
    # one-edge direction, which belongs to an enumerated face if h>=2.
    require(gain,'no positive face arc in the retained target face')
    return max(gain,key=lambda o:(quality(o['path'])[0],-len(o['path']))+quality(o['path'])[1:])


def selection_only(o):
    return {k:v for k,v in o.items() if k!='path'}


def produce_decision(A,b,f,target,root,cache):
    if tuple(root) not in cache:cache[tuple(root)]=base.basis_packet(A,b,root)
    bs=cache[tuple(root)];T=set(target['active']);locked=sorted(set(bs['active'])&T)
    opts=neighbors(A,b,bs,locked)
    require(opts,'nonterminal vertex has no allowed tangent edge')
    free=[j for j in bs['active'] if j not in locked]
    immediate=any((set(base.active_rows(A,b,o['to']))&T)-set(locked) for o in opts)
    faces=[]
    if not immediate:
        require(len(free)>=2,'one-dimensional retained face failed to reach target')
        for i,j in combinations(free,2):
            fixed=[r for r in bs['active'] if r not in (i,j)]
            faces.append(trace_face(A,b,root,fixed,cache))
    result={'basis':bs,'faces':faces,'selection':selection_only(choose(A,b,f,target,root,opts,faces))}
    return result  # construct() audits the entire candidate collection.


def audit_decision(A,b,f,target,cert):
    root,J,D=base.audit_basis(A,b,cert['basis']);y,T,_=base.audit_basis(A,b,target)
    locked=sorted(set(J)&set(T));opts=neighbors(A,b,cert['basis'],locked)
    require(opts and dot(f,[v-u for u,v in zip(root,y)])>0,'phase objective not strict at current point')
    weights=[b[j]-dot(A[j],y) for j in J]
    require(all(w>=0 for w in weights) and
        all(y[k]-root[k]==sum(w*v[k] for w,v in zip(weights,D)) for k in range(len(root))),
        'false target tangent decomposition')
    require(any(dot(f,[v-u for u,v in zip(root,o['to'])])>0 for o in opts),
            'no improving eligible original edge')
    immediate=any((set(base.active_rows(A,b,o['to']))&set(T))-set(locked) for o in opts)
    free=[j for j in J if j not in locked]
    expected=[] if immediate else [[r for r in J if r not in (i,j)] for i,j in combinations(free,2)]
    require(len(cert['faces'])==len(expected),'omitted or extra eligible two-face')
    edge_counts=[]
    for fixed,face in zip(expected,cert['faces']):
        report=audit_face(A,b,root,fixed,face);edge_counts.append(len(report['vertices']))
    choice=choose(A,b,f,target,root,opts,cert['faces'])
    require(type(cert['selection']) is dict and all(type(v) is int for k,v in cert['selection'].items()
        if k in ('selected','sign','count')) and cert['selection']==selection_only(choice),
        'incorrect acquisition or improvement selection')
    path=choice['path'];end=path[-1]
    acquired=sorted((set(base.active_rows(A,b,end))&set(T))-set(locked))
    require(bool(acquired)==(choice['kind']!='face_gain'),'wrong phase-ending classification')
    cap=len(A)-len(root)+2
    require(len(path)<= (cap//2 if acquired else cap-1),'face macro exceeds its facet-count bound')
    require(not any((set(base.active_rows(A,b,z))&set(T))-set(locked) for z in path[:-1]),
            'macro did not stop at its first target acquisition')
    require(all(set(locked)<=set(base.active_rows(A,b,z)) for z in path),'macro releases locked target facet')
    if not acquired:
        require(all(dot(f,[v-u for u,v in zip(x,z)])>0
                    for x,z in zip([root]+path[:-1],path)),'fallback arc is not strictly improving')
    return path,{'kind':choice['kind'],'acquired':acquired,'faces':len(edge_counts),
        'traced_face_edges':sum(edge_counts),'largest_face':max(edge_counts,default=0),
        'candidate_vertex_occurrences':len(opts)+sum(edge_counts),
        'old_phase_decreasing_steps':sum(dot(f,[v-u for u,v in zip(x,z)])<0
            for x,z in zip([root]+path[:-1],path))}


def construct(A,b,start,target,edge_cap=10000):
    A,b,start,target=parse(A,b,start,target)
    require(type(edge_cap)is int and edge_cap>=0,'invalid edge cap')
    target_bs=base.basis_packet(A,b,target);x=list(start);cache={};phases=[];count=0
    while x!=target:
        f,locked=phase_objective(A,b,x,target_bs)
        p={'anchor':list(x),'objective':f,'locked':locked,'decisions':[]}
        while x!=target:
            require(count<edge_cap,'route cap: no completion claimed')
            c=produce_decision(A,b,f,target_bs,x,cache)
            arc,info=audit_decision(A,b,f,target_bs,c)
            require(count+len(arc)<=edge_cap,'route cap before committing complete arc')
            p['decisions'].append(c);count+=len(arc);x=arc[-1]
            if info['acquired']:break
        phases.append(p)
    cert={'format':'complete-two-face-v1','problem_sha256':digest(A,b,start,target),
          'target_basis':target_bs,'phases':phases}
    return {'certificate':cert,'verified':verify(A,b,start,target,cert)}


def loop_erase(path):
    out=[];where={}
    for p in path:
        t=tuple(p)
        if t in where:
            cut=where[t]
            for z in out[cut+1:]:where.pop(tuple(z))
            out=out[:cut+1]
        else:where[t]=len(out);out.append(p)
    return out


def verify(A,b,start,target,c):
    A,b,start,target=parse(A,b,start,target)
    require(c['format']=='complete-two-face-v1' and c['problem_sha256']==digest(A,b,start,target),'changed problem')
    bs=c['target_basis'];y,T,_=base.audit_basis(A,b,bs);require(y==target,'wrong target basis')
    x=start;path=[start];totals={'decisions':0,'acquisition_decisions':0,'fallback_decisions':0,
       'faces':0,'traced_face_edges':0,'largest_face':0,'candidate_vertex_occurrences':0,
       'old_phase_decreasing_steps':0,'retired_improving_faces':0};phase_counts=[];anchors=set();retired=set();phase_bounds=[]
    initial=len(set(base.active_rows(A,b,start))&set(T))
    for phase in c['phases']:
        require(phase['anchor']==x and phase['decisions'],'wrong or empty phase')
        f,locked=phase_objective(A,b,x,bs)
        require(all(type(z) in (int,Q) for z in phase['objective']) and
                phase['objective']==f and phase['locked']==locked,'phase objective/locking changed')
        count=0;phase_fallbacks=0;h=len(start)-len(locked)
        for i,dc in enumerate(phase['decisions']):
            require(tuple(x) not in anchors,'repeated decision anchor');anchors.add(tuple(x))
            require(dc['basis']['point']==x,'discontinuous decision')
            arc,info=audit_decision(A,b,f,bs,dc)
            require(bool(info['acquired'])==(i==len(phase['decisions'])-1),'phase did not end at first acquisition')
            totals['decisions']+=1;totals['acquisition_decisions']+=bool(info['acquired'])
            totals['fallback_decisions']+=not info['acquired']
            if not info['acquired']:
                require(h>=3,'the complete two-dimensional target face must have an acquisition')
                improving=[face for face in dc['faces'] if
                    max(dot(f,bs['point']) for bs in face['corners'])>dot(f,x)]
                labels=[tuple(face['fixed_rows']) for face in improving]
                require(len(labels)>=h-1 and not(set(labels)&retired),
                        'improving-face retirement is missing or reused')
                require(all(max(dot(f,bs['point']) for bs in face['corners'])<=dot(f,arc[-1])
                    for face in dc['faces']),'fallback did not dominate all inspected face maxima')
                retired.update(labels);totals['retired_improving_faces']+=len(labels);phase_fallbacks+=1
            for key in ['faces','traced_face_edges','candidate_vertex_occurrences','old_phase_decreasing_steps']:
                totals[key]+=info[key]
            totals['largest_face']=max(totals['largest_face'],info['largest_face'])
            path+=arc;count+=len(arc);x=arc[-1]
        phase_counts.append(count)
        upper=comb(len(A)-len(start),h-2)//(h-1) if h>=3 else 0
        require(phase_fallbacks<=upper,'original non-target row subset budget failed')
        phase_bounds.append({'intrinsic_dimension':h,'fallback_decisions':phase_fallbacks,'facet_subset_upper_bound':upper})
    require(x==target and len(phase_counts)<=len(start)-initial,'target or acquisition bound failed')
    short=loop_erase(path)
    cap=len(A)-len(start)+2
    r=len(start)-initial;e=len(A)-len(start)
    accounted=r*(cap//2)+totals['fallback_decisions']*(cap-1)
    combinatorial=r*(cap//2)+sum(comb(e+1,j) for j in range(2,r))
    require(len(path)-1<=combinatorial,'explicit binomial route bound failed')
    require(len(path)-1<=accounted,'macro accounting bound failed')
    return {'status':'PASS','dimension':len(start),'input_rows':len(A),'committed_edges':len(path)-1,
        'loop_erased_edges':len(short)-1,'bound_using_audited_fallback_count':accounted,
        'original_facet_binomial_route_bound':combinatorial,'phase_fallback_bounds':phase_bounds,'phase_edges':phase_counts,'path':path,'loop_erased_path':short,
        **totals,'each_face_edge_bound':len(A)-len(start)+2,
        'ambient_graph_supplied':False,'ambient_graph_precomputed':False,'universal_polynomial_route_bound':False,
        'scope':'Exact original-H two-face coverage and route. Simple bounded class; binomial fallback accounting, not a uniform polynomial bound. Not Lean verification.'}


def decode(c):
    if 'certificate' in c:c=c['certificate']
    # Convert rational strings only; labels and counts remain actual integers.
    def basis(b):return {'point':list(map(rat,b['point'])),'active':b['active'],
                         'directions':[list(map(rat,d)) for d in b['directions']]}
    out={'format':c['format'],'problem_sha256':c['problem_sha256'],'target_basis':basis(c['target_basis']),'phases':[]}
    for p in c['phases']:
        q={'anchor':list(map(rat,p['anchor'])),'objective':list(map(rat,p['objective'])),
           'locked':p['locked'],'decisions':[]}
        for r in p['decisions']:
            q['decisions'].append({'basis':basis(r['basis']),'selection':r['selection'],
                'faces':[{'fixed_rows':f['fixed_rows'],'corners':[basis(b) for b in f['corners']]} for f in r['faces']]})
        out['phases'].append(q)
    return out


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--certificate',type=Path);p.add_argument('--edge-cap',type=int,default=10000);args=p.parse_args()
    try:
        d=json.loads(args.input.read_text());A,b,x,y=parse(d['A'],d['b'],d['start'],d['target'])
        out={'certificate':decode(json.loads(args.certificate.read_text()))} if args.certificate else construct(A,b,x,y,args.edge_cap)
        out['verified']=verify(A,b,x,y,out['certificate'])
        args.output.write_text(json.dumps(serial(out),indent=2)+'\n')
    except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No complete two-face route: {exc}\n')
if __name__=='__main__':main()
