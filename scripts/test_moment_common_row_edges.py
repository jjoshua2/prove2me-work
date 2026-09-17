#!/usr/bin/env python3
"""Exact supporting checks for the moment common-row edge proof.
No Lean compilation is performed. Small references use independent SymPy exact
elimination; the certificate consumer uses original rational row evaluations.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
from itertools import combinations
from copy import deepcopy
import json, hashlib, random
import sympy as sp

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'research/publication_packets/moment_common_row_edges'

def require(ok,msg):
    if not ok: raise ValueError(msg)

def rat(x):
    require(type(x) in (int,str,Q),'exact rational input; no floats or booleans')
    return Q(x)

def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x

def row_matrix(d,a):
    require(type(d)is int and 0<=d<len(a),'dimension must be below original row count')
    a=list(map(rat,a));m=len(a)
    return [[t**j-sum(s**j for s in a)/m for j in range(1,d+1)] for t in a]

def dot(a,x):
    require(len(a)==len(x),'dimensions differ')
    return sum((c*z for c,z in zip(a,x)),Q(0))

def tight(A,x):return frozenset(i for i,r in enumerate(A) if dot(r,x)==1)
def feasible(A,x):return all(dot(r,x)<=1 for r in A)

def binding(d,a,u,v):
    return hashlib.sha256(json.dumps(serial([d,a,u,v]),separators=(',',':')).encode()).hexdigest()

def produce(d,a,u,v):
    a=list(map(rat,a));u=list(map(rat,u));v=list(map(rat,v));A=row_matrix(d,a)
    require(len(set(a))==len(a),'parameters not injective')
    I,J=tight(A,u),tight(A,v);C=I&J
    require(len(u)==len(v)==d and feasible(A,u) and feasible(A,v),'infeasible or wrong endpoint')
    require(len(I)==len(J)==d and len(C)+1==d,'not the cardinality premise')
    r=min(I-J);q=min(J-I)
    return {'dimension':d,'parameters':a,'source':u,'target':v,'source_active':sorted(I),
            'target_active':sorted(J),'common':sorted(C),'source_private':r,'target_private':q,
            'objective':[sum(A[i][j] for i in C) for j in range(d)],'maximum':Q(len(C)),
            'binding':binding(d,a,u,v)}

def verify(c):
    d=c['dimension'];a=list(map(rat,c['parameters']));u=list(map(rat,c['source']));v=list(map(rat,c['target']))
    require(len(set(a))==len(a),'noninjective parameter map')
    A=row_matrix(d,a);require(len(u)==len(v)==d,'endpoint dimension')
    require(binding(d,a,u,v)==c['binding'],'input binding')
    require(feasible(A,u) and feasible(A,v),'endpoint feasibility')
    I,J=tight(A,u),tight(A,v);C=I&J
    require(len(I)==len(J)==d and len(C)+1==d and u!=v,'missing actual edge hypotheses')
    require(c['source_active']==sorted(I) and c['target_active']==sorted(J) and c['common']==sorted(C),'wrong exact active sets')
    r,q=c['source_private'],c['target_private']
    require(type(r)is int and type(q)is int and r in I-J and q in J-I,'wrong private labels')
    require(list(map(rat,c['objective']))==[sum(A[i][j] for i in C) for j in range(d)] and rat(c['maximum'])==len(C),'not original-row objective')
    den=1-dot(A[r],v);gap=1-dot(A[q],u)
    require(den>0 and gap>0,'private row not strictly slack at other endpoint')
    interior=outside=evals=0
    for t in map(Q,[-2,'-1/2',0,'1/7','1/3','1/2','5/6',1,'3/2',3]):
        x=[(1-t)*ui+t*vi for ui,vi in zip(u,v)]
        require((1-dot(A[r],x))/den==t,'parameter recovery failed')
        require(dot(A[q],x)==dot(A[q],u)+t*gap,'upper-bound private-row identity')
        require(feasible(A,x)==(0<=t<=1),'feasible line exceeds claimed edge endpoints')
        require(all(dot(A[i],x)==1 for i in C),'shared slice left')
        require(dot(list(map(rat,c['objective'])),x)==len(C),'support value changed along affine line')
        if 0<t<1:require(tight(A,x)==C,'unexpected interior active row');interior+=1
        if t<0 or t>1:outside+=1
        evals+=len(A)
    return {'status':'PASS','dimension':d,'original_rows':len(a),'common_rows':len(C),
            'interior_points':interior,'outside_segment_rejections':outside,'original_row_evaluations':evals,
            'zero_objective_dimension_one':d==1 and all(rat(x)==0 for x in c['objective'])}

def reference(d,a):
    A=row_matrix(d,a);V={};allpoints=[];systems=0
    for I in combinations(range(len(a)),d):
        M=sp.Matrix([A[i] for i in I]);systems+=1
        if M.det()==0:continue
        x=tuple(Q(str(t)) for t in M.inv()*sp.ones(d,1));allpoints.append(x)
        if feasible(A,x):V[x]=tight(A,x)
    require(V,'no original vertices')
    return A,V,allpoints,systems

def root_vertex(d,a,F):
    p=[Q(1)]
    for i in sorted(F):
        out=[Q(0)]*(len(p)+1)
        for j,c in enumerate(p):out[j]-=a[i]*c;out[j+1]+=c
        p=out
    vals=[sum(c*t**j for j,c in enumerate(p)) for t in a]
    if all(x<=0 for x in vals):p=[-x for x in p];vals=[-x for x in vals]
    require(all(x>=0 and (x==0)==(i in F) for i,x in enumerate(vals)),'not an exposing root polynomial')
    h=sum(vals)/len(a);return [-p[j]/h for j in range(1,d+1)]

def main():
    rng=random.Random(294);reports=[];saved=[];negatives=[];examples=[]
    totals={'models':0,'active_square_systems':0,'reference_vertices':0,'reference_edges':0,
            'adjacent_pairs_checked':0,'nonadjacent_pairs_checked':0,'extra_maximizers_on_diagonals':0,
            'original_row_evaluations':0,'interior_points':0,'outside_segment_rejections':0,
            'infeasible_full_tight_points':0,'support_objective_vertex_evaluations':0}
    for d,m in [(1,3),(2,5),(2,7),(3,6),(3,8),(4,7),(4,9),(5,8),(6,9)]:
        a=[Q(i**3+2*i-9,5) for i in range(m)];rng.shuffle(a)
        A,V,allpts,systems=reference(d,a)
        require(all(len(I)==d for I in V.values()),'unexpected nonsimple reference')
        require(sp.Matrix(A).rank()==d and all(sum(r[j] for r in A)==0 for j in range(d)),
                'missing spanning and positive-centering boundedness condition')
        edges=nonedges=excess=0
        for u,v in combinations(V,2):
            I,J=V[u],V[v];C=I&J
            # Rank here uses independent SymPy, not merely cardinality.
            rank=sp.Matrix([A[i] for i in C]).rank() if C else 0
            require(rank==len(C),'common moment rows not independent')
            obj=[sum(A[i][j] for i in C) for j in range(d)]
            maximizers=[x for x in V if dot(obj,x)==len(C)]
            require(all(dot(obj,x)<=len(C) for x in V),'original objective exceeds count')
            totals['support_objective_vertex_evaluations']+=len(V)
            if rank==d-1:
                c=produce(d,a,u,v);r=verify(c)
                require(set(maximizers)=={u,v},'supporting slice has a third vertex')
                edges+=1;totals['adjacent_pairs_checked']+=1
                for k in ['original_row_evaluations','interior_points','outside_segment_rejections']:totals[k]+=r[k]
                if edges==1:saved.append(serial(c))
            else:
                require(len(C)+1!=d,'nonedge satisfied theorem premise')
                require(len(maximizers)>2,'diagonal unexpectedly exposed as only pair')
                nonedges+=1;excess+=len(maximizers)-2
                if nonedges==1:examples.append({'dimension':d,'parameters':serial(a),'u':serial(u),'v':serial(v),
                     'common':sorted(C),'supporting_vertices':len(maximizers),'is_edge':False})
        bad=sum(not feasible(A,x) for x in set(allpts))
        totals['models']+=1;totals['active_square_systems']+=systems;totals['reference_vertices']+=len(V)
        totals['reference_edges']+=edges;totals['nonadjacent_pairs_checked']+=nonedges
        totals['extra_maximizers_on_diagonals']+=excess;totals['infeasible_full_tight_points']+=bad
        reports.append({'dimension':d,'original_rows':m,'vertices':len(V),'edges':edges,'diagonals':nonedges,
                        'independent_square_systems':systems,'infeasible_full_tight_points':bad})
        print('checked',reports[-1],flush=True)
    large=[]
    for d in [8,16,32,64]:
        a=list(map(Q,range(2*d+1)));u=root_vertex(d,a,set(range(1,d+1)));v=root_vertex(d,a,set(range(2,d+2)))
        c=produce(d,a,u,v);r=verify(c);saved.append(serial(c))
        large.append({**r,'full_vertex_graph_enumerated':False,'source_target_root_polynomials_checked':True})
    # Explicit failure without injectivity. A duplicated moment parameter gives
    # enough tight ROWS but not enough independent constraints for either endpoint.
    d=3;a=list(map(Q,[0,0,1,2,3]));A,V,_,_=reference(d,a)
    mids={tuple((x+y)/2 for x,y in zip(u,v)) for u,v in combinations(V,2)}
    counter=None
    for u,v in combinations(sorted(mids),2):
        I,J=tight(A,u),tight(A,v);C=I&J
        if len(I)==len(J)==d and len(C)==d-1:
            obj=[sum(A[i][j] for i in C) for j in range(d)]
            maxima=[x for x in V if dot(obj,x)==len(C)]
            if len(maxima)>2:
                counter={'dimension':d,'parameters':serial(a),'u':serial(u),'v':serial(v),
                         'source_tight':sorted(I),'target_tight':sorted(J),'common':sorted(C),
                         'source_rank':int(sp.Matrix([A[i] for i in I]).rank()),
                         'common_rank':int(sp.Matrix([A[i] for i in C]).rank()),'extra_support_vertices':len(maxima),
                         'repeated_parameter_hypothesis_necessary':True};break
    require(counter is not None,'missing repeated-node countermodel')
    def reject(name,fn):
        try:fn()
        except (ValueError,TypeError,KeyError,IndexError,ZeroDivisionError):negatives.append(name)
        else:raise AssertionError('forgery accepted '+name)
    baseline=next(c for c in saved if c['dimension']==3)
    for name,mut in [('wrong_objective',lambda c:c['objective'].__setitem__(0,'999')),
      ('wrong_maximum',lambda c:c.update(maximum='999')),
      ('omitted_shared_row',lambda c:c['common'].pop()),
      ('false_private_row',lambda c:c.update(source_private=c['common'][0])),
      ('changed_endpoint',lambda c:c['target'].__setitem__(0,'999')),
      ('wrong_source_active',lambda c:c['source_active'].pop()),
      ('duplicate_parameter',lambda c:c['parameters'].__setitem__(0,c['parameters'][1])),
      ('float_coordinate',lambda c:c['target'].__setitem__(0,0.5)),
      ('boolean_dimension',lambda c:c.update(dimension=True)),
      ('bad_binding',lambda c:c.update(binding='00'))]:
        c=deepcopy(baseline);mut(c);reject(name,lambda c=c:verify(c))
    reject('dimension_not_below_rows',lambda:produce(3,[0,1,2],[0]*3,[1]*3))
    oldprod,oldref,oldroot=globals()['produce'],globals()['reference'],globals()['root_vertex']
    def disabled(*a,**kw):raise AssertionError('consumer called geometric production')
    globals()['produce']=globals()['reference']=globals()['root_vertex']=disabled
    try:
        for c in saved:verify(c)
    finally:globals()['produce'],globals()['reference'],globals()['root_vertex']=oldprod,oldref,oldroot
    src=(PACKET/'solution.lean').read_text();meta=json.loads((PACKET/'problem.json').read_text())
    sig=src.split('\ntheorem solution ',1)[1].split(' := by\n',1)[0]
    form=meta['formal_statement'].split('\ntheorem moment_common_rows_expose_edges ',1)[1].split(' := by sorry',1)[0]
    require(sig==form,'public statement mismatch')
    require(all(x not in src for x in ['sorry','admit','native_decide','unsafe']),'proof admission or unsafe evaluator')
    report={'status':'PASS','scope':'Exact finite semantics/source checks, NOT Lean verification',
            'small':totals,'models':reports,'large':large,'repeated_parameter_counterexample':counter,
            'negative_controls':negatives,'producer_disabled_audits':len(saved),'public_type_match':True,
            'source_lines':len(src.splitlines()),'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
             for p in (PACKET/'solution.lean',PACKET/'problem.json',Path(__file__))}}
    (ROOT/'research/MOMENT_COMMON_ROW_EDGE_TESTS.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    (ROOT/'fixtures/moment_common_row_edges.json').write_text(json.dumps({'certificates':saved,'nonadjacent_controls':examples},indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
