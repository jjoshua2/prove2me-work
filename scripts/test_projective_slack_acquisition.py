#!/usr/bin/env python3
"""Independent ORIGINAL-H comparisons and positive-projective covariance checks.

No reference graph is passed to either route producer. Complete small graphs
and both policies are recomputed. Large product graphs are not enumerated.
The distortion tests are exact rational positive projective maps; transform
positivity comes from original supporting slack, not from a sampled guess.
"""
from __future__ import annotations
from fractions import Fraction as Q
from copy import deepcopy
from pathlib import Path
from itertools import product
import argparse,hashlib,json,random,time
import projective_slack_acquisition as new
import two_face_acquisition as old
import test_two_face_acquisition as ref

ROOT=Path(__file__).resolve().parents[1]
base=old.base
require,rat,dot,serial=old.require,old.rat,old.dot,old.serial
DEPS=['two_face_acquisition.py','simple_tangent_policy_audit.py','test_two_face_acquisition.py',
      'target_phase_pivot.py','target_roof_phase_barrier.py']


def hashes():
    return {f'scripts/{n}':hashlib.sha256((ROOT/'scripts'/n).read_bytes()).hexdigest()
            for n in ['projective_slack_acquisition.py','test_projective_slack_acquisition.py']+DEPS}


def dump(path,x):
    path.parent.mkdir(exist_ok=True,parents=True)
    path.write_text(json.dumps(serial(x),indent=2,sort_keys=True)+'\n')


def independent_rho(A,b,anchor,x,T):
    values=[]
    for i in sorted(T):
        den=b[i]-sum(a*z for a,z in zip(A[i],anchor))
        if den>0:values.append((b[i]-sum(a*z for a,z in zip(A[i],x)))/den)
    return min(values)/sum(values) if sum(values) else Q(0)


def graph_checks(A,b,u,v,c,V,G):
    nf=nd=fallbacks=0
    for phase in c['phases']:
        anchor=phase['anchor']
        for dc in phase['decisions']:
            x=tuple(dc['basis']['point']);locked=V[x]&V[v]
            direct=[z for z in G[x] if locked<=V[z] and (V[z]&V[v])-locked]
            minhit=[1] if direct else [];facevalues=[]
            for face in dc['faces']:
                fixed=set(face['fixed_rows']);pts={z for z in V if fixed<=V[z]}
                require(pts=={tuple(bs['point']) for bs in face['corners']},'complete reference face mismatch')
                D=ref.distances(G,x,pts);require(set(D)==pts,'reference polygon disconnected')
                hits=[D[z] for z in pts if (V[z]&V[v])-locked]
                if hits:minhit.append(min(hits))
                facevalues.extend((independent_rho(A,b,anchor,z,V[v]),D[z],z) for z in pts)
                nf+=1
            arc,info=new.audit_decision(A,b,anchor,c['target_basis'],dc)
            require(bool(info['acquired'])==bool(minhit),'incorrect reference acquisition verdict')
            if minhit:require(len(arc)==min(minhit),'acquisition not shortest within inspected faces')
            else:
                best=min(s for s,l,z in facevalues)
                distance=min(l for s,l,z in facevalues if s==best)
                require(independent_rho(A,b,anchor,arc[-1],V[v])==best and len(arc)==distance,
                        'fallback is not a shortest route to a globally minimal inspected score')
                fallbacks+=1
            nd+=1
    return nf,nd,fallbacks


def graph_stage(name):
    begin=time.monotonic();A,b=ref.models()[name];V,G,facetanchors=ref.reference(A,b)
    pairs=[(u,v) for u in V for v in V if u!=v]
    complete=not(name.startswith('holdout') or name=='truncated_octahedron')
    if not complete:
        random.Random(253+len(A)).shuffle(pairs);pairs=pairs[:80]
    if name=='truncated_octahedron':
        pair=(tuple(map(Q,[2,1,0])),tuple(map(Q,[-2,-1,0])))
        if pair not in pairs:pairs.append(pair)
    if name=='holdout_clipped_slanted_prism':
        pair=(tuple(map(Q,[1,1,0])),tuple(map(Q,[3,9,2])))
        if pair not in pairs:pairs.append(pair)
    totals={k:0 for k in ['pairs','old_edges','new_edges','shortest_edges','old_nonshortest','new_nonshortest',
        'improved','worsened','ties','faces','decisions','fallbacks','old_fallbacks','face_checks',
        'old_phase_decreases','intermediate_rho_increases','retired_faces','loops_removed']}
    table=[];saved=set();Dcache={}
    for u,v in pairs:
        if u not in Dcache:Dcache[u]=ref.distances(G,u)
        optimum=Dcache[u][v]
        before=old.construct(A,b,u,v);out=new.construct(A,b,u,v);r=out['verified']
        p=[tuple(x) for x in r['path']];erased=[tuple(x) for x in r['loop_erased_path']]
        require(p[0]==u and p[-1]==v and all(z in G[x] for x,z in zip(p,p[1:])), 'not an original graph route')
        require(len(set(erased))==len(erased) and all(z in G[x] for x,z in zip(erased,erased[1:])),'false loop erasure')
        require(optimum<=r['loop_erased_edges']<=r['committed_edges'],'distance violation')
        faces,decisions,fallbacks=graph_checks(A,b,u,v,out['certificate'],V,G)
        oldlength=before['verified']['committed_edges'];length=r['committed_edges']
        kind='improved' if length<oldlength else 'worsened' if length>oldlength else 'ties'
        totals['pairs']+=1;totals['old_edges']+=oldlength;totals['new_edges']+=length;totals['shortest_edges']+=optimum
        totals['old_nonshortest']+=oldlength>optimum;totals['new_nonshortest']+=length>optimum;totals[kind]+=1
        totals['faces']+=r['faces'];totals['decisions']+=decisions;totals['fallbacks']+=fallbacks
        totals['old_fallbacks']+=before['verified']['fallback_decisions'];totals['face_checks']+=faces
        totals['old_phase_decreases']+=r['old_phase_objective_decreases'];totals['intermediate_rho_increases']+=r['intermediate_rho_increases']
        totals['retired_faces']+=r['retired_faces'];totals['loops_removed']+=length-r['loop_erased_edges']
        table.append({'start':u,'target':v,'old':oldlength,'new':length,'shortest':optimum,'new_fallbacks':fallbacks})
        if kind in ('improved','worsened') and kind not in saved:
            dump(ROOT/f'fixtures/projective_{name}_{kind}.json',{'input':{'A':A,'b':b,'start':u,'target':v},**out,'previous':before,'shortest':optimum});saved.add(kind)
    dump(ROOT/f'research/PROJECTIVE_PAIRS_{name}.json',table)
    return {'name':name,'complete_ordered_pairs':complete,'dimension':len(A[0]),'original_facets':len(A),
            'vertices':len(V),'graph_edges':sum(map(len,G.values()))//2,'totals':totals,'seconds':round(time.monotonic()-begin,3)}


def transform(A,b,u,v,q,delta):
    """Phi(x)=(x-v)/(delta+q.(x-v)). The caller certifies its positive
    denominator globally; no vertex sampling is used as that theorem premise."""
    q=tuple(map(rat,q));delta=rat(delta);require(delta>0,'positive target denominator')
    slack=[z-dot(a,v) for a,z in zip(A,b)];d=len(v)
    AA=[[a[j]+s*q[j]/delta for j in range(d)] for a,s in zip(A,slack)];bb=[s/delta for s in slack]
    def image(x):
        den=delta+dot(q,[a-b for a,b in zip(x,v)])
        require(den>0,'projective denominator not positive')
        return [(a-b)/den for a,b in zip(x,v)]
    return AA,bb,image(u),image(v),image


def incidence(data,path):
    A,b=data
    return [base.active_rows(A,b,p) for p in path]


def distortion_stage():
    A,b=ref.models()['truncated_octahedron'];u=list(map(Q,[2,1,0]));v=list(map(Q,[-2,-1,0]))
    target=base.basis_packet(A,b,v);f,J=old.phase_objective(A,b,u,target);h=len(v)-len(J)
    dc=old.produce_decision(A,b,f,target,u,{});arc,info=old.audit_decision(A,b,f,target,dc)
    require(not info['acquired'],'need genuine no-acquisition fallback')
    alpha=dot(f,[a-b for a,b in zip(arc[-1],u)])/h
    out=new.construct(A,b,u,v);path=out['verified']['path'];records=[]
    for power in [8,40,120,240]:
        eps=Q(1,2**power);q=[-(1-eps)*x/h for x in f]
        # Denominator eps+(1-eps)*sum(normalized target slacks)/h >=eps
        # on the ENTIRE original P. This is a positive original-row proof.
        AA,bb,uu,vv,image=transform(A,b,u,v,q,eps)
        tt=base.basis_packet(AA,bb,vv);ff,jj=old.phase_objective(AA,bb,uu,tt)
        cdc=old.produce_decision(AA,bb,ff,tt,uu,{});carc,ci=old.audit_decision(AA,bb,ff,tt,cdc)
        ratio=dot(ff,[a-b for a,b in zip(carc[-1],uu)])/h
        expected=eps*alpha/(1-(1-eps)*alpha)
        require(ratio==expected and cdc['selection']==dc['selection'],'projective old-order/gap formula failed')
        newout=new.construct(AA,bb,uu,vv)
        require(newout['verified']['path']==[image(x) for x in path],'new route not projectively covariant')
        first=newout['certificate']['phases'][0]['decisions'][0]
        _,m=new.audit_decision(AA,bb,uu,newout['certificate']['target_basis'],first)
        require(m['rho_before']==Q(1,3) and m['rho_after']==Q(4,25),'projective share change failed')
        record={'epsilon_power':power,'old_initial_gap_fraction':alpha,'transformed_old_gap_fraction':ratio,
            'new_first_share':m['rho_before'],'new_after_first_macro':m['rho_after'],
            'new_first_macro_edges':first['selection'].get('count',1),
            'new_total_edges':newout['verified']['committed_edges'],
            'entire_new_route_is_transformed_original':True,'denominator_global_lower_bound':eps}
        records.append(record)
        if power in (8,240):dump(ROOT/f'fixtures/projective_gap_{power}.json',{'input':{'A':AA,'b':bb,'start':uu,'target':vv},**newout,'distortion':record})
    return {'original_dimension':3,'original_facets':len(A),'genuine_no_acquisition_source':True,
        'fixed_combinatorial_type':True,'records':records,'universal_positive_gap_fraction_refuted':True}


def invariance_stage():
    records=[];rowchecks=vertexchecks=0
    for name in ['moment_3_8','clipped_cube_3','truncated_octahedron','holdout_clipped_slanted_prism']:
        A,b=ref.models()[name];V,G,_=ref.reference(A,b);pts=list(V)
        for number in range(3):
            u,v=pts[(3*number)%len(pts)],pts[(-2*number-1)%len(pts)]
            before=new.construct(A,b,u,v);row=number%len(A);t=Q(number+1,7)
            q=[-t*x for x in A[row]];delta=1+t*(b[row]-dot(A[row],v))
            # Positive globally: D(x)=1+t*slack_row(x)>=1.
            AA,bb,uu,vv,image=transform(A,b,u,v,q,delta)
            after=new.construct(AA,bb,uu,vv)
            require(after['verified']['path']==[image(x) for x in before['verified']['path']],'positive-projective trajectory mismatch')
            require([p['locked'] for p in after['certificate']['phases']]==[p['locked'] for p in before['certificate']['phases']], 'phase locks changed')
            require([[dc['selection'] for dc in p['decisions']] for p in after['certificate']['phases']]==
                    [[dc['selection'] for dc in p['decisions']] for p in before['certificate']['phases']], 'selected original-face itinerary changed')
            # Independently verify the ORIGINAL transformed halfspace identity
            # on every small reference vertex, and recover the full new H graph.
            for x in pts:
                den=1+t*(b[row]-dot(A[row],x));xx=image(x)
                require(all(B-dot(a,xx)==(B0-dot(a0,x))/den for a,B,a0,B0 in zip(AA,bb,A,b)), 'homogeneous slack identity failed')
                rowchecks+=len(A);vertexchecks+=1
            if number==0:
                VV,GG,_=ref.reference(AA,bb)
                require(set(VV)=={tuple(image(x)) for x in pts},'full independently recovered projective vertices mismatch')
                require(all(tuple(image(z)) in GG[tuple(image(x))] for x in G for z in G[x]),'full projected original edge graph mismatch')
            # Further affine coordinate mixing and positive row scales must not
            # alter the same combinatorial choices either.
            AAA,bbb,uuu,vvv,affine=ref.affine(AA,bb,uu,vv,754+number)
            scales=[Q(1+i%7,2+i%5) for i in range(len(AAA))]
            AAA=[[s*x for x in a] for s,a in zip(scales,AAA)];bbb=[s*x for s,x in zip(scales,bbb)]
            combined=new.construct(AAA,bbb,uuu,vvv)
            require(combined['verified']['path']==[affine(x) for x in after['verified']['path']], 'dense affine/scaling composition mismatch')
            records.append({'model':name,'transform':number,'projective_edges':after['verified']['committed_edges'],
                'dense_composed_edges':combined['verified']['committed_edges'],'global_denominator_lower_bound':1,
                'complete_graph_recovered':number==0})
    return {'projective_full_route_checks':len(records),'dense_affine_positive_row_compositions':len(records),
        'original_slack_identity_checks':rowchecks,'small_vertex_images_checked':vertexchecks,'records':records}


def product_stage():
    out=[]
    for d in [4,8,12]:
        A,b,u,v=ref.product_model([(10,2,2,8)]*(d//2))
        begin=time.monotonic();before=old.construct(A,b,u,v);after=new.construct(A,b,u,v)
        target=base.basis_packet(A,b,v);row=target['active'][0];t=Q(1,11)
        q=[-t*x for x in A[row]];delta=1+t*(b[row]-dot(A[row],v))
        AA,bb,uu,vv,image=transform(A,b,u,v,q,delta)
        transformed=new.construct(AA,bb,uu,vv)
        require(transformed['verified']['path']==[image(x) for x in after['verified']['path']], 'large product projective covariance failed')
        # 15-gon factors, endpoints six apart on their cycles. This is a
        # separate product-graph lower bound, not graph input to the solver.
        lower=6*(d//2)
        require(after['verified']['committed_edges']==lower,'polygon-product shortestness failed')
        record={'dimension':d,'original_facets':len(A),'proved_product_vertices':15**(d//2),
            'old_route_edges':before['verified']['committed_edges'],'new_route_edges':after['verified']['committed_edges'],
            'projectively_transformed_route_edges':transformed['verified']['committed_edges'],
            'independent_product_distance':lower,'new_faces':after['verified']['faces'],
            'new_traced_face_edges':after['verified']['traced_face_edges'],'whole_graph_enumerated':False,
            'seconds':round(time.monotonic()-begin,3)}
        out.append(record)
        if d==12:dump(ROOT/'fixtures/projective_product12d.json',{'input':{'A':AA,'b':bb,'start':uu,'target':vv},**transformed,'independent_product_distance':lower})
    return out


def negative_stage():
    A,b=ref.models()['truncated_octahedron'];u=list(map(Q,[2,1,0]));v=list(map(Q,[-2,-1,0]));out=new.construct(A,b,u,v);c=out['certificate'];names=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,TypeError,IndexError,ZeroDivisionError):names.append(name)
        else:raise AssertionError('accepted invalid '+name)
    for field,value in [('format','bad'),('problem_sha256','bad')]:
        z=deepcopy(c);z[field]=value;reject(field,lambda z=z:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['faces'].pop();reject('omitted_face',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['faces'][0]['corners'].pop();reject('omitted_polygon_corner',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['selection']['count']=1;reject('not_global_minimum',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['selection']['count']+=6;reject('nonshortest_repeated_arc',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['anchor']=[Q(1,2)]*3;reject('changed_phase_anchor',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['locked']=[0];reject('spurious_locked_row',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][-1]['decisions'].pop();reject('incomplete_route',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['basis']['directions'][0][0]+=1;reject('false_basis_inverse',lambda:new.verify(A,b,u,v,z))
    z=deepcopy(c);z['phases'][0]['decisions'][0]['selection']['count']=2.0;reject('float_selection',lambda:new.verify(A,b,u,v,z))
    reject('changed_original_endpoint',lambda:new.verify(A,b,u,u,c))
    reject('cap_without_completion',lambda:new.construct(A,b,u,v,edge_cap=1))
    zA=deepcopy(A);zA[0][0]=1.0;reject('float_original_row',lambda:new.construct(zA,b,u,v))
    reject('invalid_projective_chart',lambda:transform(A,b,u,v,[0,0,0],0))
    # Verify stored rational JSON and block every discovery entry point.
    decoded=new.decode(serial(c));require(new.verify(A,b,u,v,decoded)==out['verified'],'JSON exact replay mismatch')
    blocked=[(base,'invert'),(base,'basis_packet'),(old,'trace_face'),(new,'produce')];previous=[]
    def forbidden(*a,**k):raise AssertionError('verifier invoked discovery')
    try:
        for obj,name in blocked:previous.append((obj,name,getattr(obj,name)));setattr(obj,name,forbidden)
        require(new.verify(A,b,u,v,c)==out['verified'],'search-disabled audit failed')
    finally:
        for obj,name,fn in previous:setattr(obj,name,fn)
    squareA=[[-1,0],[0,-1],[1,0],[0,1]];squareb=[0,0,1,1]
    point=new.construct(squareA,squareb,[0,0],[0,0])['verified'];require(point['committed_edges']==0,'zero route')
    line=new.construct(squareA,squareb,[0,0],[1,0])['verified'];require(line['committed_edges']==1,'one-dimensional locked face')
    return {'rejected':len(names),'names':names,'search_disabled_audit':True,'rational_JSON_audit':True,
        'equal_endpoint_edges':0,'one_dimensional_face_edges':1}


def main():
    p=argparse.ArgumentParser();p.add_argument('--graph');p.add_argument('--aux',action='store_true');p.add_argument('--assemble',action='store_true');a=p.parse_args()
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    selected=[a.graph] if a.graph else list(ref.models()) if not (a.aux or a.assemble) else []
    for name in selected:
        r=graph_stage(name);dump(ROOT/f'research/PROJECTIVE_STAGE_{name}.json',{'source_sha256':hashes(),'result':r});print(name,r['totals'],flush=True)
    if a.aux or (a.graph is None and not a.assemble):
        r={'distortion':distortion_stage(),'invariance':invariance_stage(),'products':product_stage(),'negative':negative_stage()}
        dump(ROOT/'research/PROJECTIVE_STAGE_aux.json',{'source_sha256':hashes(),'result':r});print('AUX PASS',flush=True)
    if a.assemble or (a.graph is None and not a.aux):
        stages=[json.loads((ROOT/f'research/PROJECTIVE_STAGE_{name}.json').read_text()) for name in ref.models()]
        aux=json.loads((ROOT/'research/PROJECTIVE_STAGE_aux.json').read_text());require(all(s['source_sha256']==hashes() for s in stages+[aux]),'stale stages')
        totals={k:sum(s['result']['totals'][k] for s in stages) for k in stages[0]['result']['totals']}
        out={'status':'PASS','scope':'Exact simple original-H policy comparison; written projective/retirement proof, no Lean or platform verdict.',
             'source_sha256':hashes(),'graph_totals':totals,'graphs':[s['result'] for s in stages],**aux['result']}
        dump(ROOT/'research/PROJECTIVE_SLACK_CHECK.json',out);print('TOTAL',totals,flush=True)
if __name__=='__main__':main()
