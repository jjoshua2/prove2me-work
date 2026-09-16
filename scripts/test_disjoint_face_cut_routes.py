#!/usr/bin/env python3
"""Independent full-H references, exact permutation averages and adverse cases."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations,permutations
from pathlib import Path
from collections import deque
from math import factorial
import argparse,hashlib,json,random
import disjoint_face_cut_routes as R


def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(R.serial(x),sort_keys=True,indent=2)+'\n')


def model_data(d,codes,seed=273,depth=Q(1,5),lower=None,upper=None):
    rng=random.Random(seed);low=[Q(0)]*d if lower is None else lower;high=[Q(1)]*d if upper is None else upper
    C=[];b=[]
    for code in sorted(codes):
        w=[rng.randint(1,7) for _ in range(d)]
        a=[Q(w[i]*(1 if code>>i&1 else -1),high[i]-low[i]) for i in range(d)]
        corner=[high[i] if code>>i&1 else low[i] for i in range(d)]
        C.append(a);b.append(R.dot(a,corner)-depth)
    return {'base':{'kind':'box','lower':low,'upper':high},'cuts_A':C,'cuts_b':b}


def face_data(d,specs,seed=882):
    rng=random.Random(seed);C=[];b=[]
    for mask,code in specs:
        w=[rng.randint(1,7) if mask>>i&1 else 0 for i in range(d)]
        a=[z*(1 if code>>i&1 else -1) for i,z in enumerate(w)]
        C.append(a);b.append(sum(a[i] for i in range(d) if code>>i&1)-Q(1,5))
    return {'base':{'kind':'box','lower':[0]*d,'upper':[1]*d},'cuts_A':C,'cuts_b':b}


def same_272(d):
    # EXACT earlier capped_box generator, not a replacement input distribution.
    rng=random.Random(272+d);codes={(1<<d)-(1<<j) for j in range(1,d)}
    while len(codes)<2*d-2:codes.add(rng.randrange(1,(1<<d)-1))
    C=[];h=[]
    for code in sorted(codes):
        w=[rng.randrange(1,8) for _ in range(d)]
        C.append([w[i]*(1 if code>>i&1 else -1) for i in range(d)])
        h.append(sum(w[i] for i in range(d) if code>>i&1)-Q(1,5))
    data={'base':{'kind':'box','lower':[0]*d,'upper':[1]*d},'cuts_A':C,'cuts_b':h}
    M=R.Model(data);data.update(A=M.A,b=M.b,max_cut_overlap=1,start=[0]*d,target=[1]*d)
    return data


def all_states(M):
    return [(c,p) for c in range(1<<M.d) for p in (M.cap(c)['support'] if M.cap(c) is not None else [None])]


def combinatorial_graph(M):
    S=all_states(M);G={s:set() for s in S}
    for c,p in S:
        if p is not None:
            F=M.cap(c)
            for j in range(M.d):
                if j in F['support']:
                    if j!=p:G[c,p].add((c,j))
                else:G[c,p].add((c^(1<<j),p))
            n=c^(1<<p);G[c,p].add((n,p if M.cap(n) is not None else None))
        else:
            for j in range(M.d):
                n=c^(1<<j);G[c,p].add((n,j if M.cap(n) is not None else None))
    return G


def distances(G,s):
    D={s:0};q=deque([s])
    while q:
        a=q.popleft()
        for b in G[a]:
            if b not in D:D[b]=D[a]+1;q.append(b)
    return D


def full_H(M):
    import sympy as sp
    A=sp.Matrix(M.A);b=sp.Matrix(M.b);V=set();systems=0
    for I in combinations(range(len(M.A)),M.d):
        systems+=1;B=A[list(I),:]
        if B.det():
            x=tuple(Q(str(a)) for a in B.inv()*b[list(I),:])
            if all(R.dot(a,x)<=t for a,t in zip(M.A,M.b)):V.add(x)
    acts={x:set(R.audit.active(M.A,M.b,x)) for x in V};G={x:set() for x in V}
    for x,y in combinations(V,2):
        I=sorted(acts[x]&acts[y])
        if I and A[I,:].rank()==M.d-1:G[x].add(y);G[y].add(x)
    states=all_states(M);C=combinatorial_graph(M)
    assert V=={M.point(s) for s in states}
    assert all(G[M.point(s)]=={M.point(t) for t in C[s]} for s in states)
    return C,{'active_systems':systems,'original_vertices':len(V),'original_edges':sum(map(len,G.values()))//2}


def small_stage(folder):
    rng=random.Random(273);cases=[]
    for d,codes in [(2,[]),(2,[0]),(2,list(range(4))),(3,[0,1,3]),(3,list(range(8))),
                    (3,[0,2,3,5,6]),(4,[0,1,2,4,8,15])]:
        data=model_data(d,codes,seed=700+d+len(codes))
        if d==2 and len(codes)==1:data=model_data(d,codes,seed=704,lower=[Q(-2),Q(1,3)],upper=[Q(3,2),Q(7,3)])
        cases.append(data)
    cases.extend([face_data(3,[(3,0)]),face_data(3,[(3,0),(6,6)]),face_data(4,[(3,0),(6,6),(15,9)])])
    counts={'models':0,'routes':0,'original_edges':0,'BFS_edges':0,'nonshortest':0,'worse_than_best_order':0,
            'permutations_checked':0,'active_systems':0,'original_vertices':0,'graph_edges':0,'nonrevisiting':0}
    saved=[];records=[]
    for index,data in enumerate(cases):
        M=R.Model(data)
        G,ref=full_H(M)
        counts['active_systems']+=ref['active_systems'];counts['original_vertices']+=ref['original_vertices'];counts['graph_edges']+=ref['original_edges']
        states=all_states(M);pairs=list(combinations(states,2))
        if len(pairs)>90:pairs=rng.sample(pairs,90)
        pairs+=[(states[0],states[0])];stats={'routes':0,'nonshortest':0,'worse_than_best_order':0}
        for s,t in pairs:
            inp=R.serial({**data,'start':M.point(s),'target':M.point(t)});out=R.construct(inp);c=out['certificate']
            h=s[0]^t[0];coords=[i for i in range(M.d) if h>>i&1]
            costs=[len(R.splice(M,s,t,list(p)))-1 for p in permutations(coords)]
            counts['permutations_checked']+=len(costs)
            assert Q(sum(costs),len(costs))==Q(c['initial_expectation'])
            route=[M.identify(p['point']) for p in c['path']['vertices']]
            assert all(y in G[x] for x,y in zip(route,route[1:]))
            best=distances(G,s)[t];L=out['verified']['original_edges']
            assert best<=L<=max(costs) and not out['verified']['original_row_reentries']
            counts['routes']+=1;counts['original_edges']+=L;counts['BFS_edges']+=best
            counts['nonshortest']+=L>best;counts['worse_than_best_order']+=L>min(costs);counts['nonrevisiting']+=1
            stats['routes']+=1;stats['nonshortest']+=L>best;stats['worse_than_best_order']+=L>min(costs)
            if L>best or len(saved)<8:saved.append({'input':inp,**out,'reference_shortest':best,'best_coordinate_order':min(costs)})
        counts['models']+=1;records.append({'dimension':M.d,'cuts':len(M.cuts),**ref,**stats})
        print('small',index,records[-1],flush=True)
    dump(folder/'small.json',saved)
    return {'status':'PASS','counts':counts,'models':records,'saved_records':len(saved)}


def large_stage(folder):
    records=[];saved=[]
    for d in [4,8,16,32]:
        data=R.serial(same_272(d));out=R.construct(data);M=R.Model(data)
        reference_order=list(reversed(range(d)))
        reference_states=R.splice(M,M.identify(data['start']),M.identify(data['target']),reference_order)
        old=R.serial(R.path_packet(M,data,reference_states));R.audit.verify_path(data,old)
        assert len(reference_states)-1==2*d-1
        # d original target facets are absent initially; simple edges gain at most one.
        assert out['verified']['original_edges']>=d
        record={'dimension':d,**out['verified'],**out['discovery'],
                'old_reverse_order_edges_reaudited':len(reference_states)-1,
                'same_generator_as_272':True,'proved_vertex_formula_not_enumerated':2**d+len(M.cuts)*(d-1)}
        records.append(record);saved.append({'input':data,**out,'old_coordinate_order_path':old})
        dump(folder/f'same272-{d}.json',saved[-1]);print('large',record,flush=True)
    # Every first cubical neighbor is cut: each source edge gains no target facet.
    # Therefore d+1 is a rigorous lower bound, attained by this construction.
    sharp=[]
    for d in [3,6,12]:
        data=model_data(d,[1<<i for i in range(d)],seed=100+d);data.update(start=[0]*d,target=[1]*d)
        out=R.construct(R.serial(data));assert out['verified']['original_edges']==d+1
        M=R.Model(data)
        assert all(not any(z==1 for z in M.point((1<<i,i))) for i in range(d))
        sharp.append({'dimension':d,**out['verified'],'shortest_by_first_step_and_target_facet_count':True})
        dump(folder/f'sharp-{d}.json',{'input':data,**out})
    # Endpoint ports and tiny/asymmetric cut coefficients stay explicit.
    extra=[]
    for power in [20,80,160]:
        data=model_data(6,[0,1,2,3,60,62,63],depth=Q(1,2**power));M=R.Model(data)
        data.update(start=M.point((0,4)),target=M.point((63,4)));out=R.construct(R.serial(data))
        extra.append({'epsilon_power':power,**out['verified']})
        dump(folder/f'tiny-{power}.json',{'input':data,**out})
    # This deterministic average-minimizer is NOT an optimizer of actual length.
    codes=[1,2,4,5,12,13,14,15,16,21,23,24,25,26,28,29,30]
    data=model_data(5,codes,seed=981);data.update(start=[0]*5,target=[1]*5);M=R.Model(data)
    out=R.construct(R.serial(data));costs=[]
    for order in permutations(range(5)):
        states=R.splice(M,(0,None),(31,None),order);costs.append((len(states)-1,order,states))
    best,order,states=min(costs);assert out['verified']['original_edges']==6 and best==5
    short=R.serial(R.path_packet(M,data,states));R.audit.verify_path({**data,'A':M.A,'b':M.b},short)
    dump(folder/'adverse-greedy.json',{'input':data,**out,'shorter_certificate':short})
    adverse={'dimension':5,'cuts':17,'chosen_edges':6,'shortest_edges':5,
             'best_order':order,'checked_orders':120,'shortest_lower_bound':'five target facets absent at simple source'}
    extremal=[]
    for d in [2,3,5]:
        data=model_data(d,list(range(1<<d)),seed=42+d);M=R.Model(data)
        data.update(start=M.point((0,0)),target=M.point(((1<<d)-1,0)))
        out=R.construct(R.serial(data));assert out['verified']['original_edges']==2*d
        extremal.append({'dimension':d,**out['verified'],'shortest_by_port_parity_argument':True})
        dump(folder/f'full-truncation-{d}.json',{'input':data,**out})
    # A codimension-two cut removes 2^(d-2) old corners, not one.
    mixed=[]
    for d in [8,32]:
        data=same_272(d);keep=[j for j,a in enumerate(data['cuts_A']) if not(a[0]<0 and a[1]<0)]
        data.pop('A');data.pop('b')
        data['cuts_A']=[data['cuts_A'][j] for j in keep]+[[-1,-1]+[0]*(d-2)]
        data['cuts_b']=[data['cuts_b'][j] for j in keep]+[-Q(1,5)]
        M=R.Model(data);data['start']=M.point((0,0));out=R.construct(R.serial(data))
        record={**out['verified'],**out['discovery'],'removed_vertices_of_large_face':2**(d-2),
            'vertex_count_formula_not_enumerated':2**d+sum((len(F['support'])-1)*2**(d-len(F['support'])) for F in M.cuts.values())}
        mixed.append(record);dump(folder/f'noncorner-{d}.json',{'input':data,**out});print('noncorner',record,flush=True)
    return {'status':'PASS','mixed_face_cases':mixed,'same_272_inputs':records,'sharp_first_layer':sharp,'tiny_cut_endpoints':extra,
            'adverse_conditional_choice':adverse,'sharp_2d_endpoints':extremal}


def negative_stage(folder):
    data=R.serial(same_272(4));good=R.construct(data);bad=[]
    def reject(name,fn):
        try:fn()
        except (ValueError,KeyError,IndexError,TypeError,ZeroDivisionError):bad.append(name);return
        raise AssertionError('accepted '+name)
    def mutate(name,fn):
        c=deepcopy(good['certificate']);fn(c);reject(name,lambda:R.verify(data,c))
    mutate('wrong binding',lambda c:c.update(input_sha256='bad'))
    mutate('false expectation',lambda c:c.update(initial_expectation='0'))
    mutate('missing decision',lambda c:c['decisions'].pop())
    mutate('wrong prefix',lambda c:c['decisions'][0].update(corner=7))
    mutate('repeated coordinate',lambda c:c['decisions'][1].update(next_coordinate=c['decisions'][0]['next_coordinate']))
    mutate('false after potential',lambda c:c['decisions'][0].update(after='-1'))
    mutate('false immediate cost',lambda c:c['decisions'][0].update(immediate_edges=0))
    mutate('wrong port',lambda c:c['start_state'].__setitem__(1,2))
    mutate('cut fractions changed',lambda c:c['cuts'][0].update(depth='100'))
    mutate('missing facet anchor',lambda c:c['facet_anchors'].pop())
    mutate('false strict point',lambda c:c.update(strict_point=data['start']))
    mutate('false vertex inverse',lambda c:c['path']['vertices'][0]['inverse'][0].__setitem__(0,'17'))
    mutate('edge certificate removed',lambda c:c['path']['edges'].pop())
    mutate('endpoint changed',lambda c:c['path']['vertices'][-1]['point'].__setitem__(0,'9'))
    reject('cut exceeds its shallow-face depth',lambda:R.Model(model_data(3,[0],depth=Q(20))))
    nonsingle={'base':{'kind':'box','lower':[0]*3,'upper':[1]*3},'cuts_A':[[1,1,0]],'cuts_b':[1]}
    reject('deep nonlocal cut at threshold',lambda:R.Model(nonsingle))
    dup=model_data(3,[0]);dup['cuts_A']*=2;dup['cuts_b']*=2
    reject('duplicate corner cuts',lambda:R.Model(dup))
    meet={'base':{'kind':'box','lower':[0,0],'upper':[1,1]},'cuts_A':[[-1,-1],[1,-1]],'cuts_b':['-1/2','1/2']}
    reject('touching cap closures',lambda:R.Model(meet))
    altered=deepcopy(data);altered['A'][0][0]='1';reject('unbound original H',lambda:R.Model(altered))
    interior=deepcopy(data);interior['start']=['1/2']*4;reject('nonvertex input',lambda:R.construct(interior))
    unknown=deepcopy(data);unknown['affine_chart']={'matrix':[]};reject('unsupported chart',lambda:R.construct(unknown))
    # Positive row scales keep the same geometric model and coordinate decisions.
    scaled=deepcopy(data);scaled.pop('A');scaled.pop('b')
    for j in range(len(scaled['cuts_A'])):
        scale=Q(j+1,7);scaled['cuts_A'][j]=[str(Q(x)*scale) for x in scaled['cuts_A'][j]];scaled['cuts_b'][j]=str(Q(scaled['cuts_b'][j])*scale)
    mapped=R.construct(scaled)
    assert [x['next_coordinate'] for x in mapped['certificate']['decisions']]==[x['next_coordinate'] for x in good['certificate']['decisions']]
    assert [p['point'] for p in mapped['certificate']['path']['vertices']]==[p['point'] for p in good['certificate']['path']['vertices']]
    return {'status':'PASS','rejected':bad,'positive_row_scaling_same_path':True}


def replay(folder):
    records=[]; compared_paths=0; compared_edges=0
    for f in sorted(folder.glob('*.json')):
        x=json.loads(f.read_text());records.extend(x if isinstance(x,list) else [x])
    def kill(*a,**k):raise AssertionError('production used in verifier')
    old={n:getattr(R,n) for n in ['choose_order','construct','path_packet']}
    vp=R.Model.vertex_packet;anchors=R.Model.anchors
    au={n:getattr(R.audit,n) for n in ['solve','inverse_or_kernel','independent_rows','vertex_packet','add_path_inverses']}
    try:
        for n in old:setattr(R,n,kill)
        R.Model.vertex_packet=kill;R.Model.anchors=kill
        for n in au:setattr(R.audit,n,kill)
        for x in records:
            assert R.verify(x['input'],x['certificate'])==x['verified']
            for name in ('old_coordinate_order_path','shorter_certificate'):
                if name in x:
                    M=R.Model(x['input']);data={**x['input'],'A':M.A,'b':M.b}
                    result=R.audit.verify_path(data,x[name])
                    compared_paths+=1;compared_edges+=result['original_edges']
    finally:
        for n,f in old.items():setattr(R,n,f)
        R.Model.vertex_packet=vp;R.Model.anchors=anchors
        for n,f in au.items():setattr(R.audit,n,f)
    return {'status':'PASS','records':len(records),'comparison_paths_reaudited':compared_paths,
            'comparison_edges_reaudited':compared_edges,'order_search_inverse_and_geometry_producers_disabled':True}


def main():
    p=argparse.ArgumentParser();p.add_argument('--stage',choices=['small','large','negative','audit'],required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--fixtures',type=Path,required=True);a=p.parse_args()
    a.fixtures.mkdir(parents=True,exist_ok=True)
    result={'small':small_stage,'large':large_stage,'negative':negative_stage,'audit':replay}[a.stage](a.fixtures)
    result['source_sha256']={s:hashlib.sha256((Path(__file__).parent/s).read_bytes()).hexdigest() for s in
        ['disjoint_face_cut_routes.py','test_disjoint_face_cut_routes.py','original_route_exclusion.py']}
    dump(a.out,result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
