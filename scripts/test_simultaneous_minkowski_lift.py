#!/usr/bin/env python3
"""Independent exact ground truth and negative controls for simultaneous lifts."""
from simultaneous_minkowski_lift import *
from pathlib import Path
import copy

def unique_objective(model,rng,base=False):
    for _ in range(200):
        f=vec(rng.randint(-29,29) for _ in range(model.core.dim))
        if base:f=f[:-1]+(F(-100),)
        try:model.support_state(f);return f
        except ValueError:pass
    raise ValueError('objective cap')

def explicit_sum(model,cap=20000):
    c=model.core
    if c.kind in ('point','polygon'):cores=c.vertices
    else:
        n=c.dim if c.kind=='box' else c.dim-1
        cores=[vec(xs)+((F(0),) if c.kind=='pyramid' else ()) for xs in itertools.product([-1,1],repeat=n)]
        if c.kind=='pyramid':cores.append((F(0),)*n+(F(1),))
    require(len(cores)*__import__('math').prod(len(vs) for vs in model.factors)<=cap,'ground-truth cap')
    return tuple(set(vsum(qs,c.dim) for qs in itertools.product(cores,*model.factors)))

def all_edges(cert):
    result=[]
    for j,f in enumerate(cert['fibres']):
        result+=f['edges']
        if j<len(cert['bridges']):result.append(cert['bridges'][j]['edge'])
    return result

def independent_check(model,cert,points):
    for e in all_edges(cert):
        x,y=model.point(e['left']),model.point(e['right']);f=e['normal'];beta=max(dot(f,v) for v in points)
        require(x in points and y in points and x!=y,'not sum endpoints')
        require(dot(f,x)==beta==dot(f,y),'not globally supporting')
        require(all(dot(f,v)!=beta or segment_member(v,x,y) for v in points),'sum support face not an edge')
    for obj,state in [(cert['start_objective'],cert['fibres'][0]['states'][0]),(cert['end_objective'],cert['fibres'][-1]['states'][-1])]:
        x=model.point(state);beta=dot(obj,x)
        require(all(v==x or dot(obj,v)<beta for v in points),'endpoint not uniquely exposed')

def random_factors(dim,count,rng):
    result=[]
    for i in range(count):
        n=2 if i%4==3 else 3;vs={(F(0),)*dim}
        while len(vs)<n:vs.add(vec(F(rng.randint(-3,3),rng.randint(1,3)) for _ in range(dim)))
        result.append(tuple(sorted(vs)))
    return tuple(result)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--stage',choices=['small','large','negative','all'],default='all');ap.add_argument('--out',type=Path);args=ap.parse_args()
    rng=random.Random(20260914);records=[];counts={'routes':0,'ordinary_edges':0,'independent_full_sum_edges':0,'planar_graph_pairs':0,'nonshortest_routes':0,'rejected_controls':0}
    if args.stage in ('all','small'):
        for mi in range(12):
            d=2 if mi<8 else 3
            core=Core('polygon',2,hull2([vec((0,0)),vec((2,0)),vec((3,1)),vec((1,3)),vec((-1,1))])) if mi%3==0 and d==2 else Core('box' if mi%2 else 'pyramid',d)
            model=Model(core,random_factors(d,1+mi%3,rng));points=explicit_sum(model);hull=hull2(points) if d==2 else None
            for q in range(10):
                fa,fb=unique_objective(model,rng),unique_objective(model,rng);cert=lift(model,fa,fb,100*mi+q);independent_check(model,cert,points)
                su=cert['summary'];counts['routes']+=1;counts['ordinary_edges']+=su['ordinary_edges'];counts['independent_full_sum_edges']+=su['ordinary_edges']
                if hull:
                    a=hull.index(model.point(model.support_state(fa)));b=hull.index(model.point(model.support_state(fb)))
                    distance=min((a-b)%len(hull),(b-a)%len(hull));counts['planar_graph_pairs']+=1
                    require(distance<=su['ordinary_edges'],'shorter than independent graph distance')
                    if distance<su['ordinary_edges']:counts['nonshortest_routes']+=1
                    for e in all_edges(cert):
                        a=hull.index(model.point(e['left']));b=hull.index(model.point(e['right']))
                        require(min((a-b)%len(hull),(b-a)%len(hull))==1,'not a polygon edge')
                records.append({'model':mi,**su})
        examples=[('parallel',((vec((0,0)),vec((1,0))),(vec((0,0)),vec((3,0)))),vec((-1,1)),vec((1,1))),('collinear-redundant',((vec((0,0)),vec((1,0)),vec((2,0))),),vec((-1,1)),vec((1,1))),('repaired-rank-two',((vec((0,0)),vec((1,0))),(vec((0,0)),vec((0,1)))),vec((-1,-1)),vec((1,1)))]
        for label,factors,a,b in examples:
            model=Model(Core('point',2,(vec((0,0)),)),factors);cert=lift(model,a,b,77);independent_check(model,cert,explicit_sum(model))
            if label=='parallel':require(cert['summary']['ordinary_edges']==1,'parallel switch bug')
            if label=='repaired-rank-two':require(cert['summary']['generic_retries']>0,'nongeneric control not exercised')
            records.append({'model':label,**cert['summary']});counts['routes']+=1;counts['ordinary_edges']+=cert['summary']['ordinary_edges'];counts['independent_full_sum_edges']+=cert['summary']['ordinary_edges']
    if args.stage in ('all','large'):
        rng=random.Random(20260914)
        for d,r in [(8,8),(16,12),(24,16),(32,24)]:
            factors=[]
            for i in range(r):
                u=[F(0)]*d;v=[F(0)]*d
                u[i%(d-1)]=F(1);u[(i+1)%(d-1)]+=F(1,3);u[-1]=F(i%3,5)
                v[(i+2)%(d-1)]=F(1);v[i%(d-1)]+=F(-1,4);v[-1]=F((i+1)%3,7)
                factors.append(((F(0),)*d,tuple(u),tuple(v)))
            model=Model(Core('pyramid',d),tuple(factors));fa=unique_objective(model,rng,True);fb=unique_objective(model,rng,True)
            cert=lift(model,fa,fb,d+r);counts['routes']+=1;counts['ordinary_edges']+=cert['summary']['ordinary_edges']
            records.append({'dimension':d,'triangle_factors':r,'core_vertices_formula':2**(d-1)+1,'input_representation':'pyramid core and finite lists; not newly discovered H-equality',**cert['summary']})
            if d==32:
                dest=Path(__file__).resolve().parents[1]/'research/fixtures/simultaneous_lift_32d.json';dest.write_text(json.dumps(to_json({'model':model,'certificate':cert}),separators=(',',':'))+'\n')
    if args.stage in ('all','negative'):
        model=Model(Core('pyramid',3),((vec((0,0,0)),vec((1,0,1)),vec((0,1,0))),(vec((0,0,0)),vec((1,2,0)),vec((-1,0,1)))))
        cert=lift(model,vec((-3,-5,-9)),vec((4,2,-8)),5)
        def rejects(name,fn):
            try:fn()
            except (ValueError,IndexError):counts['rejected_controls']+=1;return
            raise AssertionError('accepted invalid control '+name)
        def mutate(fn):
            c=copy.deepcopy(cert);fn(c);return lambda:check_lift(model,c)
        rejects('wrong normal',mutate(lambda c:c['fibres'][0]['edges'][0].update(normal=(F(0),)*3)))
        rejects('missing edge',mutate(lambda c:c['fibres'][0]['edges'].pop()))
        rejects('wrong wall',mutate(lambda c:c['fibres'][0]['wall_times'].__setitem__(0,F(0))))
        rejects('time backwards',mutate(lambda c:c['fibres'][0]['samples'].__setitem__(1,F(-1))))
        rejects('wrong coefficients',mutate(lambda c:c['fibres'][0]['edges'][0].update(parallel_weights=(F(0),)*3)))
        rejects('wrong endpoint',mutate(lambda c:c.update(end_objective=c['start_objective'])))
        rejects('wrong core path',mutate(lambda c:c['core_path'].__setitem__(1,c['core_path'][0])))
        rejects('bridge missing',mutate(lambda c:c['bridges'].pop()))
        rejects('core not same fibre',mutate(lambda c:c['fibres'][0].update(core=c['core_path'][1])))
        diag=Model(Core('point',2,(vec((0,0)),)),((vec((0,0)),vec((1,0))),(vec((0,0)),vec((0,1)))))
        rejects('rank-two switch mistaken for edge',lambda:sweep_once(diag,vec((-1,-1)),vec((1,1)),vec((0,0))))
        rejects('cube-face diagonal',lambda:Core('box',3).check_face(vec((0,0,1)),vec((-1,-1,1)),vec((1,1,1))))
        rejects('pyramid face',lambda:Core('pyramid',3).check_face(vec((0,0,-1)),vec((-1,-1,0)),vec((1,1,0))))
        rejects('empty factor',lambda:Model(Core('point',2,(vec((0,0)),)),((),)))
        rejects('duplicate list',lambda:Model(Core('point',2,(vec((0,0)),)),((vec((0,0)),vec((0,0))),)))
    out={'status':'PASS','seed':20260914,'stage':args.stage,'counts':counts,'records':records,'scope':'Exact exposed-edge and affine-envelope certificates in the stated factor representation. No arbitrary original-H decomposition, universal Python correctness, Lean compilation or Polynomial Hirsch claim.','source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),Path(__file__).with_name('simultaneous_minkowski_lift.py')]}}
    if args.out:args.out.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'stage':args.stage,'counts':counts,'large':[x for x in records if 'dimension' in x]},indent=2))
if __name__=='__main__':main()
