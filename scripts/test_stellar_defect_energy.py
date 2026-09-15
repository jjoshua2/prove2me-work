#!/usr/bin/env python3
"""Independent complex subdivision and exact original-H geometry regressions."""
from __future__ import annotations
from collections import deque
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse, copy, hashlib, json, random
from stellar_defect_energy import (Complex, analyze, stellar, schedule, verify_schedule,
    verify_step, facet_subdivide, ridge_graph, carrier_route, verify_carrier_path, minimal, ordered, need)

# Fixed integers discovered by a random paraboloid search. The tests below do
# NOT use that floating-point search: they rebuild the polar with exact rows.
SEED_POINTS = [
 [-8,-6,-4,-9,7,246], [2,-6,-5,-9,8,210], [2,-3,-5,7,-6,123],
 [-9,0,6,-1,-3,127], [3,-1,-1,9,8,156], [7,-8,1,-1,9,196],
 [-2,-9,6,-2,-7,174], [-4,4,0,7,-2,85], [0,4,-8,-7,-4,145],
 [7,6,-4,4,8,181]]
BASE_WORD = [(2,3),(4,8),(5,8),(1,10),(0,11),(5,10),(7,9),(6,16)]
REPAIR_WORD = [(0,6),(0,5),(1,4),(2,16)]

def dot(a,b):
    need(len(a)==len(b), 'dimension mismatch')
    return sum((x*y for x,y in zip(a,b)), Q(0))

def solve(a,b):
    n=len(b); w=[[Q(x) for x in row]+[Q(rhs)] for row,rhs in zip(a,b)]
    need(len(w)==n and all(len(row)==n+1 for row in w), 'nonsquare system')
    for j in range(n):
        pivot=next((i for i in range(j,n) if w[i][j]),None)
        if pivot is None:return None
        w[j],w[pivot]=w[pivot],w[j];t=w[j][j]
        w[j]=[x/t for x in w[j]]
        for i in range(n):
            if i!=j and w[i][j]:
                t=w[i][j];w[i]=[x-t*y for x,y in zip(w[i],w[j])]
    return tuple(w[i][-1] for i in range(n))

def all_faces(facets):
    ans={frozenset()}
    for f in facets:
        for k in range(1,len(f)+1):
            ans.update(map(frozenset,combinations(f,k)))
    return ans

def missing_from_facets(n,facets):
    faces=all_faces(facets);d=max(map(len,facets),default=0);result=[]
    for size in range(2,min(n,d+1)+1):
        for t in combinations(range(n),size):
            s=frozenset(t)
            if s not in faces and all(s-{v} in faces for v in s):result.append(s)
    return tuple(ordered(result))

def facets_from_missing(k):
    need(k.n<=9,'abstract full enumeration cap')
    faces=[frozenset(c) for size in range(k.n+1) for c in combinations(range(k.n),size) if k.face(c)]
    return tuple(s for s in faces if not any(s<t for t in faces))

class Poly:
    """Exact simple bounded original-H polytope and a complete vertex table.

    Completeness is established at the seed by all active bases, then maintained
    by the proved cut/product operations, not inferred from sampled points.
    """
    def __init__(self,a,b,vertices,history=None):
        self.a=tuple(tuple(map(Q,row)) for row in a);self.b=tuple(map(Q,b))
        self.n=len(a);self.d=len(a[0]);self.vertices=dict(vertices);self.history=history or []

    @classmethod
    def polar(cls,points):
        n=len(points);d=len(points[0]);s=[sum(v[j] for v in points) for j in range(d)]
        a=[tuple(Q(n*v[j]-s[j]) for j in range(d)) for v in points];b=[Q(1)]*n;vertices={};trials=0
        for f in combinations(range(n),d):
            trials+=1;x=solve([a[i] for i in f],[b[i] for i in f])
            if x is None or any(dot(row,x)>rhs for row,rhs in zip(a,b)):continue
            active=frozenset(i for i in range(n) if dot(a[i],x)==b[i])
            need(len(active)==d,'seed is not simple')
            vertices[active]=x
        need(vertices,'empty/full-rank seed not established')
        need(all(sum(a[i][j] for i in range(n))==0 for j in range(d)), 'no positive normal balance')
        # A nonzero determinant basis together with positive normal balance
        # certifies trivial recession. Origin is strict in every row.
        p=cls(a,b,vertices,[{'operation':'exact_centered_polar','active_bases':trials,'point_count':n}]);p.audit()
        return p

    def audit(self):
        need(all(len(f)==self.d for f in self.vertices),'nonsimple active table')
        for f,x in self.vertices.items():
            need(all(dot(row,x)<=rhs for row,rhs in zip(self.a,self.b)),'infeasible original point')
            active=frozenset(i for i in range(self.n) if dot(self.a[i],x)==self.b[i])
            need(active==f,'false full active set')
            need(solve([self.a[i] for i in sorted(f)],[self.b[i] for i in sorted(f)])==x,'singular active basis')
        for i in range(self.n):
            xs=[x for f,x in self.vertices.items() if i in f];need(xs,'nongenuine original row')
            anchor=tuple(sum(x[j] for x in xs)/len(xs) for j in range(self.d))
            need(dot(self.a[i],anchor)==self.b[i], 'bad facet anchor')
            need(all(j==i or dot(self.a[j],anchor)<self.b[j] for j in range(self.n)), 'no strict relative facet point')
        return {'dimension':self.d,'genuine_facets':self.n,'vertices':len(self.vertices)}

    def cut(self,edge):
        e=frozenset(edge);u,v=sorted(e)
        need(len(e)==2 and any(e<=f for f in self.vertices),'cut is not an actual ridge')
        slack={f:self.b[u]+self.b[v]-dot(tuple(x+y for x,y in zip(self.a[u],self.a[v])),x)
               for f,x in self.vertices.items()}
        need(all(t>=0 for t in slack.values()),'negative ridge slack')
        need(all((t==0)==(e<=f) for f,t in slack.items()),'wrong ridge vertices')
        epsilon=min(t for t in slack.values() if t>0)/2
        newrow=tuple(x+y for x,y in zip(self.a[u],self.a[v]));rhs=self.b[u]+self.b[v]-epsilon
        a=(*self.a,newrow);b=(*self.b,rhs)
        # A cut's new vertices are precisely its intersections with crossing
        # OLD edges. These are constructed independently of the nonface update.
        g=ridge_graph(self.vertices,self.d);new={f:x for f,x in self.vertices.items() if slack[f]>0}
        for f,x in self.vertices.items():
            if slack[f]:continue
            for h in g[f]:
                if not slack[h]:continue
                y=self.vertices[h];t=epsilon/slack[h]
                need(0<t<1,'not a shallow cut')
                point=tuple(p+t*(q-p) for p,q in zip(x,y))
                active=frozenset(i for i in range(self.n+1) if dot(a[i],point)==b[i])
                need(len(active)==self.d,'cut generated a nonsimple point')
                new[active]=point
        predicted=set(facet_subdivide(self.vertices,e,self.n))
        need(set(new)==predicted,'geometric cut and independent stellar facets disagree')
        out=Poly(a,b,new,self.history+[{'operation':'ridge_truncate','edge':sorted(e),
                 'new_label':self.n,'epsilon':str(epsilon),'minimum_positive_old_slack':str(2*epsilon)}])
        out.audit();return out

    def product_interval(self):
        a=[(*row,Q(0)) for row in self.a]
        a += [(Q(0),)*self.d+(Q(1),),(Q(0),)*self.d+(Q(-1),)]
        b=[*self.b,Q(1),Q(1)];vertices={}
        for f,x in self.vertices.items():
            vertices[f|{self.n}]=(*x,Q(1));vertices[f|{self.n+1}]=(*x,Q(-1))
        out=Poly(a,b,vertices,self.history+[{'operation':'product_interval'}]);out.audit();return out

    def edge(self,f,h):
        f,h=frozenset(f),frozenset(h);need(f in self.vertices and h in self.vertices,'unknown H endpoints')
        need(len(f&h)==self.d-1,'not codimension-one active overlap')
        x,y=self.vertices[f],self.vertices[h];direction=tuple(q-p for p,q in zip(x,y));need(any(direction),'stationary')
        ratios=[]
        for i in range(self.n):
            delta=dot(self.a[i],direction);slack=self.b[i]-dot(self.a[i],x)
            need(slack>=0 and dot(self.a[i],y)<=self.b[i], 'violated original inequality')
            if i in f&h:need(delta==0,'lost common active row')
            if delta>0:ratios.append(slack/delta)
        need(ratios and min(ratios)==1,'not a full original maximal feasible step')
        need(solve([self.a[i] for i in sorted(f)],[self.b[i] for i in sorted(f)])==x,'no independent original basis')
        return True

    def data(self):
        return {'a':[[str(v) for v in row] for row in self.a],'b':list(map(str,self.b)),
                'vertices':[{'active':sorted(f),'point':list(map(str,x))} for f,x in sorted(self.vertices.items(),key=lambda t:tuple(sorted(t[0])))],
                'history':self.history}

def fixed_word(k,word,macro_lengths=None):
    initial=k;steps=[];energies=[k.energy()]
    for e in word:
        k,record=analyze(k,e);steps.append(record);energies.append(k.energy())
    lengths=macro_lengths or [1]*len(word);macros=[];pos=0
    for length in lengths:
        macros.append({'start':pos,'length':length,'energy_before':energies[pos],'energy_after':energies[pos+length]});pos+=length
    need(pos==len(word),'wrong macro decomposition')
    result={'mode':'two-step','initial':initial.data(),'input_sha256':initial.digest(),
            'status':'flag' if not k.higher() else 'stalled','steps':steps,'macros':macros,
            'final':k.data(),'search_evaluations':0};verify_schedule(result)
    return result,k

def missing_graph_connected(k):
    edges={i:set() for i in range(k.n)}
    for n in k.missing:
        for u,v in combinations(n,2):edges[u].add(v);edges[v].add(u)
    seen={0};stack=[0]
    while stack:
        for v in edges[stack.pop()]-seen:seen.add(v);stack.append(v)
    return len(seen)==k.n

def augment(k):
    # Product with an interval, followed by an actual face-edge subdivision.
    # Both selected endpoints are outside every higher nonface.
    need(all(3 not in n for n in k.higher()),'anchor belongs to a higher defect')
    j=Complex.make(k.n+2,[*k.missing,{k.n,k.n+1}]);j=stellar(j,(3,k.n))
    need(j.higher()==k.higher(),'flag-only coupling changed a higher defect')
    return j

def abstract_stage():
    systems={}
    n=4;possible=[frozenset(c) for s in range(2,n+1) for c in combinations(range(n),s)]
    for mask in range(1<<len(possible)):
        ns=tuple(minimal(possible[i] for i in range(len(possible)) if mask>>i&1));systems[(n,ns)]=Complex(n,ns)
    rng=random.Random(20260915)
    for n in (5,6,7):
        for _ in range(35):
            ns=minimal(frozenset(rng.sample(range(n),rng.randint(2,n))) for _ in range(rng.randint(1,12)))
            systems[(n,tuple(ns))]=Complex(n,tuple(ns))
    counts={'complexes':len(systems),'edge_updates':0,'nonbranching':0,'nontwin_nonbranching':0,
            'negative_energy_with_branching':0,'higher_increase_with_energy_drop':0}
    for k in systems.values():
        facets=facets_from_missing(k)
        for e in combinations(range(k.n),2):
            if not k.face(e):continue
            j,record=analyze(k,e)
            actual=facet_subdivide(facets,e,k.n)
            independent=missing_from_facets(k.n+1,actual)
            need(j.missing==independent,'formula disagrees with literal subdivided complex')
            verify_step(k,record);counts['edge_updates']+=1
            counts['nonbranching']+=record['no_branch']
            counts['nontwin_nonbranching']+=record['no_branch'] and record['containing_defects']>0 and not record['twin']
            counts['negative_energy_with_branching']+=j.energy()<k.energy() and not record['no_branch']
            counts['higher_increase_with_energy_drop']+=j.energy()<k.energy() and len(j.higher())>len(k.higher())
    return counts

def geometry_stage(fixtures):
    cases=[];counts={'source_polytopes':0,'original_route_pairs':0,'original_edges':0,
                    'refined_steps':0,'stationary_carriers':0,'nonshortest_routes':0,'direct_H_edge_audits':0,'bfs_edges':0}
    rng=random.Random(19260815)
    for d,n in [(4,7),(4,8),(4,9),(6,9),(6,10),(8,11)]:
        points=[tuple(t**j for j in range(1,d+1)) for t in range(n)]
        p=Poly.polar(points);k=Complex(n,missing_from_facets(n,p.vertices))
        old=schedule(k,'twins');new=schedule(k,'nonbranch');energy=schedule(k,'two-step')
        need(old['status']=='stalled' and new['status']=='flag','cyclic comparison no longer applies')
        vertices=list(p.vertices);pairs=[tuple(rng.sample(vertices,2)) for _ in range(12)]
        g=ridge_graph(vertices,d);distances={}
        for f,h in pairs:
            r=carrier_route(vertices,d,new,f,h);path=list(map(frozenset,r['original_path']))
            for a,b in zip(path,path[1:]):p.edge(a,b);counts['direct_H_edge_audits']+=1
            q=deque([f]);distance={f:0}
            while q:
                z=q.popleft()
                for w in g[z]:
                    if w not in distance:distance[w]=distance[z]+1;q.append(w)
            counts['bfs_edges']+=distance[h]
            counts['nonshortest_routes']+=len(path)-1>distance[h]
            counts['original_route_pairs']+=1;counts['original_edges']+=r['original_steps']
            counts['refined_steps']+=r['refined_steps'];counts['stationary_carriers']+=r['stationary_carriers']
        counts['source_polytopes']+=1
        cases.append({**p.audit(),'initial_higher':len(k.higher()),'initial_energy':k.energy(),
                      'twin_steps':len(old['steps']),'twin_residual_higher':sum(len(n)>=3 for n in old['final']['missing']),
                      'nonbranch_steps':len(new['steps']),'nonbranch_bound':new['final']['n']-d,
                      'two_step_steps':len(energy['steps'])})
    return {'counts':counts,'cyclic_cases':cases}

def barrier_stage(fixtures):
    p=Poly.polar(SEED_POINTS);k=Complex(p.n,missing_from_facets(p.n,p.vertices))
    seed_info={**p.audit(),'higher':len(k.higher()),'energy':k.energy()}
    need(not any(analyze(k,e)[1]['no_branch'] for e in k.productive_edges()),'seed has a nonbranch move')
    rise,record=analyze(k,(2,3))
    need(len(rise.higher())==13 and rise.energy()==16 and len(k.higher())==12 and k.energy()==19,
         'expected counted branching example changed')
    for e in BASE_WORD:p=p.cut(e);k=stellar(k,e)
    need(p.n==18 and p.d==6 and len(p.vertices)==164,'wrong barrier size')
    need(k.missing==missing_from_facets(p.n,p.vertices),'barrier nonfaces not independently complete')
    need(k.energy()==4 and len(k.higher())==4 and not k.twins(),'wrong barrier defects')
    support=set().union(*k.higher())
    residual_faces=sum(k.face(c) for size in range(1,len(support)+1) for c in combinations(support,size))
    need(len(support)==8 and residual_faces==135,'wrong residual-block comparison')
    table=[]
    for e in combinations(range(k.n),2):
        if k.face(e):
            j,r=analyze(k,e);table.append({'edge':list(e),'delta':j.energy()-k.energy(),
                  'containing':r['containing_defects'],'branch_energy':r['branch_energy']})
    need(min(x['delta'] for x in table)==0,'not an all-edge local minimum')
    need(not any(analyze(k,e)[1]['no_branch'] for e in k.productive_edges()),'barrier has a no-branch repair')
    strict=schedule(k,'energy');two=schedule(k,'two-step')
    need(strict['status']=='stalled' and two['status']=='flag','two-step escape failed')
    repair,end=fixed_word(k,REPAIR_WORD,[2,1,1])
    need([k.energy()]+[r['energy_after'] for r in repair['steps']]==[4,4,3,2,0], 'wrong fixed repair')
    need(missing_graph_connected(k),'base decomposes as a join')
    vertices=list(p.vertices);rng=random.Random(20261509);routes=[];totals={'pairs':0,'original_edges':0,
       'refined_steps':0,'stationary_carriers':0,'nonshortest':0,'direct_H_edges':0,'bfs_edges':0}
    g=ridge_graph(vertices,p.d);diameter=0
    for f in vertices:
        distance={f:0};q=deque([f])
        while q:
            v=q.popleft()
            for w in g[v]:
                if w not in distance:distance[w]=distance[v]+1;q.append(w)
        need(len(distance)==len(vertices),'disconnected original graph');diameter=max(diameter,max(distance.values()))
    for _ in range(40):
        f,h=rng.sample(vertices,2);route=carrier_route(vertices,p.d,repair,f,h)
        verify_carrier_path(vertices,p.d,repair,route,f,h)
        path=list(map(frozenset,route['original_path']))
        for a,b in zip(path,path[1:]):p.edge(a,b);totals['direct_H_edges']+=1
        distance={f:0};q=deque([f])
        while h not in distance:
            v=q.popleft()
            for w in g[v]:
                if w not in distance:distance[w]=distance[v]+1;q.append(w)
        totals['bfs_edges']+=distance[h]
        totals['nonshortest']+=len(path)-1>distance[h]
        totals['pairs']+=1;totals['original_edges']+=route['original_steps'];totals['refined_steps']+=route['refined_steps']
        totals['stationary_carriers']+=route['stationary_carriers'];routes.append(route)
    forged_route_rejections=0
    for key, value in [('original_steps', 0), ('all_pairs_bound_from_flag_theorem', 0),
                       ('intermediate_levels_checked', 0), ('original_path', []),
                       ('refined_path', [[999]])]:
        bad=copy.deepcopy(routes[0]);bad[key]=value
        f=frozenset(routes[0]['original_path'][0]);h=frozenset(routes[0]['original_path'][-1])
        try:verify_carrier_path(vertices,p.d,repair,bad,f,h)
        except ValueError:forged_route_rejections+=1
        else:raise AssertionError('accepted forged route field: '+key)
    family=[];current=k
    for r in range(65):
        need(current.n==18+3*r and current.higher()==k.higher(),'bad suspended/coupled family')
        need(missing_graph_connected(current),'coupled family became a join')
        # Only E contained in some higher nonface can decrease energy. Those
        # 12 candidates retain exactly the base obstruction for every r.
        local=[analyze(current,e)[1] for e in current.productive_edges()]
        need(len(local)==12 and all(x['energy_after']>=4 for x in local),'family barrier lost')
        words=[(0,6),(0,5),(1,4),(2,16)]
        cert,fin=fixed_word(current,words,[2,1,1]);need(not fin.higher(),'family fixed repair failed')
        if r in (0,1,2,4,10,26,64):
            family.append({'r':r,'dimension':6+r,'genuine_facets_by_construction':current.n,
                           'higher_defects':4,'energy':4,'productive_edges':12,
                           'strict_decreasing_edges':0,'repair_steps':4,
                           'flag_vertices':fin.n,'all_pairs_bound':fin.n-(6+r)})
        if r<64:current=augment(current)
    # Two explicit original-H family lifts, separately from symbolic large-r proof.
    coordinate_family=[];pp=p
    for r in (1,2):
        oldn=pp.n;pp=pp.product_interval().cut((3,oldn))
        coordinate_family.append({'r':r,**pp.audit()})
    if fixtures:
        fixtures.mkdir(parents=True,exist_ok=True)
        data={'original_H':p.data(),'complex':k.data(),'all_face_edge_energy_changes':table,
              'repair':repair,'sample_routes':routes,'exact_original_graph_diameter':diameter}
        (fixtures/'stellar-energy-barrier.json').write_text(json.dumps(data,indent=2)+'\n')
        (fixtures/'stellar-energy-seed-points.json').write_text(json.dumps(SEED_POINTS)+'\n')
    return {'seed':seed_info,'branching_descent':record,'barrier':{**p.audit(),'higher':4,'energy':4,
             'face_edges_checked':len(table),'productive_edges':len(k.productive_edges()),
             'minimum_delta':min(x['delta'] for x in table),'maximum_delta':max(x['delta'] for x in table),
             'exact_graph_diameter':diameter,'residual_support':len(support),'residual_nonempty_faces':residual_faces,
             'old_residual_block_bound':p.n-p.d-len(support)+residual_faces},'fixed_repair_energy':[4,4,3,2,0],
             'two_step_constructor':verify_schedule(two),'route_tests':totals,'forged_route_rejections':forged_route_rejections,
             'infinite_family_samples':family,'explicit_H_family_lifts':coordinate_family}

def negative_stage():
    k=Complex.make(6,[{0,1,2},{3,4,5}]);j,rec=analyze(k,(0,3));need(j.energy()==4,'old branching control lost')
    c=schedule(k,'two-step');count=0
    def rejects(name,fn):
        nonlocal count
        try:fn()
        except (ValueError,IndexError,KeyError):count+=1;return
        raise AssertionError('accepted invalid control '+name)
    rejects('nonminimal list',lambda:Complex.make(4,[{0,1},{0,1,2}]))
    rejects('bad labels',lambda:Complex.make(3,[{0,3}]))
    rejects('nonface edge',lambda:stellar(Complex.make(3,[{0,1}]),(0,1)))
    for field,value in [('energy_after',0),('branch_energy',0),('extra_higher',[]),('no_branch',True),('new_label',0),('input_sha256','bad')]:
        x=copy.deepcopy(rec);x[field]=value
        rejects(field,lambda x=x:verify_step(k,x))
    r=copy.deepcopy(c);r['steps'].pop();rejects('omitted step',lambda:verify_schedule(r))
    r=copy.deepcopy(c);r['macros'][0]['energy_after']=999;rejects('wrong macro energy',lambda:verify_schedule(r))
    r=copy.deepcopy(c);r['final']['n']+=1;rejects('wrong final labels',lambda:verify_schedule(r))
    rejects('search cap',lambda:schedule(k,search_cap=1))
    rejects('step cap',lambda:schedule(k,step_cap=0))
    return {'rejected':count,'unshielded_join_energy_before':2,'unshielded_join_energy_after':4}

def verify_fixture(path):
    data=json.loads(Path(path).read_text())
    p=Poly.polar(SEED_POINTS)
    for e in BASE_WORD:p=p.cut(e)
    need(p.data()==data['original_H'],'serialized original-H geometry does not match exact construction')
    k=Complex(p.n,missing_from_facets(p.n,p.vertices))
    need(k.data()==data['complex'],'serialized minimal-nonface list incomplete')
    need(data['repair']['initial']==k.data(),'repair starts at a different complex')
    verify_schedule(data['repair']);edge_count=0
    for route in data['sample_routes']:
        f=frozenset(route['original_path'][0]);h=frozenset(route['original_path'][-1])
        verify_carrier_path(p.vertices,p.d,data['repair'],route,f,h)
        original=list(map(frozenset,route['original_path']))
        for a,b in zip(original,original[1:]):p.edge(a,b);edge_count+=1
    table=[]
    for e in combinations(range(k.n),2):
        if k.face(e):
            j,r=analyze(k,e);table.append({'edge':list(e),'delta':j.energy()-k.energy(),
                'containing':r['containing_defects'],'branch_energy':r['branch_energy']})
    need(table==data['all_face_edge_energy_changes'],'incomplete or incorrect edge-energy ledger')
    return {'status':'PASS','exact_original_vertices':len(p.vertices),'original_facets':p.n,
            'saved_routes':len(data['sample_routes']),'original_edge_audits':edge_count,
            'all_face_edges_checked':len(table),'routing_search_rerun':False,
            'graph_diameter_recomputed':False,
            'scope':'Exact seed and cut reconstruction, saved stellar/carrier replay and original-row checks; not Lean.'}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--stage',choices=['abstract','geometry','barrier','negative','all'],default='all')
    ap.add_argument('--out',type=Path);ap.add_argument('--fixtures',type=Path);ap.add_argument('--verify-fixture',type=Path);args=ap.parse_args()
    if args.verify_fixture:
        print(json.dumps(verify_fixture(args.verify_fixture),indent=2));return
    result={'status':'PASS','scope':'Written mathematical results and exact finite tests; not Lean compilation, axiom audit, Prove2Me acceptance, universal strategy completion, or Polynomial Hirsch.'}
    for name,fn in [('abstract',abstract_stage),('geometry',lambda:geometry_stage(args.fixtures)),('barrier',lambda:barrier_stage(args.fixtures)),('negative',negative_stage)]:
        if args.stage in (name,'all'):
            result[name]=fn();print(name, 'PASS', flush=True)
    result['source_sha256']={p:hashlib.sha256((Path(__file__).parent/p).read_bytes()).hexdigest() for p in ('stellar_defect_energy.py','test_stellar_defect_energy.py')}
    text=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.parent.mkdir(parents=True,exist_ok=True);args.out.write_text(text)
    print(text)

if __name__=='__main__':main()
