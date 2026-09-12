#!/usr/bin/env python3
"""Exhaustive small graph/set checks, forged-certificate controls, exact barrier table."""
from collections import Counter
from copy import deepcopy
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
from portal_debt_router import Model,distances,verify_tree,require,jsonable


def graph_checks():
    counts=Counter()
    for n in range(1,6):
        edges=list(combinations(range(n),2))
        for mask in range(1<<len(edges)):
            g={j:set() for j in range(n)}
            for k,(u,v) in enumerate(edges):
                if mask>>k&1:g[u].add(v);g[v].add(u)
            counts['graphs']+=1
            for u in range(n):
                ds=distances(g,u)
                def walk(path):
                    v=path[-1];length=len(path)-1
                    if length<=ds[v]+1:
                        slack=length-ds[v]
                        for z in range(n):
                            ix=[i for i,x in enumerate(path) if z==x or x in g[z]]
                            require(not ix or max(ix)-min(ix)<=slack+2,'near-geodesic window')
                            require(len(ix)<=slack+3,'near-geodesic contact count')
                            counts['contact_windows']+=1
                        counts['near_geodesic_paths']+=1
                    if length>=n-1:return
                    for w in sorted(g[v]):
                        if w not in path:walk(path+[w])
                walk([u])
    # Sharp q+3 contact count for every tested slack, including q=1.
    for q in range(7):
        p=list(range(q+3));z=q+3;g={i:set() for i in range(q+4)}
        for u,v in zip(p,p[1:]):g[u].add(v);g[v].add(u)
        for u in p:g[z].add(u);g[u].add(z)
        require(len(p)-1==distances(g,0)[p[-1]]+q,'sharp fixture slack')
        require(sum(x in g[z] for x in p)==q+3,'sharp fixture contacts')
        counts['sharp_slack_examples']+=1
    return dict(counts)


def signature_checks():
    counts=Counter()
    U=range(4)
    for d in range(1,5):
        sigs=[set(s) for s in combinations(U,d)]
        for seq in product(sigs,repeat=4):
            counts['signature_chains']+=1
            seen=set(seq[0]);fresh=True;cost=0
            for a,b in zip(seq,seq[1:]):
                if (b&seen)-a:fresh=False
                cost+=len(b-a);seen|=b
            if fresh:
                require(cost+len(seq[0])==len(seen),'fresh-chain union telescoping')
                neutral=seen-(seq[0]|seq[-1])
                require(cost==len(seq[-1]-seq[0])+len(neutral),'neutral debt identity')
                counts['fresh_chains']+=1
            # True with arbitrary reentries: exact per-row triangle/excursion debt.
            debt=0
            for j in U:
                bits=[int(j in s) for s in seq]
                toggles=sum(a!=b for a,b in zip(bits,bits[1:]))
                debt+=(toggles-abs(bits[0]-bits[-1]))//2
            require(cost==len(seq[-1]-seq[0])+debt,'arbitrary-chain excursion identity')
    return dict(counts)


def barrier_table(root):
    p=json.loads((root/'fixtures/portal_debt_barrier_input.json').read_text())
    m=Model(p['input']);u=p['comparison']['u'];v=p['comparison']['v']
    common,pts,facets=m.face(u,v);regions,g,ds,dt=m.regions(u,v)
    require(m.dim(u,v)==3 and ds[-2]==3,'barrier should use exactly two facets')
    rows=[]
    # This lower bound uses exact graph distances INSIDE facets, not the
    # recursive router's own distances. Thus even perfect child solvers cannot
    # do better while keeping the parent facet path metric-shortest.
    for a in sorted(facets):
        if u not in facets[a]:continue
        for b in sorted(facets):
            if v not in facets[b] or a==b:continue
            inter=facets[a]&facets[b]
            if not inter:continue
            ga={x:m.graph[x]&facets[a] for x in facets[a]}
            gb={x:m.graph[x]&facets[b] for x in facets[b]}
            da=distances(ga,u);db=distances(gb,v)
            for z in sorted(inter):
                rows.append({'first_facet':a,'second_facet':b,'portal':z,
                             'first_cost':da[z],'second_cost':db[z],'total':da[z]+db[z]})
    exact=distances(m.graph,u)[v];lower=min(row['total'] for row in rows)
    require(exact==5 and lower==6,'barrier bound changed')
    geo=m.route(u,v,'recursive');relaxed=m.route(u,v,'relaxed')
    require(geo['length']==lower and relaxed['length']==exact and relaxed['facet_slack']==1,'route witness mismatch')
    p['certificates']={mode:m.route(u,v,mode) for mode in ['lex','local','recursive','relaxed']}
    p['independent_lower_bound']={'candidates':rows,'minimum':lower,'ambient_distance':exact}
    (root/'fixtures/small_geodesic_barrier.json').write_text(json.dumps(jsonable(p),indent=2,sort_keys=True)+'\n')
    return m,p,{'barrier_vertices':len(m.vertices),'barrier_facets':m.n,
                'independently_audited_geodesic_portals':len(rows),'strict_geodesic_minimum':lower,
                'one_extra_region_edge_route':relaxed['length']}


def negative_checks(m,p):
    u=p['comparison']['u'];v=p['comparison']['v'];base=p['certificates']['recursive']['tree']
    cases=[]
    cases.append(('changed requested source',lambda:verify_tree(m,base,v,v)))
    for name,mut in [
        ('false dimension',lambda t:t.update(dimension=99)),
        ('false neutral row list',lambda t:t.update(neutral_rows=[])),
        ('missing children',lambda t:t.update(children=[])),
        ('changed portal',lambda t:t['portals'].__setitem__(0,v)),
        ('repeated region label',lambda t:t['labels'].__setitem__(1,t['labels'][2])),
        ('unknown region label',lambda t:t['labels'].__setitem__(1,999)),
        ('invalid endpoint',lambda t:t.update(u=-1)),
        ('changed child destination',lambda t:t['children'][0].update(v=v)),
    ]:
        t=deepcopy(base);mut(t);cases.append((name,lambda t=t:verify_tree(m,t,u,v)))
    relaxed=p['certificates']['relaxed']['tree']
    cases.append(('hidden geodesic relaxation',lambda:verify_tree(m,relaxed,u,v,max_slack=0)))
    cases.append(('unsupported slack allowance',lambda:verify_tree(m,relaxed,u,v,max_slack=9)))
    for name,mut in [
        ('floating point input',lambda d:d['A'][0].__setitem__(0,0.0)),
        ('bad positive balance',lambda d:d['positive_balance'].__setitem__(0,'0')),
        ('wrong interior',lambda d:d.update(interior=['0']*3)),
        ('duplicate inequality',lambda d:(d['A'].append(d['A'][0][:]),d['b'].append(d['b'][0]),d['positive_balance'].append('1'))),
    ]:
        d=deepcopy(p['input']);mut(d);cases.append((name,lambda d=d:Model(d)))
    pyramid={'A':[[0,0,-1],[1,0,1],[-1,0,1],[0,1,1],[0,-1,1]],'b':[0,1,1,1,1],
             'interior':[0,0,'1/2'],'positive_balance':[4,1,1,1,1]}
    cases.append(('nonsimple pyramid',lambda:Model(pyramid)))
    rejected=[]
    for name,f in cases:
        try:f()
        except (ValueError,KeyError,TypeError):rejected.append(name)
        else:raise AssertionError('accepted negative control: '+name)
    return rejected


def main():
    root=Path(__file__).resolve().parents[1]
    counts={**graph_checks(),**signature_checks()}
    m,p,barrier=barrier_table(root);counts.update(barrier)
    neg=negative_checks(m,p)
    exp=json.loads((root/'research/PORTAL_DEBT_EXPLORATION.json').read_text())
    dantzig=json.loads((root/'fixtures/portal_debt_dantzig_input.json').read_text())
    dm=Model(dantzig['input']);u=dantzig['u'];v=dantzig['v']
    dr={mode:dm.route(u,v,mode) for mode in ['lex','local','recursive','relaxed']}
    require(dr['lex']['local_debt']==0 and dr['lex']['debt']==1,'zero-root/high-descendant witness')
    require(dr['recursive']['length']==6,'Dantzig recursive route changed')
    dantzig['certificates']=dr
    (root/'fixtures/dantzig_zero_root_debt.json').write_text(json.dumps(jsonable(dantzig),indent=2,sort_keys=True)+'\n')
    result={'status':'PASS','scope':'Exact finite graph/set/rational-polytope checks. No Lean or Prove2Me verdict.',
            **counts,'models_checked':len(exp['models'])+2,'ordinary_route_certificates':exp['route_checks']+8,
            'negative_controls_rejected':len(neg),'negative_control_names':neg,
            'comparative_findings':{k:v for k,v in exp.items() if k not in ('models','witnesses')},
            'dantzig_witness':{'dimension':6,'facets':dm.n,'vertices':len(dm.vertices),
                               'root_debt':0,'lex_length':dr['lex']['length'],'descendant_debt':dr['lex']['debt'],
                               'optimized_length':dr['recursive']['length']},
            'source_sha256':{str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest()
                             for folder,ext in [('Solutions','*.lean'),('scripts','*.py')]
                             for f in sorted((root/folder).glob(ext))}}
    (root/'research/PORTAL_DEBT_CHECK_2026-09-12.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
