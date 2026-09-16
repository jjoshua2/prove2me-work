#!/usr/bin/env python3
"""Route-local conditional expectation for disjoint single-face box cuts.

Recognizes the class from ALL actual cut coefficients, constructs actual
original edges, and reuses #271's unchanged arithmetic positive-path checker.
No LP, direction catalogue, global vertex graph, or random trial is needed.
The class excludes cuts not confined to one box face, or intersecting caps.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import argparse, hashlib, json
import original_route_exclusion as audit

need, rat, serial, dot = audit.require, audit.rat, audit.serial, audit.dot


class Model:
    def __init__(self, data):
        B=data['base']; need(B['kind']=='box' and not data.get('affine_chart'),
                                 'requires an explicit axis box; arbitrary charts are not recognized')
        self.low=tuple(map(rat,B['lower'])); self.high=tuple(map(rat,B['upper']))
        self.d=d=len(self.low)
        need(d>=2 and len(self.high)==d and all(x<y for x,y in zip(self.low,self.high)),
             'nondegenerate box of dimension at least two required')
        self.width=tuple(y-x for x,y in zip(self.low,self.high))
        self.C=tuple(tuple(map(rat,row)) for row in data.get('cuts_A',[]))
        self.rhs=tuple(map(rat,data.get('cuts_b',[])))
        need(len(self.C)==len(self.rhs) and all(len(row)==d for row in self.C),'cut dimensions')
        E=[tuple(Q(i==j) for j in range(d)) for i in range(d)]
        self.A=tuple(tuple(-x for x in e) for e in E)+tuple(E)+self.C
        self.b=tuple(-x for x in self.low)+self.high+self.rhs
        if 'A' in data or 'b' in data:
            need(tuple(tuple(map(rat,row)) for row in data['A'])==self.A and
                 tuple(map(rat,data['b']))==self.b,'unbound or altered original H rows')
        self.cuts={}; self.cut_certificates=[]
        for j,(a,b) in enumerate(zip(self.C,self.rhs)):
            w=tuple(abs(t*s) for t,s in zip(a,self.width))
            support=tuple(i for i,t in enumerate(w) if t)
            need(len(support)>=2,'cut must truncate a face of codimension at least two')
            mask=sum(1<<i for i in support)
            c=sum(1<<i for i,t in enumerate(a) if t>0)
            beta=dot(a,self.corner(c))-b
            need(0<beta<min(w[i] for i in support),'cut does not strictly remove exactly one box face')
            need(c not in self.cuts,'two cuts assigned to the same original corner')
            alpha=tuple(beta/x if x else None for x in w)
            self.cuts[c]={'row':2*d+j,'alpha':alpha,'beta':beta,'weights':w,'mask':mask,'pattern':c,'support':support}
            self.cut_certificates.append({'pattern':c,'fixed_mask':mask,'depth':beta,'fractions':alpha})
        self.cap_cache={}
        caps=list(self.cuts.values())
        for j,F in enumerate(caps):
            for G in caps[:j]:
                opposite=F['mask'] & G['mask'] & (F['pattern']^G['pattern'])
                need(opposite,'two deleted original faces intersect')
                if opposite.bit_count()==1:
                    i=opposite.bit_length()-1
                    need(F['alpha'][i]+G['alpha'][i]<1,
                         'cut closures meet: no positive surviving connecting segment')
        # A fixed strict point proves full dimension; the box proves boundedness.
        self.center=tuple((x+y)/2 for x,y in zip(self.low,self.high))
        need(all(dot(a,self.center)<b for a,b in zip(self.A,self.b)),'no certified strict center')

    def corner(self,c):
        need(type(c)is int and 0<=c<1<<self.d,'invalid corner code')
        return tuple(self.high[i] if c>>i&1 else self.low[i] for i in range(self.d))

    def cap(self,c):
        if c not in self.cap_cache:
            matches=[F for F in self.cuts.values() if (c^F['pattern']) & F['mask']==0]
            need(len(matches)<=1,'original vertex belongs to two deleted faces')
            self.cap_cache[c]=matches[0] if matches else None
        return self.cap_cache[c]

    def point(self,state):
        c,port=state; x=list(self.corner(c));F=self.cap(c)
        if F is None:
            need(port is None,'uncut corner cannot have a cap port');return tuple(x)
        need(type(port)is int and port in F['support'],'cut face requires a transverse port')
        sign=1 if not(c>>port&1) else -1
        x[port]+=sign*self.width[port]*F['alpha'][port]
        return tuple(x)

    def identify(self,x):
        x=tuple(map(rat,x));need(len(x)==self.d,'endpoint dimension')
        need(all(dot(a,x)<=b for a,b in zip(self.A,self.b)),'infeasible endpoint')
        free=[i for i in range(self.d) if x[i] not in (self.low[i],self.high[i])]
        need(len(free)<=1,'endpoint not a vertex of the recognized truncation')
        code=sum(1<<i for i in range(self.d) if x[i]==self.high[i])
        if not free:
            need(self.cap(code) is None,'removed base vertex');return code,None
        p=free[0]; choices=[(c,p) for c in (code,code|(1<<p))
                           if self.cap(c) is not None and p in self.cap(c)['support'] and self.point((c,p))==x]
        need(len(choices)==1,'fractional endpoint is not a unique cap vertex')
        return choices[0]

    def vertex_packet(self,state):
        x=self.point(state);I=list(audit.active(self.A,self.b,x));d=self.d;c,p=state
        need(len(I)==d,'non-simple vertex in purported disjoint-face class')
        R=[[Q(0)]*d for _ in range(d)]
        if p is None:
            for k,row in enumerate(I):
                i=row%d;R[i][k]=1/self.A[row][i]
        else:
            cut=self.cap(c)['row'];need(I[-1]==cut,'wrong active cut')
            a=self.A[cut]
            for k,row in enumerate(I[:-1]):
                i=row%d;R[i][k]=1/self.A[row][i];R[p][k]=-a[i]*R[i][k]/a[p]
            R[p][-1]=1/a[p]
        return {'point':x,'active':I,'basis':I,'inverse':R}

    def anchors(self):
        out={};d=self.d
        for j in range(d):
            for bit in (0,1):
                c=(1<<j) if bit else 0;F=self.cap(c)
                if F is None:x=self.corner(c)
                else:
                    i=next(i for i in F['support'] if i!=j)
                    n=c^(1<<i);G=self.cap(n)
                    x=tuple((a+b)/2 for a,b in zip(self.point((c,i)),
                               self.point((n,i if G is not None else None))))
                need(all(dot(a,x)<b for a,b in zip(self.C,self.rhs)),'no strictly uncut facet seed')
                # Move toward the relative interior of the old box facet.
                center=list(self.center);center[j]=self.high[j] if bit else self.low[j]
                move=tuple(a-b for a,b in zip(center,x));epsilon=Q(1,2)
                for a,b in zip(self.C,self.rhs):
                    epsilon=min(epsilon,(b-dot(a,x))/(2*(abs(dot(a,move))+1)))
                out[j+bit*d]=tuple(a+epsilon*z for a,z in zip(x,move))
        for F in self.cuts.values():
            x=list(self.center);s=len(F['support'])
            for j in F['support']:
                bit=bool(F['pattern']>>j&1)
                x[j]=(self.high[j] if bit else self.low[j])+( -1 if bit else 1)*self.width[j]*F['alpha'][j]/s
            out[F['row']]=tuple(x)
        return [out[i] for i in range(len(self.A))]


def potential(M,c,port,target,target_port,stats=None):
    """Exact expected spliced length; free-face coordinates do not count as hits."""
    rem=c^target;r=rem.bit_count();ans=Q(r)
    for F in M.cuts.values():
        if stats is not None:stats['cut_incidence_tests']+=1
        fixed=F['mask'];wrong=(c^F['pattern']) & fixed
        if wrong & ~rem:continue  # A permanently wrong fixed coordinate.
        enter=wrong & rem;leave=(~wrong) & fixed & rem
        a,b=enter.bit_count(),leave.bit_count()
        if a and b:ans+=Q(1,comb(a+b,a))
        elif not a and b:
            need(port in F['support'],'missing source-face port')
            ans+=1-Q(int(bool(leave & (1<<port))),b)
        elif a and not b:
            need(target_port in F['support'],'missing target-face port')
            ans+=1-Q(int(bool(enter & (1<<target_port))),a)
        else:ans+=int(port!=target_port)  # Entire base path lies in this face.
    return ans


def transition(M,c,port,i):
    F=M.cap(c);n=c^(1<<i);G=M.cap(n)
    if F is not None and i not in F['support']:
        need(G is F,'free coordinate leaves its designated deleted face')
        return n,port,1
    return n,i if G is not None else None,1+int(F is not None and port!=i)


def choose_order(M,start,end):
    c,port=start;target,tp=end;records=[];stats={'cut_incidence_tests':0,'conditional_branches':0}
    while c!=target:
        before=potential(M,c,port,target,tp,stats); candidates=[]
        for i in range(M.d):
            if (c^target)>>i&1:
                nxt,np,cost=transition(M,c,port,i)
                after=potential(M,nxt,np,target,tp,stats)
                candidates.append((Q(cost)+after,i,cost,after));stats['conditional_branches']+=1
        # Tower identity gives a deterministic non-increasing conditional expectation.
        need(sum((x[0] for x in candidates),Q(0))/len(candidates)==before,'expectation recursion failed')
        value,i,cost,after=min(candidates)
        need(value<=before,'conditional choice increased expected total')
        records.append({'corner':c,'arrival_port':port,'next_coordinate':i,
                        'before':before,'immediate_edges':cost,'after':after})
        c,port,_=transition(M,c,port,i)
    return records,stats


def splice(M,start,end,order):
    c,port=start;target,tp=end;states=[start]
    for i in order:
        F=M.cap(c)
        if F is not None and i in F['support'] and port!=i:states.append((c,i))
        c,port,_=transition(M,c,port,i)
        if states[-1]!=(c,port):states.append((c,port))
    need(c==target,'coordinate order does not reach requested corner')
    if states[-1]!=end:states.append(end)
    return states


def path_packet(M,data,states):
    packets=[M.vertex_packet(s) for s in states];edges=[];d=M.d
    for p,q in zip(packets,packets[1:]):
        common=sorted(set(p['active'])&set(q['active']))
        need(len(common)==d-1,'constructed step is not a ridge exchange')
        cols=[p['basis'].index(i) for i in common]
        edges.append({'rows':common,'right_inverse':[[row[j] for j in cols] for row in p['inverse']]})
    return {'format':'original-route-witness-v1',
        'input_sha256':audit.binding(M.A,M.b,tuple(map(rat,data['start'])),tuple(map(rat,data['target']))),
        'vertices':packets,'edges':edges,'length':len(states)-1}


def bind(data):return hashlib.sha256(json.dumps(serial(data),sort_keys=True,separators=(',',':')).encode()).hexdigest()


def construct(data):
    M=Model(data);start=M.identify(data['start']);end=M.identify(data['target'])
    records,stats=choose_order(M,start,end)
    states=splice(M,start,end,[r['next_coordinate'] for r in records])
    c={'format':'disjoint-face-order-route-v1','input_sha256':bind(data),'start_state':start,'target_state':end,
       'cuts':M.cut_certificates,'initial_expectation':potential(M,*start,*end),'decisions':records,
       'strict_point':M.center,'facet_anchors':M.anchors(),'path':path_packet(M,data,states)}
    c=serial(c);return {'certificate':c,'verified':verify(data,c),'discovery':stats}


def verify(data,c):
    """No order search, random trials, inverse construction or route producer."""
    M=Model(data);need(c['format']=='disjoint-face-order-route-v1' and c['input_sha256']==bind(data),'changed input binding')
    start=M.identify(data['start']);end=M.identify(data['target']);v,port=start;target,tp=end
    need(c['start_state']==list(start) and c['target_state']==list(end),'false endpoint state')
    need(c['cuts']==serial(M.cut_certificates),'false face-cut certificate')
    initial=potential(M,v,port,target,tp);need(rat(c['initial_expectation'])==initial,'false initial expectation')
    used=[];total=0
    for rec in c['decisions']:
        i=rec['next_coordinate'];need(type(i)is int and 0<=i<M.d and (v^target)>>i&1,'not a remaining coordinate')
        need(rec['corner']==v and rec['arrival_port']==port,'changed conditional prefix')
        nxt,np,cost=transition(M,v,port,i)
        before=potential(M,v,port,target,tp);after=potential(M,nxt,np,target,tp)
        need(rat(rec['before'])==before and rat(rec['after'])==after and rec['immediate_edges']==cost,'false conditional cost')
        need(cost+after<=before,'conditional expectation increase')
        total+=cost;used.append(i);v=nxt;port=np
    need(v==target,'unfinished coordinate chain')
    total+=int(M.cap(v) is not None and port!=tp)
    expected_states=splice(M,start,end,used)
    raw={'A':M.A,'b':M.b,'start':data['start'],'target':data['target']}
    geometry=audit.verify_path(raw,c['path'])
    need([tuple(map(rat,p['point'])) for p in c['path']['vertices']]==[M.point(s) for s in expected_states],
         'path not the chosen original-edge splice')
    need(total==geometry['original_edges'] and total<=initial,'realized route exceeds expectation')
    need(geometry['original_row_reentries']==0,'original facet was revisited')
    common=set(audit.active(M.A,M.b,tuple(map(rat,data['start']))))&set(audit.active(M.A,M.b,tuple(map(rat,data['target']))))
    need(all(common<=set(p['active']) for p in c['path']['vertices']),'lost a common original facet')
    strict=tuple(map(rat,c['strict_point']));need(len(strict)==M.d and all(dot(a,strict)<b for a,b in zip(M.A,M.b)),'bad strict point')
    anchors=c['facet_anchors'];need(len(anchors)==len(M.A),'missing genuine-facet witness')
    for i,x in enumerate(anchors):
        x=tuple(map(rat,x));need(len(x)==M.d and dot(M.A[i],x)==M.b[i] and
            all(dot(a,x)<b for j,(a,b) in enumerate(zip(M.A,M.b)) if j!=i),'false genuine-facet anchor')
    need(total<=len(M.A)-M.d and total<=2*M.d,'Hirsch/2d class bound exceeded')
    return {'status':'PASS','dimension':M.d,'genuine_original_facets':len(M.A),'cut_faces':len(M.cuts),'noncorner_cuts':sum(len(F['support'])<M.d for F in M.cuts.values()),
        'different_base_coordinates':(start[0]^end[0]).bit_count(), 'expected_length':str(initial),
        'integer_bound':initial.numerator//initial.denominator,**geometry,'common_original_facets':len(common),
        'global_class_bound':min(M.d+len(M.cuts),2*M.d),
        'scope':'Exact recognized disjoint-face class, not arbitrary cuts or shortest-route optimality; no Lean verification.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    data=json.loads(a.input.read_text());out=verify(data,json.loads(a.certificate.read_text())) if a.certificate else construct(data)
    a.output.write_text(json.dumps(serial(out),sort_keys=True,indent=2)+'\n')
if __name__=='__main__':main()
