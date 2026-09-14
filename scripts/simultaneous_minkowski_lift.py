#!/usr/bin/env python3
"""Exact simultaneous Minkowski edge lifting; no summed vertex enumeration.

Input: a certified core (point, box, pyramid over a box, or a complete convex
polygon) and finite rational point-list summands. A decomposition of an
unrelated H-polyhedron is NOT discovered or assumed. All emitted edges have
exact exposed-face certificates in this represented Minkowski sum.
"""
from __future__ import annotations
from fractions import Fraction as F
from dataclasses import dataclass
from typing import Sequence
import itertools, random, json, hashlib, argparse

Vec = tuple[F, ...]

def require(ok: bool, msg: str) -> None:
    if not ok: raise ValueError(msg)

def vec(xs) -> Vec: return tuple(F(x) for x in xs)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def mul(a,x): return tuple(a*b for b in x)
def dot(x,y):
    require(len(x)==len(y), 'dimension mismatch')
    return sum((a*b for a,b in zip(x,y)),F(0))
def vsum(xs,dim):
    out=(F(0),)*dim
    for x in xs: out=add(out,x)
    return out

def segment_member(x,p,q):
    g=sub(q,p); h=sub(x,p)
    j=next((j for j,v in enumerate(g) if v),None)
    if j is None: return x==p
    t=h[j]/g[j]
    return 0<=t<=1 and h==mul(t,g)

def hull2(points):
    """Complete exact monotone-chain planar hull, independent of the sweep."""
    pts=sorted(set(points))
    require(all(len(p)==2 for p in pts),'not planar')
    if len(pts)<2: return tuple(pts)
    def cross(a,b,c):
        u,v=sub(b,a),sub(c,a)
        return u[0]*v[1]-u[1]*v[0]
    def half(ps):
        out=[]
        for p in ps:
            while len(out)>1 and cross(out[-2],out[-1],p)<=0: out.pop()
            out.append(p)
        return out
    return tuple(half(pts)[:-1]+half(list(reversed(pts)))[:-1])

@dataclass(frozen=True)
class Core:
    kind: str
    dim: int
    vertices: tuple[Vec,...]=()

    def __post_init__(self):
        require(self.dim>=1,'positive ambient dimension required by implementation')
        require(self.kind in ('point','box','pyramid','polygon'),'unknown core')
        if self.kind=='pyramid': require(self.dim>=2,'pyramid needs dimension at least two')
        if self.kind=='polygon':
            require(self.dim==2 and len(self.vertices)>=3,'invalid polygon')
            require(self.vertices==hull2(self.vertices),'polygon must be the complete CCW hull')
        if self.kind=='point': require(len(self.vertices)==1 and len(self.vertices[0])==self.dim,'invalid point')

    def face_generators(self,f):
        """Support-face generators; returns only a spanning set for high faces.

        For a box face, a corner and its free coordinate flips suffice to test
        whether the entire face is contained in a proposed segment. Each is an
        actual maximizer, and their affine span is the full face's affine span.
        """
        require(len(f)==self.dim,'core objective dimension')
        if self.kind in ('point','polygon'):
            best=max(dot(f,v) for v in self.vertices)
            return tuple(v for v in self.vertices if dot(f,v)==best)
        n=self.dim if self.kind=='box' else self.dim-1
        corner=tuple(F(1) if f[j]>=0 else F(-1) for j in range(n))
        base=corner if self.kind=='box' else corner+(F(0),)
        pts=[base]
        for j in range(n):
            if not f[j]:
                p=list(base);p[j]=-p[j];pts.append(tuple(p))
        if self.kind=='pyramid':
            apex=(F(0),)*n+(F(1),)
            bv=sum((abs(f[j]) for j in range(n)),F(0))
            if f[-1]>bv: return (apex,)
            if f[-1]==bv: pts.append(apex)
        return tuple(pts)

    def unique(self,f):
        pts=self.face_generators(f)
        require(len(pts)==1,'nonunique core maximum')
        return pts[0]

    def route(self,p,q):
        if p==q:return [p]
        if self.kind=='point': raise ValueError('point core cannot move')
        if self.kind=='pyramid':
            apex=(F(0),)*(self.dim-1)+(F(1),)
            return [p,q] if p==apex or q==apex else [p,apex,q]
        if self.kind=='box':
            path=[p]
            for j in range(self.dim):
                if p[j]!=q[j]:
                    out=list(path[-1]);out[j]=q[j];path.append(tuple(out))
            return path
        a,b=self.vertices.index(p),self.vertices.index(q);n=len(self.vertices)
        step=1 if (b-a)%n<=(a-b)%n else -1
        return [self.vertices[(a+step*j)%n] for j in range(min((b-a)%n,(a-b)%n)+1)]

    def edge_normal(self,p,q,rng):
        if self.kind=='box':
            changed=[j for j in range(self.dim) if p[j]!=q[j]]
            require(len(changed)==1,'not a box edge')
            return tuple(F(0) if j==changed[0] else p[j]*rng.randint(1,13) for j in range(self.dim))
        if self.kind=='pyramid':
            base=p if p[-1]==0 else q
            require((p[-1],q[-1]) in ((0,1),(1,0)),'not a pyramid spoke')
            xs=tuple(base[j]*rng.randint(1,17) for j in range(self.dim-1))
            return xs+(sum(map(abs,xs),F(0)),)
        require(self.kind=='polygon','no edge normal')
        d=sub(q,p);f=(d[1],-d[0])
        if max(dot(f,v) for v in self.vertices)>dot(f,p):f=mul(F(-1),f)
        return f

    def check_face(self,f,p,q):
        gs=self.face_generators(f)
        # Endpoints must also be actual core points, not merely on the span.
        def contains(v):
            if self.kind=='point':return v==self.vertices[0]
            if self.kind=='polygon':
                return v in self.vertices # all used endpoints are vertices
            if self.kind=='box':return all(-1<=x<=1 for x in v)
            return 0<=v[-1]<=1 and all(abs(x)<=1-v[-1] for x in v[:-1])
        require(contains(p) and contains(q),'endpoint outside core')
        beta=dot(f,gs[0])
        require(dot(f,p)==beta and dot(f,q)==beta,'core endpoints not maximal')
        require(all(segment_member(v,p,q) for v in gs),'core face is not the proposed segment')
        return beta

@dataclass(frozen=True)
class Model:
    core: Core
    factors: tuple[tuple[Vec,...],...]
    def __post_init__(self):
        for vs in self.factors:
            require(vs and len(vs)==len(set(vs)),'empty or duplicate point list')
            require(all(len(v)==self.core.dim for v in vs),'factor dimensions')
    @property
    def K(self):return sum(len(vs)-1 for vs in self.factors)
    def choices(self,f):
        out=[]
        for vs in self.factors:
            scores=[dot(f,v) for v in vs];best=max(scores)
            ids=[j for j,x in enumerate(scores) if x==best]
            require(len(ids)==1,'nonunique factor maximum')
            out.append(ids[0])
        return tuple(out)
    def support_state(self,f):return self.core.unique(f),self.choices(f)
    def point(self,state):
        p,choice=state
        return add(p,vsum((vs[j] for vs,j in zip(self.factors,choice)),self.core.dim))
    def check_edge(self,f,left,right):
        """Independent exact face test, using all original factor points.

        Each entire support face is the segment between its two chosen
        endpoints; all nonzero segments must be nonnegative parallel multiples
        of the total direction. Their sum is exactly the exposed total edge.
        """
        p,lc=left;q,rc=right
        require(len(lc)==len(self.factors)==len(rc),'bad state width')
        require(all(isinstance(j,int) and 0<=j<len(vs) for j,vs in zip(lc,self.factors)),'bad left index')
        require(all(isinstance(j,int) and 0<=j<len(vs) for j,vs in zip(rc,self.factors)),'bad right index')
        self.core.check_face(f,p,q)
        pairs=[(p,q)]
        for vs,a,b in zip(self.factors,lc,rc):
            x,y=vs[a],vs[b];beta=max(dot(f,v) for v in vs)
            require(dot(f,x)==beta==dot(f,y),'factor endpoint not exposed')
            require(all(dot(f,v)!=beta or segment_member(v,x,y) for v in vs),'higher-dimensional exposed factor face')
            pairs.append((x,y))
        x,y=self.point(left),self.point(right);g=sub(y,x)
        pivot=next((j for j,v in enumerate(g) if v),None)
        require(pivot is not None,'stationary edge')
        coeff=[]
        for p,q in pairs:
            d=sub(q,p);eta=d[pivot]/g[pivot]
            require(eta>=0 and d==mul(eta,g),'nonparallel or opposing face changes')
            coeff.append(eta)
        require(sum(coeff,F(0))==1,'segment sum mismatch')
        return {'normal':f,'left':left,'right':right,'parallel_weights':tuple(coeff)}

def same_state(model,f,state):
    try:return model.support_state(f)==state
    except ValueError:return False

def jitter(model,f,state,rng):
    noise=tuple(F(rng.randint(-19,19)) for _ in f)
    for e in range(1,90):
        g=add(f,mul(F(1,2**e),noise))
        if same_state(model,g,state):return g
    raise ValueError('jitter cap; no incomplete certificate returned')

def sweep_once(model,fa,fb,core_vertex):
    require(model.core.unique(fa)==core_vertex==model.core.unique(fb),'fibre endpoints not in the same open core cone')
    direction=sub(fb,fa);times={F(0),F(1)}
    for vs in model.factors:
        for u,v in itertools.combinations(vs,2):
            d=sub(u,v);b=dot(direction,d)
            if b:
                t=-dot(fa,d)/b
                if 0<t<1:times.add(t)
    times=sorted(times);mids=[(u+v)/2 for u,v in zip(times,times[1:])]
    states=[(core_vertex,model.choices(add(fa,mul(t,direction)))) for t in mids]
    require(states[0]==model.support_state(fa) and states[-1]==model.support_state(fb),'endpoint mismatch')
    chosen=[states[0]];samples=[mids[0]];edges=[];wall_times=[]
    for j in range(1,len(states)):
        if states[j]!=chosen[-1]:
            f=add(fa,mul(times[j],direction))
            edges.append(model.check_edge(f,chosen[-1],states[j]))
            wall_times.append(times[j]);chosen.append(states[j]);samples.append(mids[j])
    return {'f0':fa,'f1':fb,'core':core_vertex,'states':chosen,'samples':samples,
            'wall_times':wall_times,'edges':edges}

def sweep(model,fa,fb,rng):
    left,right=model.support_state(fa),model.support_state(fb)
    require(left[0]==right[0],'different core fibres')
    for attempt in range(80):
        a=fa if not attempt else jitter(model,fa,left,rng)
        b=fb if not attempt else jitter(model,fb,right,rng)
        try:
            out=sweep_once(model,a,b,left[0]);check_sweep(model,out);out['generic_attempt']=attempt;return out
        except ValueError: pass
    raise ValueError('generic sweep cap; no incomplete route returned')

def check_sweep(model,cert):
    """Verify without running the event enumerator or constructor."""
    fa,fb=cert['f0'],cert['f1'];p=cert['core'];ss=cert['states'];ts=cert['samples'];es=cert['edges']
    require(len(ss)==len(ts)==len(es)+1 and len(es)==len(cert['wall_times']),'sweep lengths')
    require(ss[0]==model.support_state(fa) and ss[-1]==model.support_state(fb),'wrong sweep endpoints')
    require(model.core.unique(fa)==p==model.core.unique(fb),'invalid fibre cone')
    require(all(0<t<1 for t in ts) and all(a<b for a,b in zip(ts,ts[1:])),'sample order')
    direction=sub(fb,fa)
    ranks=[]
    for t,s in zip(ts,ss):
        require(s[0]==p and model.support_state(add(fa,mul(t,direction)))==s,'false affine maximum')
        ranks.append(sum(sum(dot(direction,v)<dot(direction,vs[j]) for v in vs)
                         for vs,j in zip(model.factors,s[1])))
    for j,e in enumerate(es):
        require(e['left']==ss[j] and e['right']==ss[j+1],'edge/choice mismatch')
        require(ts[j]<cert['wall_times'][j]<ts[j+1],'wall outside sample interval')
        require(e['normal']==add(fa,mul(cert['wall_times'][j],direction)),'wrong affine wall')
        check=model.check_edge(e['normal'],e['left'],e['right'])
        require(check==e,'forged parallel weights')
        require(ranks[j+1]>ranks[j],'affine envelope rank failed to increase')
    require(len(es)+ranks[0]<=ranks[-1]<=model.K,'additive vertex budget violated')
    return len(es)

def bridge(model,p,q,rng):
    for _ in range(80):
        f=model.core.edge_normal(p,q,rng);g=sub(q,p)
        # Shrinking epsilon cannot fix a non-generic wall.
        pivot=next(j for j,x in enumerate(g) if x)
        wall_ok=True
        for vs in model.factors:
            beta=max(dot(f,v) for v in vs)
            top=[v for v in vs if dot(f,v)==beta]
            for v in top[1:]:
                d=sub(v,top[0]);t=d[pivot]/g[pivot]
                if d!=mul(t,g):wall_ok=False;break
            if not wall_ok:break
        if not wall_ok:continue
        for power in range(1,90):
            eps=F(1,2**power);fa=sub(f,mul(eps,g));fb=add(f,mul(eps,g))
            try:
                a,b=model.support_state(fa),model.support_state(fb)
                if a[0]!=p or b[0]!=q:continue
                e=model.check_edge(f,a,b)
                return {'f0':fa,'f1':fb,'edge':e}
            except ValueError: continue
    raise ValueError('bridge cap; no incomplete route returned')

def lift(model,fa,fb,seed=1):
    rng=random.Random(seed);a,b=model.support_state(fa),model.support_state(fb)
    path=model.core.route(a[0],b[0]);connectors=[bridge(model,p,q,rng) for p,q in zip(path,path[1:])]
    fibres=[]
    for j,p in enumerate(path):
        x=fa if not j else connectors[j-1]['f1']
        y=fb if j==len(path)-1 else connectors[j]['f0']
        fibres.append(sweep(model,x,y,rng))
    out={'start_objective':fa,'end_objective':fb,'core_path':path,'fibres':fibres,'bridges':connectors}
    out['summary']=check_lift(model,out)
    return out

def check_lift(model,cert):
    a,b=model.support_state(cert['start_objective']),model.support_state(cert['end_objective'])
    ps=cert['core_path'];fs=cert['fibres'];bs=cert['bridges']
    require(ps and len(fs)==len(ps)==len(bs)+1,'lift lengths')
    require(ps[0]==a[0] and ps[-1]==b[0],'wrong projected endpoints')
    require(fs[0]['states'][0]==a and fs[-1]['states'][-1]==b,'wrong lifted endpoints')
    edges=[];cost=0
    for j,f in enumerate(fs):
        require(f['core']==ps[j],'wrong fibre label')
        cost+=check_sweep(model,f);edges+=f['edges']
        if j<len(bs):
            c=bs[j];e=c['edge']
            require(e['left'][0]==ps[j] and e['right'][0]==ps[j+1],'wrong projected edge')
            require(model.support_state(c['f0'])==e['left'] and model.support_state(c['f1'])==e['right'],'bridge endpoint exposure')
            require(model.check_edge(e['normal'],e['left'],e['right'])==e,'bad bridge face')
            require(f['states'][-1]==e['left'] and fs[j+1]['states'][0]==e['right'],'noncontiguous lift')
            edges.append(e);cost+=1
    L=len(bs);bound=L+(L+1)*model.K
    require(cost<=bound,'summed lift budget failed')
    for u,v in zip(edges,edges[1:]):require(u['right']==v['left'],'route gap')
    return {'core_edges':L,'factor_vertex_budget':model.K,'fibre_edges':cost-L,
            'ordinary_edges':cost,'additive_bound':bound,
            'iterated_vertex_bound':(L+1)*__import__('math').prod(len(vs) for vs in model.factors)-1,
            'exposed_edge_certificates':len(edges),'generic_retries':sum(f['generic_attempt'] for f in fs)}

def to_json(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,Core):return {'kind':x.kind,'dim':x.dim,'vertices':to_json(x.vertices)}
    if isinstance(x,Model):return {'core':to_json(x.core),'factors':to_json(x.factors)}
    if isinstance(x,dict):return {k:to_json(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [to_json(v) for v in x]
    return x

def load_bundle(path):
    """Deserialize exact rationals and verify a saved certificate, independently
    of event enumeration, generic search, or route construction."""
    import re
    def decode(x):
        if isinstance(x,str) and re.fullmatch(r'-?\d+(?:/\d+)?',x):return F(x)
        if isinstance(x,list):return tuple(decode(v) for v in x)
        if isinstance(x,dict):return {k:decode(v) for k,v in x.items()}
        return x
    raw=decode(json.loads(__import__('pathlib').Path(path).read_text()))
    m=raw['model'];c=m['core'];model=Model(Core(c['kind'],c['dim'],c['vertices']),m['factors'])
    result=check_lift(model,raw['certificate'])
    require(result==raw['certificate']['summary'],'serialized summary is not the verified count')
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',required=True,help='Exact JSON bundle to verify')
    args=parser.parse_args()
    print(json.dumps(load_bundle(args.verify),indent=2))
