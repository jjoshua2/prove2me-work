#!/usr/bin/env python3
"""Find the minimal projected face and decide an image-edge query from endpoints.

Inputs: original rational A,b, linear image matrix G, and feasible distinct image
points u,v. No selected original rows, exposing objective, preimage endpoints,
rank claim or graph are supplied. Exact LP discovery has explicit pivot caps.
A successful EDGE is checked by #246's unchanged arithmetic auditor. A NO_EDGE
returns either a transverse midpoint decomposition or a nonextreme endpoint.
The independent verifier calls neither an LP nor rank/elimination routines.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as Q
from pathlib import Path
import sympy as sp
from exact_farkas_lp import (ExactLP, Unbounded, parse, rat, serial, dot,
    require, feasible_point, verify_dual, dense_dual)
from projected_face_certificate import audit as audit_edge, row_coefficients


def vec(v,n):
    require(isinstance(v,(list,tuple)) and len(v)==n,'wrong vector shape')
    return tuple(map(rat,v))


def image(G,x): return tuple(dot(g,x) for g in G)
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(t,x): return tuple(t*v for v in x)


def read_input(data):
    A,b=parse(data['A'],data['b']);n=len(A[0]);G=tuple(vec(g,n) for g in data['G'])
    require(G,'positive image ambient dimension required');u=vec(data['u'],len(G));v=vec(data['v'],len(G))
    require(u!=v,'distinct image endpoints required')
    return A,b,G,u,v


def digest(A,b,G,u,v):
    return hashlib.sha256(json.dumps(serial([A,b,G,u,v]),separators=(',',':')).encode()).hexdigest()


def fibre_system(A,b,G,z):
    return A+G+tuple(scale(-1,g) for g in G), b+z+scale(-1,z)


def face_system(A,b,J):
    # Original rows already contain the <= half of the selected equalities.
    return A+tuple(scale(-1,A[j]) for j in J), b+tuple(-b[j] for j in J)


def rank_one_modulo_rows(A,J,G,delta):
    pivot=next(i for i,x in enumerate(delta) if x);phi=scale(1/delta[pivot],G[pivot])
    W=[[Q(0)]*len(G) for _ in J]
    for l in range(len(G)):
        coeff=row_coefficients([A[j] for j in J],sub(G[l],scale(delta[l],phi)))
        if coeff is None:return None
        for j,c in enumerate(coeff):W[j][l]=c
    return phi,W


def small_step(A,b,x,z):
    # This is arithmetic, not a guessed numerical tolerance.
    return min([Q(1)]+[(t-dot(a,x))/(2*abs(dot(a,z))) for a,t in zip(A,b) if dot(a,z)])


def discover(data,pivot_cap=20000):
    A,b,G,u,v=read_input(data);n=len(A[0]);m=len(A);p=len(G);mid=scale(Q(1,2),add(u,v))
    lifts=[]
    for w in (u,v):
        C,d=fibre_system(A,b,G,w);lifts.append(feasible_point(C,d,pivot_cap=pivot_cap))
    x,y=lifts;C,d=fibre_system(A,b,G,mid);seed=scale(Q(1,2),add(x,y))
    lp=ExactLP(C,d,seed,pivot_cap);J=[];zero_proofs=[];strict=[seed];unbounded=0
    for i,a in enumerate(A):
        objective=scale(-1,a)
        try:
            opt=lp.maximize(objective);s=b[i]+rat(opt['value'])
            require(s>=0,'invalid negative maximum slack')
            if s==0:
                J.append(i);zero_proofs.append({'row':i,'dual':opt['dual']})
            else:strict.append(vec(opt['point'],n))
        except Unbounded as e:
            w=add(e.point,e.direction)
            require(b[i]-dot(a,w)>0,'unbounded slack witness has no positive slack')
            strict.append(w);unbounded+=1
    anchor=tuple(sum(w[k] for w in strict)/len(strict) for k in range(n))
    require(image(G,anchor)==mid,'anchor left midpoint fibre')
    require(all((dot(a,anchor)==t)==(i in J) for i,(a,t) in enumerate(zip(A,b))),
            'averaged witnesses do not give the exact active set')
    weights=[Q(1)]*len(J);normal=[Q(0)]*p
    for q in zero_proofs:
        drow=dense_dual(q['dual'],len(C));verify_dual(C,d,scale(-1,A[q['row']]),q['dual'])
        require(all(not drow[k] or k in J for k in range(m)),'dual uses a row slack at anchor')
        for j,k in enumerate(J):weights[j]+=drow[k]
        for l in range(p):normal[l]-=drow[m+l]-drow[m+p+l]
    face={'anchor':anchor,'selected_rows':J,'zero_slack_duals':zero_proofs,
          'normal':normal,'positive_weights':weights}
    verify_face(A,b,G,mid,face)
    delta=sub(v,u);positive=rank_one_modulo_rows(A,J,G,delta)
    if positive is None:
        # This nullspace is untrusted discovery only. The returned feasible
        # points and a nonzero 2x2 image minor are independently audited.
        M=sp.Matrix([list(A[j]) for j in J]) if J else sp.zeros(0,n)
        z=None
        for raw in M.nullspace():
            cand=tuple(Q(str(t)) for t in raw);w=image(G,cand)
            if any(w[i]*delta[j]!=w[j]*delta[i] for i in range(p) for j in range(p)):
                z=cand;break
        require(z is not None,'inconsistent row-factorization/nullspace search')
        eps=small_step(A,b,anchor,z);require(eps>0,'no positive face step')
        result={'status':'NO_EDGE','kind':'transverse_midpoint',
                'minus':sub(anchor,scale(eps,z)),'plus':add(anchor,scale(eps,z))}
    else:
        phi,W=positive;E,rhs=face_system(A,b,J);face_lp=ExactLP(E,rhs,anchor,pivot_cap)
        extremes=[];result=None
        for sign,endpoint in [(-1,x),(1,y)]:
            objective=scale(sign,phi)
            try:
                opt=face_lp.maximize(objective);w=vec(opt['point'],n)
                bound=rat(opt['value']);wanted=dot(objective,endpoint)
                require(bound>=wanted,'face endpoint infeasible')
                if bound>wanted:
                    result=outside_witness(A,b,G,u,v,x,y,w,sign);break
                full=dense_dual(opt['dual'],len(E));ineq=full[:m];eq=tuple(-full[m+j] for j in range(len(J)))
                extremes.append((ineq,eq))
            except Unbounded as e:
                wanted=dot(objective,endpoint);step=max(Q(1),(wanted-dot(objective,e.point)+1)/dot(objective,e.direction))
                w=add(e.point,scale(step,e.direction));result=outside_witness(A,b,G,u,v,x,y,w,sign);break
        if result is None:
            lo,gl=extremes[0];up,gu=extremes[1]
            edge={'x':x,'y':y,'rows':J,'weights':weights,'normal':normal,
                  'coordinate':phi,'residual':W,'lower':lo,'upper':up,'lower_eq':gl,'upper_eq':gu}
            audit_edge(A,b,G,edge)
            result={'status':'EDGE','edge_certificate':edge}
    cert=serial({'problem_sha256':digest(A,b,G,u,v),'endpoint_lifts':[x,y],
                 'face_certificate':face,'result':result})
    return {'certificate':cert,'verified':verify(data,cert),
            'discovery':{'slack_LP_calls':lp.calls,'slack_LP_pivots':lp.pivots,
                         'unbounded_slack_objectives':unbounded,
                         'rank_solver':'rational elimination; not used by the auditor'}}


def outside_witness(A,b,G,u,v,x,y,w,sign):
    delta=sub(v,u);k=next(i for i,d in enumerate(delta) if d)
    t=(image(G,w)[k]-u[k])/delta[k]
    require(image(G,w)==add(u,scale(t,delta)),'endpoint LP produced off-line point')
    require(t<0 if sign==-1 else t>1,'point is not beyond candidate endpoint')
    return {'status':'NO_EDGE','kind':'nonextreme_endpoint','outside':w,
            'outside_parameter':t,'endpoint':0 if sign==-1 else 1}


def verify_face(A,b,G,mid,face):
    n=len(A[0]);m=len(A);p=len(G);anchor=vec(face['anchor'],n)
    J=face['selected_rows'];require(type(J)is list and J==sorted(set(J)) and
        all(type(j)is int and 0<=j<m for j in J),'invalid selected-row list')
    require(image(G,anchor)==mid and all(dot(a,anchor)<=t for a,t in zip(A,b)),
            'invalid midpoint-fibre anchor')
    require(all((dot(a,anchor)==t)==(j in J) for j,(a,t) in enumerate(zip(A,b))),
            'anchor is not strict off the selected rows')
    C,d=fibre_system(A,b,G,mid);seen=set();normal=[Q(0)]*p;weights=[Q(1)]*len(J)
    for item in face['zero_slack_duals']:
        j=item['row'];require(type(j)is int and j in J and j not in seen,'invalid repeated zero-slack witness');seen.add(j)
        bound=verify_dual(C,d,scale(-1,A[j]),item['dual']);require(bound==-b[j],'slack proof not exactly zero')
        w=dense_dual(item['dual'],len(C))
        require(all(not w[i] or i in J for i in range(m)),'noncomplementary selected-row proof')
        for l,i in enumerate(J):weights[l]+=w[i]
        for l in range(p):normal[l]-=w[m+l]-w[m+p+l]
    require(seen==set(J),'missing forced-equality certificate')
    require(vec(face['normal'],p)==tuple(normal) and vec(face['positive_weights'],len(J))==tuple(weights),
            'normal or positive weights not the constructed ones')
    require(all(t>0 for t in weights),'not a strict exposing combination')
    for k in range(n):
        require(sum(normal[l]*G[l][k] for l in range(p))==sum(weights[l]*A[j][k] for l,j in enumerate(J)),
                'false image exposure column identity')
    require(dot(normal,mid)==sum(weights[l]*b[j] for l,j in enumerate(J)),'wrong image support value')
    return {'selected_rows':len(J),'original_rows':m,'source_dimension':n,
            'strict_off_face':True,'image_exposing_normal_constructed':True}


def verify(data,c):
    """No simplex, rank, nullspace, row solve, or vertex enumeration is called."""
    A,b,G,u,v=read_input(data);n=len(A[0]);mid=scale(Q(1,2),add(u,v));delta=sub(v,u)
    require(c['problem_sha256']==digest(A,b,G,u,v),'changed problem or endpoints')
    lifts=c['endpoint_lifts'];require(len(lifts)==2,'missing endpoint lifts')
    for raw,w in zip(lifts,(u,v)):
        z=vec(raw,n);require(image(G,z)==w and all(dot(a,z)<=t for a,t in zip(A,b)),
                            'invalid original endpoint lift')
    report=verify_face(A,b,G,mid,c['face_certificate']);r=c['result']
    if r['status']=='EDGE':
        proof=r['edge_certificate'];ev=audit_edge(A,b,G,proof)
        require(tuple(ev['image_start'])==u and tuple(ev['image_end'])==v,'edge certificate changes requested image points')
        require(proof['rows']==c['face_certificate']['selected_rows'] and
                vec(proof['normal'],len(G))==vec(c['face_certificate']['normal'],len(G)),
                'edge proof is not tied to the discovered face')
        return {**report,'status':'EDGE','original_image_edge':True,'whole_image_face_certified':True,
                'column_identity_checks':ev['column_identity_checks'],
                'scope':'Exact #246 edge evidence plus derived face. No bound on total route length or Lean-extracted JSON claim.'}
    require(r['status']=='NO_EDGE','unknown result')
    if r['kind']=='transverse_midpoint':
        a=vec(r['minus'],n);z=vec(r['plus'],n)
        for w in (a,z):require(all(dot(row,w)<=t for row,t in zip(A,b)),'infeasible transverse witness')
        im,ip=image(G,a),image(G,z);require(scale(Q(1,2),add(im,ip))==mid,'wrong midpoint decomposition')
        d=sub(ip,im);require(any(d[i]*delta[j]!=d[j]*delta[i] for i in range(len(G)) for j in range(len(G))),
                            'claimed transverse direction is parallel')
    elif r['kind']=='nonextreme_endpoint':
        w=vec(r['outside'],n);t=rat(r['outside_parameter']);k=r['endpoint']
        require(type(k)is int and k in (0,1),'invalid endpoint label')
        require(all(dot(a,w)<=s for a,s in zip(A,b)),'infeasible outside point')
        require(image(G,w)==add(u,scale(t,delta)),'outside point not on image line')
        require(t<0 if k==0 else t>1,'no extension beyond the endpoint')
    else:raise ValueError('unknown negative witness')
    return {**report,'status':'NO_EDGE','negative_kind':r['kind'],
            'scope':'An explicit feasible convex-decomposition witness refutes extremality; not a failed-search inference.'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path);p.add_argument('--certificate',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--pivot-cap',type=int,default=20000);args=p.parse_args()
    try:
        data=json.loads(args.input.read_text());out=verify(data,json.loads(args.certificate.read_text())) if args.certificate else discover(data,args.pivot_cap)
        text=json.dumps(serial(out),indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except (ValueError,KeyError,TypeError,ZeroDivisionError,OSError) as exc:
        p.exit(2,f'No completed image-edge decision: {exc}\n')
if __name__=='__main__':main()
