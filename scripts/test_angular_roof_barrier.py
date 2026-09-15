#!/usr/bin/env python3
"""Exact fixed-facet angular-stall test, not a diameter lower bound."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib,time
import projective_slack_acquisition as policy
import test_two_face_acquisition as ref
old=policy.old;base=policy.base;require=policy.require;dot=policy.dot
ROOT=Path(__file__).resolve().parents[1]
SITES=[(Q(1),Q(0)),(-Q(3,5),Q(4,5)),(-Q(3,5),-Q(4,5)),
       (Q(4),Q(1)),(Q(1),Q(5)),(-Q(4),Q(3)),(-Q(5),-Q(1)),
       (-Q(1),-Q(4)),(Q(3),-Q(5))]

def model(delta):
    require(Q(0)<delta<=Q(1,64),'delta outside proved positive range')
    A=[[-Q(i==j) for j in range(3)] for i in range(3)];b=[Q(0)]*3
    for p,q in SITES:
        k=1-Q(2,3)*delta*(p+q)-delta*delta*(p*p+q*q)
        A.append([k+2*delta*p,k+2*delta*q,k]);b.append(Q(1))
    x=[1/(3*(1-delta*delta))]*3;v=[Q(0)]*3
    return A,b,x,v

def experiment(power,reference=True):
    delta=Q(1,2**power);A,b,x,v=model(delta)
    # Positive rows imply a bounded original polytope. Target has only lower facets.
    require(all(a>0 for row in A[3:] for a in row),'positive roof coefficients')
    target=base.basis_packet(A,b,v);source=base.basis_packet(A,b,x)
    require(source['active']==[3,4,5] and target['active']==[0,1,2],'root/target incidence')
    c=policy.produce(A,b,x,target,x,{});arc,info=policy.audit_decision(A,b,x,target,c)
    require(info['kind']=='face_descent','local roof must have no target acquisition')
    rho0=policy.score(A,b,x,x,target['active']);rho1=policy.score(A,b,x,arc[-1],target['active'])
    C=(rho0-rho1)/delta
    coords=[]
    for face in c['faces']:
        for bs in face['corners']:
            p=bs['point'];s=sum(p);u=[p[i]/s for i in range(3)]
            coords.append([(u[0]-Q(1,3))/delta,(u[1]-Q(1,3))/delta])
            require(all(q>0 for q in u),'first-star roof hits boundary')
    out=policy.construct(A,b,x,v)
    record={'power':power,'delta':str(delta),'dimension':3,'original_facets':len(A),
        'rho_before':str(rho0),'rho_after':str(rho1),'exact_deficit_over_delta':str(C),
        'first_macro_edges':len(arc),'total_route_edges':out['verified']['committed_edges'],
        'first_faces':len(c['faces']),'first_face_corners':[len(f['corners']) for f in c['faces']],
        'first_face_labels':[f['fixed_rows'] for f in c['faces']],
        'local_scaled_angular_vertices':policy.serial(sorted(set(tuple(p) for p in coords))),
        'first_macro_vertices':policy.serial(arc),'normalized_step_gain_fraction':str((rho0-rho1)/rho0)}
    if reference:
        V,G,anchors=ref.reference(A,b)
        require(all(len(I)==3 for I in V.values()),'nonsimple full model')
        require(all(tuple(z) in G[tuple(y)] for y,z in zip(out['verified']['path'],out['verified']['path'][1:])),'bad graph step')
        record.update(vertices=len(V),edges=sum(map(len,G.values()))//2,shortest=ref.distances(G,tuple(x))[tuple(v)])
        record['vertex_active_sets']=sorted([sorted(I) for I in V.values()])
    return record,{'input':{'A':A,'b':b,'start':x,'target':v},**out,'first_decision':c}

def certify_parameter_family():
    """Certify all positive delta<=1/64 using exact polynomial coefficients.
    Twenty strict feasible three-row vertices attain the universal 3-polytope
    vertex upper bound 2*m-4. Thus no hidden extra/non-simple vertex is omitted.
    """
    import sympy as sp
    from math import comb
    z=sp.Symbol('delta');t=sp.Symbol('t')
    A=[];b=[]
    for i in range(3):A.append([-sp.Integer(i==j) for j in range(3)]);b.append(sp.Integer(0))
    for p,q in SITES:
        p,q=sp.Rational(p),sp.Rational(q)
        k=1-sp.Rational(2,3)*z*(p+q)-z*z*(p*p+q*q)
        A.append([k+2*z*p,k+2*z*q,k]);b.append(sp.Integer(1))
    AA,bb,x,v=model(Q(1,64));V,G,anchors=ref.reference(AA,bb)
    active=sorted([sorted(I) for I in V.values()])
    require(len(active)==20 and all(len(I)==3 for I in active),'twenty simple vertices required')
    def positive(poly):
        poly=sp.Poly(sp.expand(poly),z)
        coeff=poly.as_dict();power=min(k[0] for k,c in coeff.items() if c)
        reduced=sp.cancel(poly.as_expr()/z**power)
        R=sp.Poly(sp.expand(reduced.subs(z,t/64)),t);n=R.degree()
        c=[R.nth(i) for i in range(n+1)]
        beta=[sp.cancel(sum(c[i]*sp.Rational(comb(k,i),comb(n,i)) for i in range(k+1))) for k in range(n+1)]
        require(all(x>=0 for x in beta) and any(x>0 for x in beta) and beta[-1]>0,
                'polynomial does not have a positive Bernstein certificate')
        return {'delta_power':power,'bernstein_coefficients':[str(v) for v in beta]}
    rows=[];strict=0;zeros=0;star=[]
    for I in active:
        matrix=sp.Matrix([A[i] for i in I]);point=matrix.inv()*sp.Matrix([b[i] for i in I])
        det=sp.factor(matrix.det())
        orientation=1 if det.subs(z,sp.Rational(1,64))>0 else -1
        determinant=positive(orientation*det)
        evidence=[]
        if set(I)&{3,4,5}:
            require(not set(I)&{0,1,2},'source star touches a target facet')
            total=sum(point)
            angular=[sp.cancel((point[k]/total-sp.Rational(1,3))/z) for k in range(3)]
            require(all(not q.free_symbols for q in angular),'angular star does not scale linearly')
            star.append(angular)
        for j,row in enumerate(A):
            f=sp.cancel(b[j]-sum(row[k]*point[k] for k in range(3)))
            if j in I:
                require(f==0,'active equality not exact');zeros+=1;continue
            num,den=sp.fraction(f)
            if den.subs(z,sp.Rational(1,64))<0:num,den=-num,-den
            evidence.append({'row':j,'numerator':positive(num),'denominator':positive(den)})
            strict+=1
        rows.append({'active':I,'determinant_sign':orientation,'determinant_certificate':determinant,'coordinates':[str(sp.cancel(v)) for v in point],'strict_slacks':evidence})
    require(strict==180 and zeros==60,'wrong complete slack counts')
    require(len(star)==10 and min(v for point in star for v in point)==-sp.Rational(13,3),'wrong exact angular gap coefficient')
    # Every roof facet has a relative-interior point at the site's own Voronoi
    # location; all sites lie strictly inside the base simplex for this range.
    require(all(Q(1,3)+Q(p,64)>0 and Q(1,3)+Q(q,64)>0 and Q(1,3)-Q(p+q,64)>0 for p,q in SITES),'site left simplex')
    return {'parameter_interval':'0 < delta <= 1/64','verified_simple_vertex_bases':20,
            'source_star_vertices':len(star),'first_fallback_rho':'(1-13*delta)/3','relative_rho_gain':'13*delta',
            'nonsingular_basis_determinants':20,'exact_active_equalities':zeros,'strict_original_slack_certificates':strict,
            'all_parameter_constant_vertex_incidences':True,'genuine_facets':12,
            'proof_of_no_other_vertices':'20 simple feasible vertices attain v <= 2*f-4 with f<=12 for bounded full-dimensional 3-polytopes.',
            'polynomial_certificate_method':'After removing a positive power of delta, nonnegative Bernstein coefficients on t=64*delta in [0,1], with positive endpoint coefficient.',
            'vertices':rows}

def main():
    (ROOT/'research').mkdir(exist_ok=True);(ROOT/'fixtures').mkdir(exist_ok=True)
    results=[];C=None;active=None;angular=None;start=time.monotonic()
    for power in [6,10,40,120,240]:
        r,c=experiment(power)
        if C is None:C=r['exact_deficit_over_delta'];active=r['vertex_active_sets'];angular=r['local_scaled_angular_vertices']
        require(r['exact_deficit_over_delta']==C,'angular coefficient varies')
        require(r['vertex_active_sets']==active,'combinatorial type changes')
        require(r['local_scaled_angular_vertices']==angular,'roof star scaling failed')
        results.append(r);print(power,C,r['first_macro_edges'],r['total_route_edges'],r['vertices'],r['shortest'],flush=True)
        if power in (6,240):
            (ROOT/f'fixtures/angular_roof_{power}.json').write_text(json.dumps(policy.serial(c),indent=2,sort_keys=True)+'\n')
    param=certify_parameter_family()
    receipt={'parameter_certificate':param,'status':'PASS','scope':'Exact genuine deformation with fixed facet count and fixed vertex incidences; not a long route or diameter obstruction.',
        'results':results,'sites':policy.serial(SITES),'no_projective_equivalence_assumed':True,
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'policy_sha256':hashlib.sha256((ROOT/'scripts/projective_slack_acquisition.py').read_bytes()).hexdigest(),
        'seconds':round(time.monotonic()-start,3)}
    (ROOT/'research/ANGULAR_ROOF_CHECK.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
if __name__=='__main__':main()
