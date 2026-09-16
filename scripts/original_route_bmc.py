#!/usr/bin/env python3
"""Search a bounded number of ORIGINAL polyhedron edges using rational SMT.

No vertex/face graph or refinement is an input. Degeneracy and redundant rows
are allowed. The default exact linear encoding uses selector-guarded rational
right inverses; the smaller alternative learns exact row-dependence exclusions.
Positive certificates are checked without the solver, floating arithmetic, or
matrix elimination. UNSAT remains a solver result, not an independently checked
proof of optimality. A timeout, encoding cap, or round cap is UNKNOWN, not UNSAT.
The mathematical formulation also allows unbounded or lower-dimensional H
presentations with actual vertex endpoints. No boundedness assertion is inferred.

The optional backend uses the installed Z3 C API (or the shared library bundled
with z3-solver). The certificate checker needs only Python's standard library.
"""
from __future__ import annotations
from fractions import Fraction as Q
from pathlib import Path
from itertools import combinations
import argparse, ctypes as C, ctypes.util, hashlib, json, os, re, time


def require(ok, message):
    if not ok: raise ValueError(message)


def rat(x):
    require(type(x) in (int,str,Q), 'exact integer/rational string required; floats/bools rejected')
    return Q(x)


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x


def dot(a,b):
    require(len(a)==len(b),'dot-product dimension mismatch')
    return sum((x*y for x,y in zip(a,b)),Q(0))


def parse(data):
    A=[list(map(rat,a)) for a in data['A']]; b=list(map(rat,data['b']))
    require(A and A[0] and len(A)==len(b) and all(len(a)==len(A[0]) for a in A),'bad H dimensions')
    u=list(map(rat,data['start']));v=list(map(rat,data['target']));d=len(A[0])
    require(len(u)==len(v)==d,'bad endpoint dimensions')
    return A,b,u,v


def binding(A,b,u,v):
    return hashlib.sha256(json.dumps(serial([A,b,u,v]),separators=(',',':')).encode()).hexdigest()


def row_reduce(rows):
    """Exact elimination, returning rank, pivot columns, and a row dependency.
    A dependency concerns the original row list, not a solver valuation.
    """
    n=len(rows); d=len(rows[0]) if n else 0
    require(all(len(r)==d for r in rows),'ragged row matrix')
    M=[list(map(rat,r)) for r in rows]
    T=[[Q(i==j) for j in range(n)] for i in range(n)]
    piv=[];q=0
    for col in range(d):
        r=next((r for r in range(q,n) if M[r][col]),None)
        if r is None: continue
        M[q],M[r]=M[r],M[q];T[q],T[r]=T[r],T[q]
        a=M[q][col];M[q]=[x/a for x in M[q]];T[q]=[x/a for x in T[q]]
        for j in range(n):
            if j!=q and M[j][col]:
                a=M[j][col];M[j]=[x-a*y for x,y in zip(M[j],M[q])]
                T[j]=[x-a*y for x,y in zip(T[j],T[q])]
        piv.append(col);q+=1
        if q==n: break
    return q,piv,T[q] if q<n else None,T


def right_inverse(rows,d):
    n=len(rows)
    if not n:return [[] for _ in range(d)]
    rank,piv,dep,_=row_reduce(rows)
    require(rank==n,'dependent row matrix')
    square=[[row[j] for j in piv] for row in rows]
    rr,pp,dd,T=row_reduce(square)
    require(rr==n and pp==list(range(n)),'inverse construction failed')
    out=[[Q(0)]*n for _ in range(d)]
    for j,col in enumerate(piv):out[col]=T[j]
    return out


def independent_subset(A,labels,size):
    if size==0:return []
    chosen=[]
    for i in labels:
        if row_reduce([A[j] for j in chosen+[i]])[0]>len(chosen):chosen.append(i)
        if len(chosen)==size:return chosen
    require(size==0,'not enough independent tight rows')
    return []


def endpoint(A,b,x):
    require(all(dot(a,x)<=c for a,c in zip(A,b)),'endpoint is infeasible')
    tight=[i for i,(a,c) in enumerate(zip(A,b)) if dot(a,x)==c]
    I=independent_subset(A,tight,len(x))
    return I


def labels(raw,m,size):
    require(type(raw)is list and len(raw)==size and raw==sorted(set(raw)) and
            all(type(i)is int and 0<=i<m for i in raw),'invalid row-index set')
    return raw


def audit_inverse(A,I,raw):
    d=len(A[0]);n=len(I)
    require(type(raw)is list and len(raw)==d and all(type(r)is list and len(r)==n for r in raw),'wrong right inverse dimensions')
    R=[list(map(rat,r)) for r in raw]
    for i,k in enumerate(I):
        for j in range(n):require(sum(A[k][l]*R[l][j] for l in range(d))==int(i==j),'false rational right inverse')
    return R


def verify(data,c):
    """Independent POSITIVE route certificate. No solver or elimination calls."""
    A,b,u,v=parse(data);m,d=len(A),len(u)
    require(c['format']=='original-route-bmc-v1' and c['problem_sha256']==binding(A,b,u,v),'wrong certificate/input binding')
    require(type(c['budget'])is int and c['budget']>=0,'invalid budget')
    V=c['vertices'];E=c['edges']
    require(type(V)is list and V and type(E)is list and len(E)==len(V)-1<=c['budget'],'bad path length')
    points=[];tight=[]
    for p in V:
        x=list(map(rat,p['point'])); require(len(x)==d,'bad point dimension')
        require(all(dot(a,x)<=rhs for a,rhs in zip(A,b)),'path point infeasible')
        I=labels(p['basis'],m,d)
        require(all(dot(A[i],x)==b[i] for i in I),'selected vertex row not tight')
        audit_inverse(A,I,p['right_inverse']);points.append(x)
        tight.append([i for i in range(m) if dot(A[i],x)==b[i]])
    require(points[0]==u and points[-1]==v,'route endpoints changed')
    for j,e in enumerate(E):
        require(points[j]!=points[j+1],'stationary output step must be removed')
        I=labels(e['shared_rows'],m,d-1)
        require(all(i in tight[j] and i in tight[j+1] for i in I),'edge rows not common and tight')
        audit_inverse(A,I,e['right_inverse'])
    # A full-rank tight vertex basis proves extremality. A common rank d-1
    # face contains two distinct vertices, hence is precisely their edge.
    return {'status':'PASS','original_edges':len(E),'original_input_rows':m,'ambient_dimension':d,
       'vertex_active_row_counts':[len(J) for J in tight],
       'overdetermined_vertex_visits':sum(len(J)>d for J in tight),
       'solver_required_for_verification':False,
       'scope':'Exact original-row feasibility and rank identities certify every original edge; not a Lean theorem or independent UNSAT proof.'}


def certificate(data,points,vertex_sets,edge_sets,budget):
    A,b,u,v=parse(data);d=len(u);V=[];E=[]
    for j,(x,I) in enumerate(zip(points,vertex_sets)):
        if V and list(x)==list(map(rat,V[-1]['point'])):continue
        if V:
            J=sorted(edge_sets[j-1]);E.append({'shared_rows':J,'right_inverse':serial(right_inverse([A[i] for i in J],d))})
        I=sorted(I);V.append({'point':serial(x),'basis':I,'right_inverse':serial(right_inverse([A[i] for i in I],d))})
    c={'format':'original-route-bmc-v1','problem_sha256':binding(A,b,u,v),'budget':budget,'vertices':V,'edges':E}
    verify(data,c);return c


def smt_num(q):
    q=rat(q);a=str(abs(q.numerator))
    if q.denominator!=1:a=f'(/ {a} {q.denominator})'
    return f'(- {a})' if q<0 else a


def sexprs(text):
    """Small strict parser for constant models. Never evals solver output."""
    tokens=re.findall(r'\(|\)|[^\s()]+',text);pos=0
    def one():
        nonlocal pos
        require(pos<len(tokens),'truncated S-expression');t=tokens[pos];pos+=1
        if t=='(':
            a=[]
            while pos<len(tokens) and tokens[pos]!=')':a.append(one())
            require(pos<len(tokens),'unclosed S-expression');pos+=1;return a
        require(t!=')','unexpected close');return t
    out=[]
    while pos<len(tokens):out.append(one())
    return out


def model_value(x):
    if x=='true':return True
    if x=='false':return False
    if isinstance(x,str):return Q(x)
    require(isinstance(x,list) and x,'bad model scalar')
    if x[0]=='-' and len(x)==2:return -model_value(x[1])
    if x[0]=='/' and len(x)==3:return model_value(x[1])/model_value(x[2])
    raise ValueError('unexpected nonrational model expression')


class Z3Backend:
    """Minimal C-API adapter; model search is deliberately NOT trusted by verify."""
    def __init__(self):
        name=os.environ.get('HIRSCH_Z3_LIBRARY') or ctypes.util.find_library('z3')
        if not name:
            try:
                import z3
                name=str(Path(z3.__file__).parent/'lib'/'libz3.so')
            except ImportError:pass
        require(name is not None,'Z3 shared library not found; install z3-solver or set HIRSCH_Z3_LIBRARY')
        self.lib=C.CDLL(name);lib=self.lib
        specs={'Z3_mk_config':([],C.c_void_p),'Z3_set_param_value':([C.c_void_p,C.c_char_p,C.c_char_p],None),
          'Z3_del_config':([C.c_void_p],None),'Z3_mk_context':([C.c_void_p],C.c_void_p),
          'Z3_del_context':([C.c_void_p],None),'Z3_set_ast_print_mode':([C.c_void_p,C.c_uint],None),'Z3_mk_solver':([C.c_void_p],C.c_void_p),
          'Z3_solver_inc_ref':([C.c_void_p,C.c_void_p],None),
          'Z3_solver_from_string':([C.c_void_p,C.c_void_p,C.c_char_p],None),
          'Z3_solver_check':([C.c_void_p,C.c_void_p],C.c_int),
          'Z3_solver_get_model':([C.c_void_p,C.c_void_p],C.c_void_p),
          'Z3_model_to_string':([C.c_void_p,C.c_void_p],C.c_char_p),
          'Z3_solver_get_reason_unknown':([C.c_void_p,C.c_void_p],C.c_char_p),
          'Z3_get_error_code':([C.c_void_p],C.c_uint),
          'Z3_get_error_msg':([C.c_void_p,C.c_uint],C.c_char_p),
          'Z3_get_full_version':([],C.c_char_p)}
        for f,(args,res) in specs.items():
            fun=getattr(lib,f);fun.argtypes=args;fun.restype=res
        self.version=lib.Z3_get_full_version().decode()
        self.handler_type=C.CFUNCTYPE(None,C.c_void_p,C.c_uint)
        lib.Z3_set_error_handler.argtypes=[C.c_void_p,self.handler_type]
        self.handler=self.handler_type(lambda ctx,code:None)
    def solve(self,script,timeout_ms):
        require(type(timeout_ms)is int and timeout_ms>0,'invalid solver timeout')
        L=self.lib;cfg=L.Z3_mk_config();L.Z3_set_param_value(cfg,b'model',b'true')
        L.Z3_set_param_value(cfg,b'timeout',str(timeout_ms).encode())
        ctx=L.Z3_mk_context(cfg);L.Z3_del_config(cfg);L.Z3_set_error_handler(ctx,self.handler)
        try:
            L.Z3_set_ast_print_mode(ctx,2)
            solver=L.Z3_mk_solver(ctx);L.Z3_solver_inc_ref(ctx,solver)
            L.Z3_solver_from_string(ctx,solver,script.encode())
            err=L.Z3_get_error_code(ctx)
            require(not err, L.Z3_get_error_msg(ctx,err).decode() if err else '')
            result=L.Z3_solver_check(ctx,solver)
            if result==-1:return {'status':'unsat','model':None}
            if result==0:return {'status':'unknown','reason':L.Z3_solver_get_reason_unknown(ctx,solver).decode()}
            text=L.Z3_model_to_string(ctx,L.Z3_solver_get_model(ctx,solver)).decode()
            # C API prints a sequence of (define-fun ...) declarations.
            forms=sexprs(text)
            if len(forms)==1 and forms[0] and forms[0][0]=='model':forms=forms[0][1:]
            vals={}
            for f in forms:
                require(isinstance(f,list) and len(f)==5 and f[0]=='define-fun' and f[2]==[],'unexpected model declaration')
                vals[f[1]]=model_value(f[4])
            return {'status':'sat','model':vals}
        finally:L.Z3_del_context(ctx)


def audit_dependency(A,c):
    I=labels(c['rows'],len(A),len(c['rows']));w=list(map(rat,c['coefficients']))
    require(I and len(w)==len(I) and any(w),'empty row dependency')
    require(all(sum(t*A[i][j] for i,t in zip(I,w))==0 for j in range(len(A[0]))),'false row dependence')
    return I


def dependency(A,I):
    r,cols,w,_=row_reduce([A[i] for i in I]);require(w is not None,'not dependent')
    pairs=[(i,a) for i,a in zip(I,w) if a]
    out={'rows':[i for i,a in pairs],'coefficients':serial([a for i,a in pairs])}
    audit_dependency(A,out);return out


def encoding(A,b,u,v,budget,cuts=()):
    m,d=len(A),len(u);lines=['; Original-H bounded route; rank exclusions separately audited.']
    for t in range(budget+1):
        for j in range(d):lines.append(f'(declare-const x_{t}_{j} Real)')
        for i in range(m):lines.append(f'(declare-const v_{t}_{i} Bool)')
    for t in range(budget):
        for i in range(m):lines.append(f'(declare-const e_{t}_{i} Bool)')
    def add(x):lines.append('(assert '+x+')')
    def linear(t,a):
        z=[f'(* {smt_num(c)} x_{t}_{j})' for j,c in enumerate(a) if c]
        return '0' if not z else z[0] if len(z)==1 else '(+ '+' '.join(z)+')'
    def cardinal(names,n):
        # Z3's supported pseudo-Boolean syntax avoids huge subset enumeration.
        if not names:return 'true' if n==0 else 'false'
        return f'((_ pbeq {n} '+ ' '.join('1' for _ in names)+') '+' '.join(names)+')'
    for t in range(budget+1):
        add(cardinal([f'v_{t}_{i}' for i in range(m)],d))
        for i,(a,rhs) in enumerate(zip(A,b)):
            ax=linear(t,a);bv=smt_num(rhs)
            add(f'(<= {ax} {bv})');add(f'(=> v_{t}_{i} (= {ax} {bv}))')
    for t in range(budget):
        add(cardinal([f'e_{t}_{i}' for i in range(m)],d-1))
        for i,(a,rhs) in enumerate(zip(A,b)):
            add(f'(=> e_{t}_{i} (and (= {linear(t,a)} {smt_num(rhs)}) (= {linear(t+1,a)} {smt_num(rhs)})))')
    for j in range(d):
        add(f'(= x_0_{j} {smt_num(u[j])})');add(f'(= x_{budget}_{j} {smt_num(v[j])})')
    for t,x in [(0,u),(budget,v)]:
        for i in endpoint(A,b,x):add(f'v_{t}_{i}')
    for cut in cuts:
        I=audit_dependency(A,cut)
        for prefix,count,size in [('v',budget+1,d),('e',budget,d-1)]:
            if len(I)>size:continue
            for t in range(count):add('(not (and '+' '.join(f'{prefix}_{t}_{i}' for i in I)+'))')
    return '\n'.join(lines)+'\n'



def inverse_encoding(A,b,u,v,budget):
    """Polynomial-size EXACT formulation, with no rank oracle or lazy cuts.

    Row labels have ordered finite integer domains. Guarding a linear
    right-inverse identity by a chosen label does not multiply variables:
    every coefficient of A is fixed input data. All arithmetic is linear.
    """
    m,d=len(A),len(u);lines=['; Exact original-edge route: selector-guarded right inverses.']
    def add(x):lines.append('(assert '+x+')')
    def linear(a,names):
        terms=[f'(* {smt_num(c)} {z})' for c,z in zip(a,names) if c]
        return '0' if not terms else terms[0] if len(terms)==1 else '(+ '+' '.join(terms)+')'
    def point(t,a):return linear(a,[f'x_{t}_{j}' for j in range(d)])
    for t in range(budget+1):
        for j in range(d):lines.append(f'(declare-const x_{t}_{j} Real)')
    for prefix,count,size in [('v',budget+1,d),('e',budget,d-1)]:
        for t in range(count):
            for slot in range(size):
                name=f'{prefix}_{t}_{slot}'
                lines.append(f'(declare-const {name} Int)');add(f'(and (<= 0 {name}) (< {name} {m}))')
                if slot:add(f'(< {prefix}_{t}_{slot-1} {name})')
            for j in range(d):
                for col in range(size):lines.append(f'(declare-const R_{prefix}_{t}_{j}_{col} Real)')
            for slot in range(size):
                for i,a in enumerate(A):
                    conditions=[f'(= {point(t,a)} {smt_num(b[i])})']
                    if prefix=='e':conditions.append(f'(= {point(t+1,a)} {smt_num(b[i])})')
                    for col in range(size):
                        lhs=linear(a,[f'R_{prefix}_{t}_{j}_{col}' for j in range(d)])
                        conditions.append(f'(= {lhs} {int(slot==col)})')
                    add(f'(=> (= {prefix}_{t}_{slot} {i}) (and '+ ' '.join(conditions)+'))')
    for t in range(budget+1):
        for a,rhs in zip(A,b):add(f'(<= {point(t,a)} {smt_num(rhs)})')
    for j in range(d):
        add(f'(= x_0_{j} {smt_num(u[j])})');add(f'(= x_{budget}_{j} {smt_num(v[j])})')
    # Endpoint bases are independent and known, so fix them to remove symmetry.
    for t,x in [(0,u),(budget,v)]:
        for slot,i in enumerate(endpoint(A,b,x)):add(f'(= v_{t}_{slot} {i})')
    return '\n'.join(lines)+'\n'


def solve_inverse(data,budget,timeout_ms=10000,backend=None,encoding_cap=500000):
    A,b,u,v=parse(data);m,d=len(A),len(u)
    require(type(budget)is int and 0<=budget<=200,'budget outside explicit 0..200 cap')
    endpoint(A,b,u);endpoint(A,b,v)
    require(type(encoding_cap)is int and encoding_cap>0,'invalid encoding size cap')
    # Scalar equalities inside all guarded identities, before expanding dot sums.
    size=m*((budget+1)*d*(d+1)+budget*(d-1)*(d+1))
    if size>encoding_cap:
        return {'status':'UNKNOWN','method':'guarded_right_inverse','budget':budget,
          'reason':'guarded equality encoding cap','guarded_scalar_equalities':size,
          'encoding_cap':encoding_cap,'independent_negative_proof':False}
    s=inverse_encoding(A,b,u,v,budget);B=backend or Z3Backend();start=time.monotonic()
    r=B.solve(s,timeout_ms)
    report={'method':'guarded_right_inverse','budget':budget,'solver_version':B.version,
      'encoding_bytes':len(s.encode()),'guarded_scalar_equalities':size,'real_variables':(budget+1)*d+(budget+1)*d*d+budget*d*(d-1),
      'integer_selector_variables':(budget+1)*d+budget*(d-1),
      'smt_sha256':hashlib.sha256((s+'(check-sat)\n').encode()).hexdigest(),'final_smt':s+'(check-sat)\n',
      'solver_seconds':time.monotonic()-start,'no_vertex_graph_supplied':True,
      'independent_negative_proof':False}
    if r['status']!='sat':return {**report,'status':'UNSAT_SOLVER' if r['status']=='unsat' else 'UNKNOWN','reason':r.get('reason')}
    M=r['model'];points=[[rat(M[f'x_{t}_{j}']) for j in range(d)] for t in range(budget+1)]
    V=[];E=[]
    def indices(prefix,t,size):
        values=[rat(M[f'{prefix}_{t}_{j}']) for j in range(size)]
        require(all(v.denominator==1 for v in values),'noninteger row selector')
        return [int(v) for v in values]
    def matrix(prefix,t,size):return [[rat(M.get(f'R_{prefix}_{t}_{j}_{col}',0)) for col in range(size)] for j in range(d)]
    for t,x in enumerate(points):
        if V and x==list(map(rat,V[-1]['point'])):continue
        if V:E.append({'shared_rows':indices('e',t-1,d-1),'right_inverse':serial(matrix('e',t-1,d-1))})
        V.append({'point':serial(x),'basis':indices('v',t,d),'right_inverse':serial(matrix('v',t,d))})
    c={'format':'original-route-bmc-v1','problem_sha256':binding(A,b,u,v),'budget':budget,'vertices':V,'edges':E}
    return {**report,'status':'SAT_CERTIFIED','certificate':c,'verified':verify(data,c)}

def solve(data,budget,timeout_ms=10000,round_cap=100,initial_cuts=(),backend=None):
    A,b,u,v=parse(data);d=len(u);m=len(A)
    require(type(budget)is int and 0<=budget<=200,'budget outside explicit 0..200 cap')
    require(type(round_cap)is int and round_cap>0,'bad refinement cap')
    endpoint(A,b,u);endpoint(A,b,v)
    B=backend or Z3Backend();cuts=[];seen=set()
    for c in initial_cuts:
        I=audit_dependency(A,c)
        if tuple(I) not in seen:cuts.append(c);seen.add(tuple(I))
    history=[];started=time.monotonic()
    for iteration in range(round_cap):
        s=encoding(A,b,u,v,budget,cuts);r=B.solve(s,timeout_ms)
        note={'round':iteration+1,'solver_status':r['status'],'rank_cuts_before':len(cuts),'encoding_bytes':len(s.encode())};history.append(note)
        common={'method':'lazy_rank_exclusions','solver_version':B.version,'budget':budget,'rounds':history,'row_dependence_cuts':cuts,
                'smt_sha256':hashlib.sha256((s+'(check-sat)\n').encode()).hexdigest(),'final_smt':s+'(check-sat)\n',
                'solve_and_refinement_seconds':time.monotonic()-started,'no_vertex_graph_supplied':True}
        if r['status']!='sat':
            return {**common,'status':'UNSAT_SOLVER' if r['status']=='unsat' else 'UNKNOWN',
                'reason':r.get('reason'),'independent_negative_proof':False}
        M=r['model']
        points=[[rat(M[f'x_{t}_{j}']) for j in range(d)] for t in range(budget+1)]
        # Missing Booleans may be don't-cares only if cardinality is trivial;
        # our model includes all selectors through constraints, default false.
        V=[[i for i in range(m) if M.get(f'v_{t}_{i}',False) is True] for t in range(budget+1)]
        E=[[i for i in range(m) if M.get(f'e_{t}_{i}',False) is True] for t in range(budget)]
        require(all(len(I)==d for I in V) and all(len(I)==d-1 for I in E),'model omitted constrained selectors')
        bad=[]
        for I,size in [(I,d) for I in V]+[(I,d-1) for I in E]:
            if row_reduce([A[i] for i in I])[0]<size:
                c=dependency(A,I);key=tuple(c['rows'])
                require(key not in seen,'solver violated a rank exclusion')
                if key not in {tuple(x['rows']) for x in bad}:bad.append(c)
        note['new_rank_exclusions']=len(bad)
        if not bad:
            c=certificate(data,points,V,E,budget)
            return {**common,'status':'SAT_CERTIFIED','certificate':c,'verified':verify(data,c)}
        for c in bad:seen.add(tuple(c['rows']));cuts.append(c)
    return {'status':'UNKNOWN','reason':'rank refinement round cap','budget':budget,'solver_version':B.version,
            'rounds':history,'row_dependence_cuts':cuts,'solve_and_refinement_seconds':time.monotonic()-started,
            'independent_negative_proof':False}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('input',type=Path)
    p.add_argument('--budget',type=int);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--verify',type=Path);p.add_argument('--timeout-ms',type=int,default=10000)
    p.add_argument('--encoding-cap',type=int,default=500000);p.add_argument('--round-cap',type=int,default=100);p.add_argument('--method',choices=['inverse','lazy'],default='inverse');args=p.parse_args()
    try:
        data=json.loads(args.input.read_text())
        out=verify(data,json.loads(args.verify.read_text())) if args.verify else (solve_inverse(data,args.budget,args.timeout_ms,encoding_cap=args.encoding_cap) if args.method=='inverse' else solve(data,args.budget,args.timeout_ms,args.round_cap))
        args.output.write_text(json.dumps(serial(out),indent=2,sort_keys=True)+'\n')
    except (ValueError,KeyError,TypeError,OSError,ZeroDivisionError) as e:p.exit(2,f'No certified route: {e}\n')
if __name__=='__main__':main()
