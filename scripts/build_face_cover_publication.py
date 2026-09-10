#!/usr/bin/env python3
"""Package already kernel-checked PR61 declarations for public verification.

Read every local proof dependency from one immutable Git commit. No proof is
synthesized, downloaded from an unpinned branch, or assumed from a theorem stub.
Only public Mathlib and Hirsch-model definitions remain as imports.
"""
from __future__ import annotations
import argparse, hashlib, json, re, subprocess
from pathlib import Path

SOURCE = '681314640b6f84792d8ae011c3534a6e8c456930'
SOURCE_RUN = 34532572816
PIN = 'c5ea00351c28e24afc9f0f84379aa41082b1188f'
LEAN = 'leanprover/lean4:v4.30.0'
PREAMBLE = '''import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
set_option maxHeartbeats 12000000
'''

CASES = [
 dict(key='weighted', name='Hirsch.weighted_geodesic_face_cover_diameter_bound',
 root='Solutions.PolynomialWeightedFaceCover',
 checked='HirschFaceSplice.diamLE_of_weighted_face_cover',
 title='Weighted extreme-face covers bound graph diameter',
 signature='''{ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ ∑ i, if x ∈ F i then weight i else 0)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, weight i * (B i + 1)) / q - 1)''',
 proof='exact HirschFaceSplice.diamLE_of_weighted_face_cover d q hq P F B weight hF hFD hcover hconnect',
 natural=r'''Let $P\subseteq\mathbb R^d$ have connected vertex-edge graph, with adjacency defined by extreme line segments. Let $(F_i)$ be a finite family of extreme subsets of $P$, with nonnegative integer weights $w_i$ and integer budgets $B_i$. Assume every vertex receives total covering weight at least $q>0$, and assume intrinsic padded graph diameter at most $B_i$ only for those $F_i$ with positive weight. Then the padded graph diameter of $P$ is at most
$$\left\lfloor\frac{\sum_i w_i(B_i+1)}q\right\rfloor-1.$$
Natural-number subtraction is truncated at zero. Zero-weight sets have no diameter hypothesis or cost. No boundedness, polyhedral presentation, simplicity, or nonemptiness is required beyond the displayed hypotheses. This is a conditional certificate, not a claim that a cheap cover always exists.''',
 explanation=r'''Choose a shortest finite parent walk between the given vertices. If two visits to an extreme subset $F_i$ were more than $B_i$ positions apart, its intrinsic route would replace the intervening subpath and shorten the parent walk. Extremeness ensures the visit points are vertices of $F_i$ and its edges are parent edges. Thus a positively weighted $F_i$ covers at most $B_i+1$ positions, even when the shortest walk leaves and re-enters it. Weighted double-counting gives
$$q(L+1)\le\sum_i w_i(B_i+1).$$
Divide by $q$ and pad with stationary steps. A zero-weight set contributes zero and its diameter is never used.'''),
 dict(key='codimension', name='Hirsch.tight_rows_outside_subspace_cardinality_bound',
 root='Solutions.PolynomialRankSensitiveFaceCover',
 checked='HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim',
 title='Tight rows outside a normal subspace cover its codimension',
 signature='''{d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    d - Module.finrank ℝ U ≤
      (Finset.univ.filter (fun i => a i ∉ U ∧ ⟪a i, x⟫ = b i)).card''',
 proof='exact HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim a b x hx U',
 natural=r'''Let $x$ be an extreme vertex of $P=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i,\ i<n\}$. For every linear subspace $U$ of the row-normal space,
$$\#\{i:a_i\notin U,\ \langle a_i,x\rangle=b_i\}\ge d-\dim U.$$
The count is of describing row indices, not a claim that all counted rows are mutually independent. Redundant and zero rows are allowed; no boundedness, strict feasibility, full-dimensionality, simplicity, or irredundancy assumption is made.''',
 explanation=r'''Evaluate the selected tight rows on $U^\perp$. This linear map is injective: a vector in its kernel annihilates the tight rows outside $U$, and by orthogonality also the tight rows inside $U$. A direction annihilating every tight inequality at a vertex must be zero, since sufficiently small positive and negative displacements would otherwise remain feasible. Dimension comparison therefore bounds $\dim U^\perp=d-\dim U$ by the number of selected coordinates.'''),
 dict(key='rank_selected', name='Hirsch.rank_selected_row_face_diameter_bound',
 root='Solutions.PolynomialRankSensitiveFaceCover',
 checked='HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds',
 title='Rank-selected supporting sections bound an extreme face diameter',
 signature='''{d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hU : Module.finrank ℝ U < d)
    (B : Fin n → ℕ)
    (hFD : ∀ i, a i ∉ U →
      DiamLE (F ∩ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ F, ∀ v ∈ extremePoints ℝ F,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj F (w j) (w (j + 1))) :
    DiamLE F
      ((∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1)) /
        (d - Module.finrank ℝ U) - 1)''',
 proof='exact HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds a b F hF U hU B hFD hconnect',
 natural=r'''Let $F$ be an extreme subset of an $n$-row H-polyhedron in $\mathbb R^d$, with connected vertex-edge graph. Let $U$ be any row-normal subspace of rank $r<d$. For each row with $a_i\notin U$, assume intrinsic padded diameter at most $B_i$ for
$$F_i=F\cap\{x\in P:\langle a_i,x\rangle=b_i\}.$$
Then
$$\operatorname{diam}(F)\le\left\lfloor\frac{\sum_{a_i\notin U}(B_i+1)}{d-r}\right\rfloor-1,$$
with truncated natural subtraction and the padded-walk convention. Rows in $U$ are neither charged nor assumed to have any diameter bound. This theorem does not assert that the selected sections are proper for an arbitrary $U$, or that their supplied budgets are small. Proper descent requires separately choosing a saturated normal space.''',
 explanation=r'''Every vertex of $F$ is a parent vertex. The tight-row codimension argument supplies at least $d-r$ incident supporting rows outside $U$. Their intersections with $F$ are extreme subsets of $F$. Apply weighted shortest-path incidence counting, assigning weight one to rows outside $U$ and weight zero to all others. The total charge is exactly the displayed selected-row sum. Neither unused rows nor a diameter bound on the parent enters the proof.'''),
 dict(key='barrier', name='Hirsch.weighted_cover_improvement_requires_smaller_child',
 root='Solutions.PolynomialFaceCoverBarrier',
 checked='HirschFaceCoverBarrier.improving_certificate_requires_improving_child',
 title='Averaging improvement requires a child better than vertex counting',
 signature='''{V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ) (hq : 0 < q)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsmall : (∑ i, weight i * (B i + 1)) / q - 1 < Fintype.card V - 1) :
    ∃ i, 0 < weight i ∧ B i + 1 < (F i).card''',
 proof='exact HirschFaceCoverBarrier.improving_certificate_requires_improving_child F B weight q hq hcover hsmall',
 natural=r'''Let $V$ be a finite set covered by finite subsets $F_i$ with nonnegative integer weights $w_i$, so every element receives covering weight at least $q>0$. Let $B_i$ be nonnegative integers. If the averaging certificate
$$\left\lfloor\frac{\sum_i w_i(B_i+1)}q\right\rfloor-1$$
is strictly less than $|V|-1$, then some positively weighted subset satisfies $B_i+1<|F_i|$. Division and subtraction are the natural-number operations. This is a finite counting theorem: it bounds what an averaging certificate can achieve, not an actual polytope diameter. No geometric or graph assumption is implicit.''',
 explanation=r'''Argue contrapositively. If every positively weighted $F_i$ satisfies $|F_i|\le B_i+1$, summing the coverage inequality over all elements yields
$$q|V|\le\sum_{v\in V}\sum_{i:v\in F_i}w_i
=\sum_i w_i|F_i|\le\sum_i w_i(B_i+1).$$
Integer division by the positive $q$ and truncated subtraction preserve the resulting lower bound $|V|-1$. Therefore a strict improvement must use a positively weighted child below its own vertex-count allowance.'''),
]

def sha(data: str) -> str:
    return hashlib.sha256(data.encode()).hexdigest()

def read_git(repo: Path, path: str) -> str:
    return subprocess.check_output(['git','-C',str(repo),'show',f'{SOURCE}:{path}'], text=True)

def without_comments(text: str) -> str:
    out=[]; i=0; depth=0
    while i<len(text):
        if text.startswith('/-',i): depth+=1; i+=2
        elif depth and text.startswith('-/',i): depth-=1; i+=2
        elif not depth and text.startswith('--',i):
            j=text.find('\n',i); i=len(text) if j<0 else j
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        else: out.append(text[i]);i+=1
    if depth:raise ValueError('unterminated Lean block comment')
    return ''.join(out)

def check_proof(text: str):
    clean=without_comments(text)
    if re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|^\s*(axiom|opaque|unsafe)\s', clean,re.M):
        raise ValueError('admission or unchecked declaration in proof')
    if re.search(r'^\s*import\s+(Solutions|Theorems)\.',clean,re.M):
        raise ValueError('nonpublic proof import survived flattening')

def flatten(repo: Path, root: str) -> tuple[str,list]:
    seen=set();pending=set();pieces=[];sources=[]
    def visit(module):
        if module in seen:return
        if module in pending:raise ValueError('cyclic source import')
        pending.add(module);path=module.replace('.','/')+'.lean'
        original=read_git(repo,path);body=[]
        for line in original.splitlines():
            if line.startswith('import '):
                for dep in line[7:].split():
                    if dep.startswith('Solutions.'):visit(dep)
                    elif dep.startswith('Mathlib') or dep=='Definitions.Def_Hirsch_model':pass
                    else:raise ValueError('unapproved import: '+dep)
            elif not line.startswith('#print axioms '):body.append(line)
        body='\n'.join(body)+'\n';check_proof(body)
        stack=[]
        for line in without_comments(body).splitlines():
            line=line.strip()
            if line=='noncomputable section' or line=='section':stack.append(None)
            elif re.match(r'^(namespace|section)\s+\S+',line):stack.append(line.split()[1])
            elif re.match(r'^end(?:\s+\S+)?\s*$',line):
                if not stack:raise ValueError('unmatched end in '+path)
                name=stack.pop()
                if len(line.split())==2 and line.split()[1]!=name:raise ValueError('namespace mismatch')
        if any(s is not None for s in stack):raise ValueError('unclosed named scope in '+path)
        pieces.append('-- Source: '+path+'\nsection\n'+body+'end\n'*len(stack)+'end\n')
        sources.append({'path':path,'sha256':sha(original)})
        pending.remove(module);seen.add(module)
    visit(root)
    return '\n'.join(pieces),sources

def build(repo: Path, out: Path):
    if read_git(repo,'lean-toolchain').strip()!=LEAN:raise ValueError('source toolchain differs')
    if PIN not in read_git(repo,'lake-manifest.json'):raise ValueError('source Mathlib differs')
    if (repo/'Definitions/Def_Hirsch_model.lean').read_text()!=read_git(repo,'Definitions/Def_Hirsch_model.lean'):
        raise ValueError('working public model differs from audited source')
    out.mkdir(parents=True,exist_ok=True);entries=[]
    for case in CASES:
        body,sources=flatten(repo,case['root'])
        wrapper='theorem solution '+case['signature']+' := by\n  '+case['proof']+'\n\n#print axioms solution\n'
        solution=PREAMBLE+'\n'+body+'\nopen scoped BigOperators RealInnerProductSpace\nopen Set Hirsch\n\n'+wrapper
        check_proof(solution)
        short=case['name'].split('.')[-1]
        formal='namespace Hirsch\n\ntheorem '+short+' '+case['signature']+' := by sorry\n\nend Hirsch'
        statement=PREAMBLE+'\n'+formal+'\n'
        (out/(case['key']+'.lean')).write_text(solution)
        (out/(case['key']+'.statement.lean')).write_text(statement)
        (out/(case['key']+'.adapter.lean')).write_text('import '+case['root']+'\n'+PREAMBLE+'\n'+wrapper)
        entries.append({**{k:case[k] for k in ['key','name','root','checked','title','natural','explanation']},
          'formal_statement':formal,'preamble':PREAMBLE,'solution_sha256':sha(solution),
          'statement_sha256':sha(statement),'sources':sources,'solution_bytes':len(solution.encode())})
    manifest={'source_commit':SOURCE,'source_run':SOURCE_RUN,'mathlib_rev':PIN,'lean_toolchain':LEAN,
      'public_model_sha256':sha(read_git(repo,'Definitions/Def_Hirsch_model.lean')),
      'entries':entries,'status':'GENERATED_NOT_YET_STANDALONE_CHECKED'}
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'generated':len(entries),'bytes':[e['solution_bytes'] for e in entries]}))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--repo',type=Path,default=Path('.'));p.add_argument('--out',type=Path,default=Path('face_cover_publication_packet'))
    args=p.parse_args();build(args.repo.resolve(),args.out.resolve())
