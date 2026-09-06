# Prove2Me Polynomial Hirsch audit and solver handoff

Date: 2026-09-05. Account: jjosh.

## Verification status

This package is a public-statement/strategy audit, an exact external computation for the posted Q28 example, and an uncompiled Lean draft. It is NOT a Prove2Me submission and NOT a Lean-verified solution of the geometric Q28 theorem. The private submission source, complete authenticated decomposition graph, failed-attempt history, and local model logs were not accessible. Public theorem types/statuses and the original papers were inspected. No credentials are included.

The exact Python/C++ computations ran successfully. The Lean file was not compiled because Lean is not installed in this environment. Treat errors in that file as implementation issues, not as proof of any geometric bridge it explicitly assumes.

## Audit summary

The profile lists three solved results: `Hirsch.spindle_n_ge_two_d`, `Hirsch.balanced_hpoly_transfer`, and `Hirsch.larman_bound`. Its thirteen posted entries comprise nine open statements, three proved statements, and one definition in the inspected snapshot. `Hirsch.larman_high_dimension` is also marked Proved, but does not appear in this user's three-item solved list. Attribution of its proof work or of the complete Larman dependency closure requires reading the accepted submissions; do not infer that attribution from authorship of the statement.

The evidence supports a capable formalization assistant, with some drift toward repeated wrappers around an unchanged hard construction. It does not support declaring the model incapable. It also does not demonstrate a new polynomial upper bound.

- Balancing to 2D describing inequalities is useful structural infrastructure, and its structural theorem is now proved. The balanced polynomial bound is still equivalent to the original conjecture. These are not contradictory observations.
- Splitting Larman into low and high dimensions is a sensible proof organization. Closing the milestone is valuable, even if some of the work is assembly of others' results.
- Santos counterexample -> five-dimensional spindle + strong d-step transfer is a source-aligned mathematical split. It isolates a fixed finite object and a general construction.
- Strong d-step -> one-step construction + induction on n-2d is a meaningful reduction.
- One-step -> selected tight row -> axial coordinates can be useful implementation scaffolding, but several such wrappers do not discharge the perturbation/short-path obstruction. Finish normalization rather than add more wrappers.
- No length-five apex path -> no length-three path between the apex neighbor sets does little by itself. It becomes genuinely helpful once connected to a finite incidence certificate. This package provides such a route.

## Public source index

Profile: https://prove2.me/users/c7399005-c54f-46c6-83fd-0131738d1e3f

| Declaration | Public theorem ID |
|---|---|
| `Hirsch.balanced_hpoly_transfer` | `e7efc9ee-dec1-4a30-bc66-5a19ad645c7f` |
| `Hirsch.balanced_polynomial_bound` | `cdb2b059-17b6-4c73-8740-caca090314d7` |
| `Hirsch.larman_bound` | `68453b6b-bcef-4672-b877-d04e56527e3f` |
| `Hirsch.larman_high_dimension` | `a9fcfcb0-8d5f-4d33-8dda-f2a00d1d24b7` |
| `Hirsch.spindle_n_ge_two_d` | `143c07df-fbd0-4443-a5f2-82b4e703f48b` |
| `Hirsch.strong_dstep_spindle` | `51a39fac-8270-4e34-a7a0-4edf053137e7` |
| `Hirsch.spindle_one_step` | `dae7c11a-f27f-4e77-96cd-8dd1b3ef0d21` |
| `Hirsch.spindle_one_step_from_apex_facet` | `7a6dc674-21f4-4903-af28-f0dcb256049a` |
| `Hirsch.spindle_one_step_axis` | `3e8cb35f-92d6-422d-bd70-a7fece9a39f4` |
| `Hirsch.spindle_normalize` | `74af7713-0235-4065-85e4-33bcfc6a6a77` |
| `Hirsch.five_spindle_length_six` | `8697af1d-650e-4a10-a2c5-de350daaffc8` |
| `Hirsch.q28_polar_no_length_five_walk` | `7d4aff6c-23f3-404f-902b-d1560d0c3a8a` |
| `Hirsch.q28_polar_no_length_three_between_links` | `b922acbd-281e-42e3-867f-0a1403360b5f` |
| Q28 definition (`Definitions.Def_Hirsch_q28`) | `c44f1578-cc0e-4f73-b0c0-c71adf68e576` |

The theorem page URL is `https://prove2.me/theorems/<ID>`.

Primary papers inspected:
- F. Santos, *A counterexample to the Hirsch conjecture*: https://arxiv.org/pdf/1006.2814 — especially Section 2.2, Theorem 2.6 and the controlled perturbation in its proof.
- B. Matschke, F. Santos, C. Weibel, *The width of 5-dimensional prismatoids*: https://arxiv.org/pdf/1202.4701 — especially Corollary 2.9. Its coordinate table was inspected visually and agrees with the posted Q28 definition.

## Priority 1: close `Hirsch.spindle_normalize`

This is a concrete affine-linear construction, not a new diameter estimate. Here is a complete mathematical route.

Put m=(u+v)/2 and w=(u-v)/2. The no-length-d-walk hypothesis implies u != v: otherwise the constant walk is a counterexample. Thus w != 0.

Let ell=d-1. Choose j with w_j != 0. Let Pi be the coordinate permutation swapping j and ell; put z=Pi(w), so z_ell != 0. Write e for the last standard basis vector. Define

    B(y) = y + y_ell (z-e),
    B^{-1}(x) = x - (x_ell/z_ell)(z-e).

These are inverse linear maps: the ell coordinate of B(y) is z_ell*y_ell, and substitution proves both identities. In particular B(e)=z. Set

    T = B^{-1} o Pi,
    F(x) = T(x-m).

Then F is an affine automorphism, F(u)=e, and F(v)=-e. This construction uses no square roots, orthonormal-basis extension, or topological existence argument.

Write S=T^{-1}. Transform each original inequality by

    a'_i = S^* a_i,
    b'_i = b_i - <a_i,m>.

Indeed x=m+S(y), so

    <a_i,x> <= b_i  iff  <a'_i,y> <= b'_i.

Consequently Hpoly(a',b')=F(Hpoly(a,b)), and each individual row's tightness is preserved. Nonemptiness and boundedness follow from the affine image; in finite dimensions the maps are continuous. Extreme points are preserved by affine equivalences. Segments and the IsExtreme predicate transport under the same equivalence, so adjacency is preserved in both directions. Pull back any purported short walk using F^{-1}, pointwise at every natural-number index, to contradict the original no-walk assumption.

This proves all conjuncts in the posted target. Work with a reusable affine-transport lemma internally, rather than re-proving extreme-point/segment transport at every use.

### An additional easy fact worth reusing

The XOR spindle assumption and endpoint feasibility imply

    <a_i,m> < b_i

for every row i: exactly one endpoint is tight and the other is strictly feasible. In particular the midpoint is strictly feasible for the finite system. Therefore the polytope has nonempty ambient interior; non-full-dimensionality is NOT an additional obstacle for these spindle inputs. The file `Q28FiniteCertificate.lean` includes the elementary scalar midpoint inequality.

### Statement/prose mismatch

The public normalization prose says an affine automorphism is produced. The actual displayed conclusion only produces a', b' and their properties; it does not return the automorphism. This is sufficient for its immediate consumer but less reusable than the prose suggests. Do not claim the formal theorem exports a map. Prove the map internally and either correct the prose or later expose a genuinely reusable transport theorem, without creating a duplicate unfinished target.

## Priority 2: finish the concrete Q28 branch using an exact finite certificate

### Results obtained in this session

Using exactly the posted normals:

- All 98,280 five-row subsets of the 28-row description were enumerated with exact integer determinants.
- 34,672 bases are singular, 61,496 have an infeasible unique solution, and 2,112 feasible bases yield 274 distinct rational vertices.
- The graph obtained by exact common-active-row rank tests has 720 edges.
- The two apices have distance 6, and each has 40 neighbors.
- The distance between their neighbor sets is 4.
- Distance layers from the positive apex contain 1, 40, 64, 64, 64, 32, 9 vertices.
- Every non-apex vertex has exactly five active rows; each apex has fourteen.
- The independent sign changes of the first four coordinates reduce the vertices to 20 orbits.

An independent floating-point halfspace-intersection calculation also returned the same 274 vertices (maximum matching error about 1.2e-16). That is only a secondary sanity check; none of the certificate arithmetic relies on it.

### The lower-bound certificate is simpler than reconstructing the whole graph

Assign to each orbit the integer level listed below. It suffices to prove that an edge changes level by at most one. The positive apex has level 0, and the negative apex has level 6. A padded five-step walk would force 6 <= 5.

The two outstanding Q28 statements can use the same certificate. A neighbor of the positive apex has level at most 1. A neighbor of the negative apex has level at least 5. Three intervening steps cannot bridge that gap.

The exact computation found a particularly convenient property:

> Whenever two distinct vertex orbits have level difference greater than one, any signed representatives have at most THREE common active original inequalities.

Actual adjacent vertices must have at least FOUR common active inequalities in dimension five. Thus no full graph-isomorphism theorem or graph-distance implementation is needed for the lower bound. A conservative supergraph is sufficient.

### Geometric bridge A: active rows span at an extreme point

For a finite H-description in R^d, the active normals at an extreme point span R^d. Otherwise choose a nonzero direction h annihilating all active normals. Every other row has positive slack. Finiteness provides a sufficiently small epsilon>0 so that x+epsilon*h and x-epsilon*h are both feasible. Their midpoint is x, contradicting extremality.

Hence every extreme point has a set of d independent active rows. For Q28, it is the unique solution of a nonsingular five-row subsystem. Conversely a feasible unique solution of such a subsystem is extreme, since feasibility and tightness force both points in any nontrivial midpoint representation to satisfy the same nonsingular equalities.

Look inside the already-proved `spindle_n_ge_two_d` proof for this linear-algebra ingredient before implementing it again. This package did not have access to that proof source and does not assume a particular public lemma name exists.

### Geometric bridge B: an edge needs at least four common active rows

Let x!=y be endpoints of an extreme segment, and m=(x+y)/2. A row is tight at m exactly when it is tight at both endpoints. If there were at most three such rows, their common nullspace in R^5 would have dimension at least two. Choose h in that nullspace, not parallel to y-x. By the finite positive slack of all other rows, m+epsilon*h and m-epsilon*h are feasible for sufficiently small epsilon>0.

Extremality of the segment [x,y] forces both perturbed points to lie on it, contradicting the choice of h. Therefore adjacency implies at least four common active rows. One can prove the stronger rank-four characterization, but the cardinality lower bound already suffices here.

Also establish once that endpoints of an extreme nondegenerate segment are extreme points of P. Along a mission padded walk, starting at an extreme point, all visited points are extreme: stationary steps preserve the point, and adjacency supplies extreme endpoints.

### Smaller completeness check: only 2,002 bases

The full 98,280-basis enumeration is unnecessary in Lean. Restrict to the nonnegative chamber x0,x1,x2,x3 >= 0. In that chamber the system is equivalent to these ten inequalities plus the four nonnegativity inequalities (t=x4):

    18*x0 + t <= 1
    30*x2 + t <= 1
    30*x3 + t <= 1
    5*x1 + 25*x3 + t <= 1
    18*x2 + 18*x3 + t <= 1
    18*x2 - t <= 1
    30*x1 - t <= 1
    30*x0 - t <= 1
    25*x0 + 5*x3 - t <= 1
    18*x0 + 18*x1 - t <= 1
    -x0 <= 0; -x1 <= 0; -x2 <= 0; -x3 <= 0.

There are only binomial(14,5)=2,002 bases. Exact enumeration gives 784 singular bases, 1,006 infeasible bases, and 212 feasible bases yielding 60 chamber vertices. Of these 60, exactly 20 have at least five active ORIGINAL rows. The other 40 cannot be extreme points of the original polytope, by bridge A.

Every original extreme point can be reflected into the chamber, because sign changes in the first four coordinates permute the original rows. It remains extreme in the original polytope and hence in the smaller chamber containing it. Thus this is an exhaustive classification of original vertices up to signs, not just a list of sample feasible points.

The independent Python checker exports the complete 2,002-case classification in `q28_chamber_certificate.json`. Each nonsingular case contains its exact rational candidate; infeasible cases identify a violated chamber row. The finite check can use determinants or certified inverses. Choose the implementation best supported by the local Mathlib project. Importantly, singular bases must not be silently omitted in a completeness proof.

### Exact sign-orbit edge checks

Apply one simultaneous sign change to make the first endpoint a nonnegative representative. The second is then one of 16 sign variants of its representative. It suffices to check 20*20*16=6,400 cases. `check_chamber.py` does this with integer arithmetic and verifies:

- signed normals permute the original 28-row list;
- level difference >1 implies at most three common active rows;
- at least four common active rows puts the two orbit IDs in the supplied quotient supergraph (or the same orbit).

Use a proof-producing finite check in Lean, not an untrusted import of the checker result. `decide`-based finite checks or explicit arithmetic certificates are natural options; runtime and resource limits must be tested locally. No claim is made here that the entire geometric verification is merely syntax cleanup.

### Rational representatives and levels

A row `(p0,p1,p2,p3,p4)/q` denotes its exact rational coordinates, with q>0. Only the first four coordinates admit independent sign changes. IDs match the JSON and Lean file.

| ID | Numerator vector | Denominator | Level |
|---:|---|---:|---:|
| 0 | (0,0,0,0,-1) | 1 | 6 |
| 1 | (0,0,0,0,1) | 1 | 0 |
| 2 | (0,3,5,18,-225) | 315 | 6 |
| 3 | (2,3,2,3,0) | 90 | 3 |
| 4 | (2,3,5,8,-75) | 165 | 5 |
| 5 | (3,2,2,3,0) | 90 | 3 |
| 6 | (3,2,5,3,-30) | 120 | 5 |
| 7 | (4,6,10,15,-135) | 315 | 4 |
| 8 | (5,3,2,3,30) | 120 | 1 |
| 9 | (5,8,3,2,75) | 165 | 1 |
| 10 | (5,18,3,0,225) | 315 | 1 |
| 11 | (6,4,9,6,-45) | 225 | 4 |
| 12 | (6,9,15,10,-90) | 360 | 3 |
| 13 | (9,6,4,6,45) | 225 | 2 |
| 14 | (10,15,6,4,135) | 315 | 2 |
| 15 | (15,10,9,6,90) | 360 | 3 |
| 16 | (21,29,50,75,-675) | 1575 | 4 |
| 17 | (44,31,75,50,-450) | 1800 | 4 |
| 18 | (50,75,29,21,675) | 1575 | 2 |
| 19 | (75,50,31,44,450) | 1800 | 2 |

### Lean content actually supplied

`Q28FiniteCertificate.lean` contains proof bodies without `sorry` for:

- the generic potential bound on padded walks;
- the scalar strict-midpoint fact;
- the finite quotient graph's one-step level bound;
- no length-five walk between its designated apices;
- no length-three walk between their neighbor sets;
- a generic transfer of the no-length-five result from an edge-compatible map to the quotient.

This file is UNCOMPILED. More importantly, the map from actual polytope vertices/edges to the quotient is still an explicit missing geometric bridge. Do not submit the finite graph theorem as though it were the original geometric target. Prove bridges A and B, the vertex classification, sign invariance, and the finite arithmetic checks, then wrap the result in the exact mission statement.

## Priority 3: repair the description-level strong-step proof plan

The public chosen-apex-facet statement only assumes that a describing row is tight at an apex. It does not certify that the row defines a facet. Nor does the displayed conclusion relate the output construction to the supplied row index. Thus the formal statement is an existence assertion under an extra hypothesis, not a specification of a construction over that exact facet.

A tight row need not define a facet: the square [0,1]^2 admits the redundant valid inequality x+y<=2, which is tight only at (1,1). This example illustrates the logical gap in tightness alone; it is not a counterexample to the whole long-spindle theorem.

There is a second issue: n>2d counts describing rows, whereas the source's nonsimpliciality argument uses actual facets/vertices. Duplicate rows do not create additional polar vertices. A raw count must not be substituted into that argument without handling redundancy.

### A useful, explicit redundant-row case

If an original row is redundant, remove it without changing P. Form

    P' = P x [0,1].

Its description uses `(n-1)+2 = n+1` inequalities, and its ambient dimension is d+1. Use apices (u,0) and (v,1). All inherited inequalities are tight at exactly one apex; the two interval inequalities each select one of the new apices.

Edges of a product with an interval are either horizontal copies of edges of P or vertical intervals over vertices of P. Any walk from (u,0) to (v,1) needs at least one vertical move. A walk of length d+1 would therefore project, after omitting vertical/stationary moves and padding as needed, to a walk of at most d steps from u to v. That contradicts the input. Thus this case gives the exact posted one-step existential conclusion without a delicate perturbation.

This is a proposed proof route derived here for the description-level formulation, not a claim that this case was already implemented or stated by the source.

### The irredundant case

The midpoint strict-feasibility argument gives full ambient dimension. With an irredundant description, rows can then be identified with actual facets. The disjoint apex incident-facet sets partition all n facets, each set has at least d elements, and n>2d forces at least one to have more than d.

Orient the apices so that the correct opposite apex is nonsimple, and choose a genuine facet as required by the source construction. In the dual picture, the base being raised from a ridge to a facet must be nonsimplicial. An arbitrary preselected apex orientation is not automatically the orientation used in Santos' proof. Since the current existential conclusion does not tie the result to i0, its proof may ignore an unsuitable supplied index and make the required choice itself.

The hard remaining task is a controlled one-point-suspension/perturbation theorem that raises the minimum length. Merely proving boundedness or continuity under perturbation does not exclude newly introduced short paths. The source uses a particular genericity and face-refinement argument. Reproduce that invariant faithfully rather than creating another theorem with the same construction hidden in a new existential.

### Another prose issue

Several descriptions say the output has exactly 2D *facets*, but their formal types only give exactly 2D *describing inequalities*. Do not claim the stronger facet count without irredundancy. The mission deliberately uses inequality descriptions, so the formal claim may still be exactly what its consumers need.

## Stop rules and reporting for the local agent

For the next work cycle:

1. Read accepted proof sources and check current statuses before duplicating anything; the public snapshot may have changed.
2. Finish `spindle_normalize` using the explicit affine map above.
3. Implement the Q28 certificate bridge and close one of the two concrete no-walk leaves. Reuse the same certificate for the other.
4. On the strong-step branch, address redundancy and the source's orientation/perturbation hypotheses before further publication.

Do not publish a new open child merely because it makes a parent proof short. Each proposed decomposition should identify (a) what substantive obligation it removes, (b) a concrete proof/certificate for each new child, and (c) an existing consumer. Keep routine wrappers private until they are implemented. Report unconditional geometric lemmas closed, dependencies actually discharged, and unresolved mathematical bottlenecks separately from the number of accepted sketches.

A controller should permit a meaningful source-aligned decomposition, but stop repeated wrapper chains around an unaltered hard existential. Prefer a smaller graph with a concrete certificate and a few standard geometric bridge lemmas over a large graph of unproved restatements.

Finally, completing the Santos branch establishes the known failure of the LINEAR Hirsch bound. It does not disprove or prove the polynomial Hirsch conjecture. Keep milestone formalization and genuinely new polynomial-diameter progress in separate reporting categories.

## Reproducing the computations

Full exact enumeration and graph calculation (requires C++17 and Python with SymPy):

```sh
g++ -O2 -std=c++17 enumerate_q28.cpp -o enumerate_q28
./enumerate_q28 > vertices_raw.txt
python check_q28.py
```

Smaller independent exact chamber/sign verification (Python standard library only; reads q28_certificate.json):

```sh
python check_chamber.py
```

An optional second C++ chamber enumerator is also supplied:

```sh
g++ -O2 -std=c++17 enumerate_chamber.cpp -o enumerate_chamber
./enumerate_chamber > chamber_vertices_raw.txt
```

Then compile the Lean draft locally against the mission's pinned environment. The geometric bridge remains real formalization work; the externally generated files are certificate data, not trusted axioms.
