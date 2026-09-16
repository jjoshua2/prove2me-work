# Exact fixed-budget search for original polyhedron edges

## Status and purpose

This is a written equivalence proof and executed research software, not a Lean
compilation or a Prove2Me acceptance. It establishes no uniform polynomial bound
on the diameter of arbitrary polytopes. SAT methods in polyhedral diameter
research and bounded-model checking are not new; historical novelty is not
claimed for the general idea or for the basic rank characterization of faces.

After #267, a universally polynomial-size complete forward stellar flagification
is not an available sufficient premise. The present tool instead asks directly:

    Do these two ORIGINAL vertices have a route of at most L ORIGINAL edges?

The producer receives only rational A,b,u,v and the proposed budget L. It receives
no vertex graph, facet complex, minimal-nonface catalogue, monotone objective,
refinement, product chart, or suggested path. It can revisit facets and use
nonsimple vertices. Redundant inequalities and lower-dimensional presentations
are allowed. The positive certificate theorem even permits unbounded polyhedra:
its steps are finite one-dimensional faces between actual vertices, never rays.
This larger scope is useful for controls; it does not make an unbounded Hirsch
counterexample into a bounded-polytope counterexample.

There are two implemented encodings. The default is an exact polynomial-size
linear-arithmetic formula with selector-guarded right inverses. A smaller optional
relaxation learns exact rank exclusions lazily. Both output the same solver-free
positive certificate. The quantitative route bound L is an INPUT, not proved
universally sufficient. A solver timeout is retained even on inputs where a
short path is already known.

## 1. Geometric lemma: shared tight rows must be independent

Let P={x in R^d:Ax<=b}, with a finite rational H-description. At a feasible point
x, if d tight row normals are independent, then x is a vertex. Indeed, any
convex decomposition x=lambda*y+(1-lambda)*z with y,z feasible forces those
rows tight at both points; their full rank then gives y=z=x. Conversely, the
active rows at a vertex span R^d: a nonzero vector in their common kernel would
permit sufficiently small feasible perturbations in both directions, contrary
to extremality. This proof includes lower-dimensional P because its affine-hull
equalities appear among the active H rows.

For two DISTINCT vertices x,y, suppose d-1 independent rows are tight at both.
Their equality slice inside P is a face containing both vertices and lying in
a line. It has dimension exactly one. Its two distinct extreme points force
it to be the segment [x,y]; an unbounded ray or line cannot have two distinct
extreme points. Hence x,y are joined by an actual ordinary edge of P.

Conversely, the common active row normals of an edge have rank d-1. A relative-
interior point of the edge has precisely those common equalities, and its minimal
face has dimension d minus their rank. Choose any independent d-1 subset.
No assumption of simplicity or an exact count of active rows is used.

Thus every vertex/edge can be certified by selected tight rows together with
RATIONAL RIGHT INVERSES:

    A_I R = I_d              for a vertex, |I|=d;
    A_J S = I_(d-1)          for an edge, |J|=d-1.                 (1)

Here R is d by d, and S is d by d-1. The consumer checks these matrix identities
directly, using fractions only, rather than trusting a determinant, a solver's
rank assertion, or a supplied adjacency list. In dimension one the edge matrix
has zero columns, as it should. Irredundancy is not needed: duplicate rows may
be present, but cannot masquerade as additional rank.

## 2. Exact polynomial-size bounded-route formulation

For t=0,...,L introduce a real point x_t and select an ORDERED set of d distinct
original row labels I_t. Require feasibility and tightness of I_t at x_t, and
introduce R_t with the first identity in (1). Set x_0=u and x_L=v.
For each t<L select d-1 distinct labels J_t, require them tight at BOTH x_t and
x_(t+1), and introduce S_t with the second identity in (1).

Stationary steps are allowed. They pad a route shorter than L, and are removed
from the emitted certificate. Removing a stationary block does not skip an
unverified edge: the last transition out of that repeated point supplies the
common-row certificate for the next different point.

### Rank can be expressed without nonlinear arithmetic

A selected row label is a finite-domain integer. For vertex slot s and each
possible original index i, emit implications such as

    I_t[s]=i  ==>  a_i.x_t=b_i,
    I_t[s]=i  ==>  sum_j A[i,j]*R_t[j,c] = delta_(s,c).           (2)

The entries A[i,j] are fixed INPUT coefficients, not variables. Therefore (2)
is linear arithmetic with finite guarded choices, not products of two unknowns.
The same construction handles edge right inverses. Ordered selectors remove
permutations of the same basis. Fixing endpoint selectors to one independently
found endpoint basis is sound: those same endpoints admit that basis in every
possible route.

The exact encoding has

    (L+1)d+(L+1)d^2+Ld(d-1) real variables,
    (L+1)d+L(d-1) finite integer selectors,
    m(d+1)[(L+1)d+L(d-1)] scalar equalities inside guards.         (3)

Thus the number of scalar constraints is O((L+1)md^2); writing dense dot products
out gives O((L+1)md^3) coefficient occurrences, with polynomial input-bit overhead.
The size is polynomial in the EXPLICIT budget L, not in log L for a binary-encoded
astronomical budget. The implementation imposes a separate guarded-equality cap
before building an oversized string, returning UNKNOWN when it is exceeded.

### Soundness and completeness for the specified budget

By Section 1, every model produces a walk of at most L genuine original edges
after removing stationary steps. Conversely, a real edge walk supplies full-rank
vertex and common-edge row sets; rational right inverses exist by elimination
on the fixed rational matrices. Rational-polyhedron vertices have rational
coordinates. Add stationary copies of the final vertex to reach L layers.
This satisfies all constraints. For L=0, feasibility means exactly u=v with
that point a vertex.

Consequently the formula is satisfiable IFF the given endpoints have such a
route. This is a mathematical statement about the exact encoding, not a blanket
claim that the backend always returns an answer under a resource limit. It also
does not establish that some polynomial expression in m,d is always a sufficient
budget, which is the conjecture-level missing step.

## 3. Optional lazy rank learning

The smaller encoding initially selects d tight rows at a vertex and d-1 common
tight rows on a step, without their inverse variables. It is only an OVER-
APPROXIMATION. For each model, exact rational row reduction tests the selected
sets. A dependent selection gives a nonzero rational relation sum c_i a_i=0.
The consumer checks that relation independently against the original rows.
Its support is forbidden from being wholly included in any future vertex or
edge basis, at EVERY path layer where it could fit.

Each exclusion is valid for every real path, and each eliminated support can
be learned only once. Therefore uncapped iteration terminates: only finitely
many subsets of at most d original rows exist. That upper bound can be
exponential. One can enumerate all such dependent sets to recover an exact
encoding, but this implementation does not do so in advance. An UNSAT answer
to any valid relaxation excludes a path mathematically if the answer is trusted;
a SAT answer is not accepted until every selected rank passes. Round-cap and
backend-unknown outcomes remain UNKNOWN, never UNSAT.

The guarded-right-inverse mode does not need these learned cuts at all. Both
modes have been run on identical test instances and independently audited.

## 4. A genuine nonsimple trap: eight rows but rank seven

Use the 4 by 4 Birkhoff polytope in (4-1)^2=9 coordinates, eliminating its final
row/column. The original sixteen inequalities are nonnegativity for all matrix
entries. Consider the identity permutation and the permutation (12)(34).

The endpoints have EIGHT common tight inequalities, which equals d-1. Nevertheless,
those eight normals have rank SEVEN. Their common face is two-dimensional:
the segment joining the endpoints is a diagonal, not an edge. This is not an
artifact of duplicate inequalities; these are genuine facets of a nonsimple
polytope. The initial rank-free one-step formula actually returns SAT on this
input. Accepting it would assert a false ordinary edge.

The exact inverse formula returns UNSAT at budget one. The lazy method learns
one exact original-row dependency and then also returns UNSAT. At budget two,
both return positively audited two-edge routes. An independent rank graph on
all 24 permutation vertices confirms shortest distance two. Birkhoff's complete
vertex characterization is classical; the reference does not assert completeness
from sampling random doubly stochastic matrices.

A 5 by 5 version in dimension16 with25 inequalities also gets a certified
two-edge route. Its endpoints' common rank is14<15, independently proving no
one-edge route. No complete reference graph is built for that larger test.

## 5. A classical forced facet-reentry route is allowed, not filtered out

Borgwardt--Stephen--Yusun's arXiv1611.08039v2, printed page17, gives the original
Klee--Walkup unbounded 4-polyhedron. In our <= convention its rows are

    [ 6, 3, 0,-1] x <= 1
    [ 3, 6,-1, 0] x <= 1
    [35,45,-6,-3] x <= 8
    [45,35,-3,-6] x <= 8
    x_i >= 0, i=1,...,4.

The source is u=(0,0,0,0), active on the last four rows; the target is
v=(1,1,8,8), active on the first four. The model is explicitly UNBOUNDED:
(0,0,1,0) is a nonzero recession direction. The primary PDF matrix and inequality
sign were checked from its page image; we do not infer them from garbled text.

Independent enumeration of all70 four-row bases gives15 finite vertices and24
finite edges. Independent BFS gives distance FIVE. Both formula variants report
UNSAT at four and produce exact five-edge certificates. Each constructed route
re-enters one of the eight original facets. In fact every five-edge path must
reenter: for a simple path L=distinct_encountered-4+reentries, so at most eight
available facets cannot cover five steps without a reentry. This is a known
unbounded non-Hirsch example, NOT a new counterexample to bounded or polynomial
Hirsch. It tests that the new solver has not quietly inserted nonrevisiting.

Adding sum x_i<=19 is a SEPARATE bounded nine-facet test, not an implicit change
to the first input. All old finite vertices have coordinate sum<=18; the new
inequality bounds the nonnegative polyhedron. The reference enumerates all126
four-row bases and finds27 vertices/54 edges with the same endpoint distance5.
Every original row in both presentations gets an explicitly checked relative-
interior facet anchor. The positive and negative solver outcomes agree with
independent BFS in both modes. This bounded test meets m-d=5 and makes no new
classical diameter claim.

## 6. Executed comparisons, resource limits, and trust boundaries

Seven independent small reference graphs contain65 vertices/133 edges. Six are
obtained from all358 square row selections in total; the 4D crosspolytope uses
its explicit coordinate vertices and independently ranked common-row adjacency.
The Birkhoff3 reference is also independently enumerated from original bases,
not only from its known permutations. Across44 selected endpoint pairs, EACH
mode finds all44 shortest routes (68 edges total) and reports UNSAT on the44
one-shorter budgets. These negative solver outcomes are not independently
verified proof objects; shortestness is independently checked by the test graph.
A repeated pyramid pair is a deliberate degeneracy control, not a new geometric
instance. Redundant-row counts are called overdetermined vertices, not evidence
that every such geometric vertex is nonsimple.

The additional genuine Birkhoff4 rank trap and both Klee--Walkup models are
separately counted. Four dense-affine/positive-row-rescaling runs on a pyramid
retain shortest distance two, without claiming identical solver tie-breaking
or label paths. Stationary routes, a one-dimensional interval and an embedded
segment in a two-dimensional H-presentation each pass in both modes.

Larger cubes d5/8 use exact inverse mode; d12/16 use lazy mode. They yield5/8/12/16
edges without a supplied or enumerated full graph. The explicit source-facet
lower bound proves these selected routes shortest. Cube16 has65536 vertices by
its defining product formula, not by graph enumeration. The dimension16 Birkhoff5
inverse encoding has1,924,728 bytes and yields the two-edge positive certificate.

Hard inputs remain. For the #267 cyclic family at (d,m)=(6,13),(8,17),(16,33),
the selected endpoint pairs have known direct routes of length d. The unrestricted
lazy solver completes d6 but times out at the stated two-second per-round budget
on d8 and d16 in both recorded runs. These are UNKNOWN, not evidence that the
routes do not exist or are long. No dimension64 direct SMT run is claimed.

There are110 saved positive routes and94 saved negative solver queries, plus
TWO actual timeout queries. All110 positive certificates replay after disabling
the solver, rank elimination, inverse production and both search modes. Eleven
forged/out-of-domain controls fail. Four explicit resource-bound controls preserve
UNKNOWN: two mocked solver outcomes, an encoding cap and a rank-round cap.
No actual timeout is mislabeled a certificate of absence.

The installed backend is Z3 4.13.3.0, called via its documented C API through
ctypes, with no downloaded compiler or Python z3 package. Test-only independent
rank work uses the recorded SymPy version. The positive consumer uses only the
Python standard library and rational arithmetic; no Z3 library is required to
verify an existing certificate. The backend path is configurable with
HIRSCH_Z3_LIBRARY. The code does not access the network or any credentials.
The mathematical formula is solver-independent. The exported SMT-LIB string
includes its check-sat command and an exact content hash.

A SAT answer without an accepted rational certificate is never reported as a
proved route. An UNSAT result currently has NO separately verified proof trace;
changing that would need another checker, not a different label on the output.
Exact Python checks, compiler verification and Prove2Me status remain distinct.
Neither script nor its JSON parser is Lean-extracted or formally verified.

## 7. Reproduction and the remaining proof target

    python3 scripts/test_original_route_bmc.py
    python3 scripts/original_route_bmc.py input.json --budget 8 --output result.json
    python3 scripts/original_route_bmc.py input.json --budget 8 --method lazy --output result.json
    python3 scripts/original_route_bmc.py input.json --verify certificate.json --output checked.json

For --verify, supply the nested `certificate` object, not the entire solver result.
The solver reports, exported formulas and positive certificates regenerate in
fixtures/original_route_bmc_examples.json. Full artifacts are bundled; the
repository keeps exact execution/source/replay records. No native shared library
is included in the bundle. No old project proof, selector or workflow is edited.

The new component is a direct experiment and certificate engine. It removes
restrictions imposed by our earlier specialized route families and does not pay
the cost of resolving every minimal nonface. Its exact bounded equivalence is
not itself a new bound on the smallest sufficient L. A universal polynomial
claim would still require a proof that a polynomial budget always has a model,
or a new geometric construction supplying that budget. Finite solver successes,
known-class shortest routes, and a polynomial FORMULA SIZE do not prove such
existence or a polynomial SAT-solving runtime.

The immediate research use is to test proposed path-local invariants against
unrestricted original routes, especially nonsimple or reentry cases, and export
small rational witnesses for future formalization. Negative solver statements
should be independently checked before becoming mathematical lower bounds.
The old accepted interfaces and other agents' owned tasks remain untouched.

Primary sources and attribution:
- D. Bremner and L. Schewe, Edge-Graph Diameter Bounds for Convex Polytopes with
  Few Facets, Experimental Mathematics20(3),2011,229--237,
  DOI10.1080/10586458.2011.564965; arXiv0809.0915. Their use of satisfiability in
  diameter research precedes this implementation; this is not that oriented-
  matroid classification algorithm.
- S. Borgwardt, T. Stephen, T. Yusun, On the Circuit Diameter Conjecture,
  arXiv1611.08039v2, printed page17, exact Klee--Walkup matrix and five-edge
  distance. Our objects here are ORDINARY edges, not relaxed circuit steps.
- N. Linial and Z. Luria, On the vertices of the d-dimensional Birkhoff polytope,
  arXiv1208.4218, introductory Birkhoff--von Neumann vertex characterization.
- Z3 official API documentation: https://z3prover.github.io/api/html/ .
