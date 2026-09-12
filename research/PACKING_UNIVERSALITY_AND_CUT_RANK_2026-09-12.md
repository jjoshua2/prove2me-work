# Near-uniform packing universality and rank-local ordinary-edge routes

## Scope, dependencies, and what changed

This continuation starts from main `321f473d871aad2d692595acd97a667d6a648d06`,
after the verified #204 work. It does not alter the concurrently developed
#205 positive-feedback-box branch. The new code uses no credentials, network
calls, workflow changes, dependency changes, or new platform theorem records.
The pinned Lean environment remains Lean 4.30.0 / Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

There are three mathematical developments, not a proof of Polynomial Hirsch:

* A same-dimension, same-face-lattice packing normalization for every bounded
  polytope with a supplied simple vertex. All upper coefficients can be made
  arbitrarily close to one. Consequently unrestricted monotone cuts, and even
  nearly parallel positive cuts, do not describe an easier universal problem.
* For any number q of nonnegative cuts on a contractive feedback box, the
  actual endpoint anchoring faces have dimension at most the CUT RANK s, not
  merely q. This gives diameter O(d+(q+s)2^s), improved to d+q+4 at rank two.
* A pure packing polytope needs no box certificate: its vertices have support
  at most s. Routing inside the two coordinate support faces gives a bound
  independent of ambient dimension, at most q+2 for rank two.

The three new Lean modules are uncompiled candidates. They prove the
normalization's onto-set/diameter transport and its positivity hypotheses,
active-cut rank localization, and sparse vertex support. The full general
simple-vertex preparation, classical reduction to simple polytopes, and the
complete low-rank anchoring/Larman/polygon composition are proved below, not
claimed as additional completed Lean declarations. Exact JSON route checks
verify individual ordinary edges; they are not Lean proof terms.

## 1. A universal packing normalization

### 1.1 Prepare coordinates at a simple vertex

Let P={z:A_i z<=b_i} be bounded and full-dimensional in R^d. Let v be a
simple vertex with exactly d active rows I, with A_I invertible. All remaining
slacks s_i=b_i-A_i v are strictly positive. Put

    x=b_I-A_I z,       z=v-A_I^{-1}x,
    R_i=-A_i A_I^{-1}/s_i  (i outside I).

This identifies P affinely with

    P0={x>=0 : R_i x<=1, i=1,...,m},       m=n-d.             (1)

All original rows are retained, including any redundant rows slack at v.
The geometric simple-vertex claim assumes a genuine facet description; an
input with extra active duplicate rows must first be separately normalized.
The CLI rejects, rather than silently discards, such rows.

Choose nonnegative row multipliers lambda with

    mu=R^T lambda >0,      sigma=sum(lambda)>0.              (2)

These are a finite certificate of boundedness: mu*x<=sigma and x>=0 give
coordinate upper bounds. They exist for every bounded model (1). For example,
LP duality for maximizing sum(x) yields R^T lambda>=1 with lambda>=0.
This existence is a classical finite-dimensional separation/duality input;
the checker either verifies supplied weights or finds them with a capped exact
dual-basis search. It does not assume a failed capped search proves anything
about geometry. Rational data admit rational weights.

### 1.2 Shift every upper row by the same normal

Fix any eta in (0,1), choose

    K > max_ij |R_ij| / eta,
    y = K*x / (1+K*sum_j x_j),
    H_ij = 1+R_ij/K.                                      (3)

Then P0 is projectively equivalent to

    Q={y>=0 : H_i y<=1},
    1-eta < H_ij < 1+eta.                                  (4)

Here is the complete two-sided argument; positivity at infinity is not omitted.
For x in P0, D=1+K*sum(x)>0. Equation (3) gives

    H_i y = (R_i x+K*sum(x))/D <= 1.

Conversely, for y in Q, y>=0 and the lambda-weighted inequalities imply

    mu*y/K + sigma*sum(y) <= sigma.

Writing mu_min=min_j mu_j>0 gives

    (mu_min/K+sigma)*sum(y) <= sigma,
    1-sum(y) >= mu_min/(K*sigma+mu_min) >0.                 (5)

Thus x=y/[K*(1-sum(y))] is well-defined, nonnegative, and R_i x<=1. It is the
inverse of (3). No spurious feasible component beyond the inverse denominator
has been included. For dimension zero the result is the trivial singleton;
the CLI handles positive dimension only.

Positive projective maps preserve closed/open segments with reweighted
nonnegative/positive coefficients. The established #203 segment-chart theorem
therefore preserves faces, vertices, ordinary edges, and ALL graph distances.
This is not circuit-diameter transport: circuits need not be projectively
invariant. The new Lean theorem `orthant_diamLE_shear_iff` proves the exact
ordinary-edge-budget equivalence for the unscaled intermediate chart; the
final scalar coordinate change is affine.

The image is contained in [0,1)^d by (5). Adding the d cube upper inequalities
y_j<=1 changes neither Q nor any of its vertices or faces. Hence Q is literally
a unit cube clipped by m positive inequalities, although those cube upper
inequalities are redundant. The genuine facet count remains n=d+m when the
input is irredundant, not 2d+m.

### 1.3 Explicit finite denominator multipliers

For the unscaled chart z=x/(1+K*sum(x)), the target rows are lower -e_j and
upper R_i+K*1, with RHS 0 and 1. Pick t>=max_j K/mu_j and D0=1+t*sigma.
Use weights

    alpha_j=(t*mu_j-K)/D0 on lower rows,
    gamma_i=t*lambda_i/D0 on upper rows.

They are nonnegative, their weighted normal is K*1, and their weighted RHS
is t*sigma/D0<1. Thus 1-K*sum(z)>0 follows directly from a finite original-row
inequality certificate. Source denominator positivity is certified by weight K
on each lower row. The implementation independently checks all these identities.

### 1.4 Consequences for the research strategy

The standard perturbation reduction says the maximum ordinary diameter at
fixed dimension and facet count is attained by a simple polytope. Santos states
this explicitly on printed page 3 of [1]. Therefore the following are equivalent
at the mathematical level:

    a uniform polynomial ordinary-diameter bound for all bounded polytopes;
    such a bound for the near-uniform positive packing models (4),
    for any one fixed eta>0.

One direction is restriction; the other is the classical simple reduction
followed by (1)-(5), preserving dimension and genuine facets. Real polytopes
are covered by the real-valued proof. The exact CLI and tests cover rational
instances, not a claim that every real realization is rational. Generic
perturbation can be kept in a rational open chamber when a rational realization
is needed for a worst-case combinatorial type.

This is NOT a newly checked replacement of the live root theorem. The full
perturbation reduction is not included in the Lean modules, and no new open
platform child has been created. It is a precise warning that arbitrary
monotone-cut routing already has universal difficulty, even for the cube base.

A scale-free claim that sufficiently small deviation from rank one, tiny
relative coefficient spread, or almost parallel upper facets forces a short
route would settle the general problem. These properties alone do not erase
any simple-polytope graph. Exact low rank, below, is a different condition.
No claim of a new classical projective-invariance or LP-duality theorem is made.

## 2. Why coordinate deletion is not an ordinary-edge argument

In the packing quadrilateral

    u,v>=0,       2u+v<=3,       u+2v<=3,

the vertex (1,1) has exactly two neighbors: (3/2,0) and (0,3/2). Each increases
one coordinate. Deleting a coordinate to (1,0) is feasible but does not even
land at a vertex. Thus down-monotonicity cannot by itself supply a
coordinatewise-nonincreasing ordinary-edge move.

This distinction is also explicit in the literature: [2, Theorem 2.3] gives
short CIRCUIT walks to the origin in anti-blocking polytopes. It does not give
the ordinary-edge theorem needed here.

We use published Todd data from [2, Section 2.2] as a stronger regression,
not as a claimed new counterexample. Its four upper rows are

    [7,4,1,0], [4,7,0,1], [43,53,2,5], [53,43,5,2],
    RHS=[1,1,8,8], with x>=0.

Independent exact enumeration gives 20 vertices and 40 edges. From
(1,1,8,8)/19 to zero, ordinary distance is 4 but the shortest path decreasing
sum(x) has length 5. After (3) with eta=10^-8, all upper coefficients lie
within eta of one and BOTH values persist. Indeed sum(y)=K*sum(x)/(1+K*sum(x))
is strictly increasing in sum(x), so this particular orientation is preserved.
The exact cut rank remains four. No rounding or approximate rank test is used.

## 3. Rank-local anchoring for arbitrarily many monotone cuts

Let B>=0, b>0, and w>0 with Bw<w. Put

    P={x:0<=x<=b+Bx},
    Q=P intersect {A*x<=beta},
    A>=0, beta>=0, with q rows and s=rank(A).                (6)

Nonemptiness of Q is automatic since 0 is feasible. Conversely any nonempty
monotone clipping of this nonnegative base has beta>=0. Dependence cycles,
dense B, row sums above one, arbitrary q, redundant cuts, zero cuts and zero
bounds are allowed. The weight condition, not unweighted row sums, is used.

The box structure, order-preserving policy vertices, and Schur closure are
the elementary M-matrix argument developed in #205. The new step is to charge
rank of active cuts instead of the number of cut labels.

### 3.1 The actual parent face is low-dimensional

For a Q-vertex x, let Z be its active lower base coordinates, U its active
upper base coordinates, and F its free pairs. Opposite base constraints
cannot both be active. Every selected base-row subsystem is independent,
so the smallest P-face containing x has dimension h=|F|.

Let W be its direction space. Active non-cut rows vanish on W. If a vector
in W also annihilated the active cuts, it would annihilate every active row
of Q, contradicting the vertex perturbation theorem. Therefore

    h=rank(active cut evaluations restricted to W)<=rank(A)=s.   (7)

This works for nonsimple Q-vertices: there may be more active cut labels than
their rank. The new Lean `PolynomialActiveCutRank` proves the generic
injectivity and rank statements independently of the feedback-box hypotheses.
The Python certificate computes the exact active restricted rank at each
actual endpoint and checks equality with its free-face dimension.

### 3.2 A retained original-vertex anchor inside that same face

Set R=(I-B_UU)^-1. With free coordinates y=x_F, write the face as

    x_Z=0,   x_U=R*b_U+R*B_UF*y,   x_F=y.                  (8)

Call this x=ell+E*y. The inverse R and E are nonnegative. Its reduced box is

    b'=b_F+B_FU*R*b_U,
    B'=B_FF+B_FU*R*B_UF.

Then b'>0, B'>=0, and B'*w_F<w_F. Empty U and empty F have their literal
zero-size/singleton meanings. Formula (8) is injective and onto the actual
parent face. Since x_F>=0, ell<=x. Hence A*ell<=A*x<=beta: ell is a retained
original vertex, with upper signature U and every other signature lower.

The cut rows in the face are A'=A*E>=0 and beta'=beta-A*ell>=0. Thus
Q intersect face_P(x) is described by at most 2h+q inequalities in h coordinates.
It is bounded. For h>0 it is full-dimensional: x_F>0, all free base rows are
strict at x, and a small positive scalar multiple of x_F makes every nonzero
cut row strict. A transformed cut with beta'=0 must have A'=0, because it
vanishes on a point all of whose free coordinates are positive. Such zero rows
are tautological, not a missing dimension issue. This also covers Q itself
being lower-dimensional because of zero bounds outside F.

Every edge in this clipped face is an ordinary edge of Q. It is not an edge
of an arbitrary section: the face is cut out by supporting rows already valid
on Q. This distinction is essential.

### 3.3 Bound the two anchor walks and the middle walk

Define

    L(h,q)=0                                      if h=0,
           1                                      if h=1,
           floor((q+4)/2)                         if h=2,
           (q+2h)*2^(h-3)                         if h>=3.  (9)

The dimension-one case is an interval. In dimension two the graph is a cycle
with at most q+4 sides, so its diameter is at most floor((q+4)/2). The remaining
cases use the existing Larman inequality in the true intrinsic h-coordinate
presentation. This bounds a route from x to ell by L(h,q).

For endpoints x,z with anchor signatures U,V, remove U\V, then add V\U.
Policy vertices are coordinatewise order-preserving in their signatures.
Thus the first half lies below the first anchor and the second half below
the second anchor. All q monotone cuts remain satisfied. Each original box
edge is retained wholly in Q, hence is an ordinary Q-edge. This takes exactly
|U symmetric_difference V| steps, at most d.

Consequently the SAME endpoints have an actual ordinary route satisfying

    dist_Q(x,z)<=L(h_x,q)+|U triangle V|+L(h_z,q).           (10)

Since L is nondecreasing in h and h_x,h_z<=s,

    diam(Q)<=d+2L(s,q).                                    (11)

In particular:

    s=0:  diameter<=d;
    s=1:  diameter<=d+2, independently of q;
    s=2:  diameter<=d+2*floor((q+4)/2)<=d+q+4;
    s>=3: diameter<=d+2(q+2s)2^(s-3).

Every fixed cut rank gives a linear bound in d+q, with any number of cuts.
Logarithmic cut rank gives a polynomial bound. This removes exponential
CUT-COUNT dependence in the applicable regime; it does not remove exponential
RANK dependence when rank grows arbitrarily.

## 4. Pure packing polytopes: remove the ambient dimension from the bound

For Q={x>=0:A*x<=beta}, A>=0, beta>=0 and Q bounded, no feedback model is
required. Let S=supp(x) at a vertex. A direction supported on S and in ker(A)
can be moved a small distance both ways: the positive coordinates stay
positive and all upper evaluations stay unchanged. It must be zero. Hence

    |supp(x)|<=rank(A)=s.                                  (12)

`PolynomialPackingSupportRank` gives this finite-perturbation/injectivity
proof in Lean candidate form, including nonsimple vertices. In fact (12)
does not need A>=0. The packing sign conditions supply the origin and the
full-dimensional support-face argument used below.

The coordinate face with coordinates outside S fixed to zero contains both
x and 0, has dimension h=|S|, and uses at most q+h rows. It is genuinely a
face of Q and is bounded. For h>0, x is strictly positive on S, so the same
small-scalar argument handles zero or redundant upper rows and shows the
face is full-dimensional after deleting tautologies.

Define J(h,q) as in (9), but replace q+2h by q+h and the polygon term by
floor((q+2)/2). Then

    dist_Q(x,z)<=J(|supp(x)|,q)+J(|supp(z)|,q),
    diam(Q)<=2J(s,q).                                      (13)

For rank two, this is at most q+2, independent of d. For rank one, boundedness
and nonnegative rows force all effective rows to be positive multiples of
one strictly positive vector. The strongest row defines a simplex (or the origin when its bound is zero);
its diameter is at most one. The implementation verifies the resulting direct
edge between distinct vertices rather than merely relying on this description.
For s>=3, (13) is 2(q+s)2^(s-3).

This is not a contradiction to Section 1: universal near-uniform packing
matrices may have exact rank d despite arbitrarily small deviation from rank
one. Numeric closeness and exact dimension are not interchangeable.

## 5. Linear cut-count dependence cannot be removed even at rank two

For any integer q>=2, consider

    u,v>=0,
    (2k+1)u+v <= q^2+k(k+1),     k=0,...,q-1.              (14)

The vertices are zero and (j,q^2-j^2), j=0,...,q. Consecutive upper constraints
meet at the corresponding consecutive chain points; every upper inequality
has a nonempty edge, and the two axes close the polygon. Thus there are q+2
vertices, its graph is a cycle, and its diameter is floor((q+2)/2).
All cut rows are nonnegative and their rank is exactly two. Large box upper
bounds may be added redundantly, placing it in (6) with B=0. Therefore even
fixed ambient dimension and fixed rank cannot yield a bound independent of q.
This matches the linear dependence of (11)/(13) up to constants.

## 6. Algorithms, certificates, and executed evidence

`packing_normalization.py` uses exact rational Gaussian elimination at the
supplied simple vertex, followed by a checked positive combination or a capped
exact dual-basis search. The verifier never calls discovery, an optimizer,
or vertex enumeration. It checks BOTH inverse identities, all original rows,
positive scales, coefficient ranges, and finite denominator multipliers.
Failure of the dual cap is explicitly unresolved. It rejects unbounded source
models even though a naive positive shear could produce a bounded target with
spurious points beyond infinity.

`rank_local_monotone_routes.py` computes the two Schur faces of the actual
clipped endpoints, enumerates only those low-dimensional faces, constructs
the two anchor walks and middle signature walk, and checks every edge against
all ORIGINAL Q-rows. `packing_support_routes.py` instead uses the two sparse
coordinate faces. Both expose local basis caps, allow degenerate vertices and
zero bounds, and do not claim polynomial running time in growing rank.
At fixed rank their local basis enumeration uses at most (q+2s) choose s
bases; rational bit-complexity and graph construction still need to be charged.
A polynomial diameter theorem is not by itself a strongly polynomial pivot rule.

Executed full regression receipt: `research/PACKING_RANK_CHECK_all.json`.
It includes 25 normalization cases plus a separate published Todd stress case;
13 independently enumerated clipped-box models; eight polygon controls;
296 box-and-cut routes and 101 pure-packing routes. All returned edges are
checked with exact shared active rank, not circuit feasibility. Original-row
feasibility and full vertex rank are checked at every route point.

The 32-dimensional dense-feedback fixture has 30 distinct rank-two cuts.
Only 32 vertices in each of two two-dimensional endpoint faces are enumerated.
The certified route uses 8+30+8=46 edges. Formula (11) guarantees diameter at
most 66; the sharper actual-pair budget is 64. No shortest-path claim is made.

The 64-dimensional pure-packing fixture has 30 rank-two cuts with repeated
positive column types. Only its two 32-vertex support polygons are enumerated.
Its returned route has 16 edges; (13) gives diameter at most 32. The ambient
graph is not enumerated. Its upper matrix is dense and nonnegative; sparsity
of VERTEX SUPPORT, not matrix zeros, is what permits the local routing.

Independent low-dimensional tests compare original and normalized full graphs,
all graph-pair distances, and every facet-incidence label. The Todd regression
also compares the directed sum-objective edges before and after normalization.
Negative controls reject omitted rows, wrong inverse/Schur data, failed
positivity, approximate floats, signed cuts, nonvertices, falsely declared
edges, and capped enumeration. The exact counts/hashes, rather than these
examples alone, are the reproducibility record.

## 7. Formalization handoff and remaining mathematical obligation

Compile the three NEW modules locally, then audit the twelve printed declarations:

    lake build Solutions.PolynomialOrthantPackingNormalization \
      Solutions.PolynomialActiveCutRank Solutions.PolynomialPackingSupportRank

They contain 460 lines and no intentional proof holes. No Lean executable is
available in this session; no local compile, hosted gate, or platform acceptance
is claimed. Use existing hosted verification only after a locally green proof.
No new root dependency, open child, or placeholder axiom is introduced.

For the complete rank-local route theorem, formalization should next connect:

1. #205's actual face/Schur chart to the generic active-cut rank theorem;
2. the retained lower anchor to all monotone cuts using E>=0;
3. Larman (and optionally the exact polygon cycle bound) inside each actual face;
4. face-to-parent ordinary edges and the remove-then-add anchor signature route.

For pure packing, the remaining adapters are even smaller: the coordinate
support-face affine embedding, the q+h intrinsic presentation, and Larman or
polygon routing to zero. The new support rank theorem already supplies the
necessary dimension bound. Do not replace any of these by an assumed route.

For universal Polynomial Hirsch, Section 1 identifies the unresolved statement
as a uniform ordinary-edge escape bound in full-rank positive packing systems.
Small coefficient spread cannot help on its own. Sparse active cut rank works,
but arbitrary supports can grow to d. A successful further theorem must bound
rank-growing escape costs or their total, while allowing coordinate increases
and necessary facet revisits. No bound of this kind is proved here.

## References and attribution

[1] Francisco Santos, *A counterexample to the Hirsch conjecture*,
Annals of Mathematics 176 (2012), 383-412; arXiv:1006.2814v3, printed page 3
for the simple-polytope worst-case reduction.
https://arxiv.org/abs/1006.2814

[2] Alexander E. Black, Steffen Borgwardt, Matthias Brugger,
*On the Circuit Diameter Conjecture for Counterexamples to the Hirsch Conjecture*,
arXiv:2302.03977v4 (2024), Sections 2.2 and 2.3. Used for the exact Todd matrix
and the explicit distinction between circuit walks and ordinary-edge walks.
https://arxiv.org/html/2302.03977

The Larman theorem and positive projective segment transport are reused from
this repository's established explicit-input interfaces, not reproved or
claimed novel. Novelty relative to the literature has not been established;
the contribution here is the proved mathematical combination, exact recognition
and routing certificates, and its precise relevance to the present frontier.
