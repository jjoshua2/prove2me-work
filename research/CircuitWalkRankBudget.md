# Circuit-walk rank accounting and zero-overhead certificates

Date: September 10, 2026, America/New_York (September 11 UTC).
Repository: `jjoshua2/prove2me-work`.
Baseline: `0a58bba9df1a45be973d40483d442b85da5156ff`.
Lean pin: `leanprover/lean4:v4.30.0`.
Mathlib pin: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Evidence level and scope

This continuation contains a complete ordinary mathematical argument, exact
rational regression evidence, and a Lean **candidate**, not a kernel-verified
new theorem. No new Prove2Me registration, proof submission, or Open child is
created. Publication is left to the user. No literature-priority claim is made.

The foundation is the already integrated checkpoint localization from PR #70
and maximal-step progress from PR #72. The new work treats whole walks rather
than changing the local swap work pursued separately in PR #76. It neither
replaces nor edits that other workstream.

The principal results are an exact endpoint-corrected conservation identity,
a sharp half-budget for rank loss/gain between vertex endpoints, and an actual
no-overhead edge-refinement certificate under a **pointwise** rank-one condition.
The last condition is automatic when the presentation has at most d+1 rows.
This is a restricted refinement result, not a solution of the d>=4 general
edge-refinement leaf.

## 1. Definitions: ranks, not row counts

Let P={x : A x <= b} be a finite n-row presentation in R^d. Assume the
presentation has a reference extreme vertex, so its total row map is injective
and d<=n. Put e=n-d.

For two feasible checkpoints x,y, let X and Y be the sets of nonzero describing
rows tight at x and y, respectively. Define

```
C = X intersection Y
h = d-rank(A_C)       -- common-carrier direction dimension
p = d-rank(A_X)       -- source self-carrier dimension
q = d-rank(A_Y)       -- target self-carrier dimension
loss(x,y) = h-p
gain(x,y) = h-q.
```

These nonnegative integers are rank changes. They need not equal the numbers
of inequalities lost or acquired. For feasible points, p=0 is equivalent to
being an extreme vertex. Inclusion of the self-carrier direction spaces in the
common carrier gives p<=h and q<=h. Consequently, with no subtraction ambiguity,

```
loss(x,y)+p = gain(x,y)+q = h.                    (1)
```

The same algebraic identity holds even without feasibility. The geometric
interpretation as a face dimension is used only for feasible checkpoints.

## 2. Exact local budget and its slack decomposition

For a nonzero row-circuit displacement g=y-x, let Z be the nonzero rows whose
normal annihilates g. Injectivity of the total row map and circuit minimality
give rank(A_Z)=d-1. Set S=X\Y and T=Y\X.

S, T, Z are pairwise disjoint. For example, a row tight at x and neutral on g
would also be tight at y, so it cannot belong to S. Adding the S rows to C
increases rank by loss(x,y), so loss<=|S|. Similarly gain<=|T|. Thus all four
terms below are nonnegative:

```
sigma(x,y) = (|S|-loss) + (|T|-gain)
           + (|Z|-rank(A_Z)) + (n-|S|-|T|-|Z|).
```

Expanding and substituting rank(A_Z)=d-1 proves the exact identity

```
loss(x,y)+gain(x,y)+sigma(x,y) = e+1.             (2)
```

This is the rank-accounting form of the verified localization inequality
`2*h+d <= n+p+q+1`. The residual sigma measures dependent/extra rows and rows
outside the three disjoint classes; it is not a graph-distance term.

For a genuinely maximal feasible step, some destination-tight row has positive
derivative along g. It annihilates every target self-carrier direction but not
g, while g belongs to the common carrier. Hence the target self-carrier is a
strict subspace of the step carrier:

```
q<h,   gain>=1.                                  (3)
```

This strictness is the previously verified maximality result, not an assumption
that the destination is a vertex. Combining (2) and (3) yields loss<=e and
q<=p+e-1.

For padding x=y, set loss=gain=sigma=0 and charge=0. For genuine steps,
charge=1. Padding must NOT be charged another e+1 merely because it occupies an
index in a padded witness.

## 3. Whole-walk conservation and the sharp half-budget

Take any padded maximal row-circuit walk w_0,...,w_L. Let N be its number of
genuine steps, R its total gained rank, D its total lost rank, and Sigma its
summed localization slack. Let p_0 and p_L be its endpoint self-nullities.
Summing (1), all intermediate self-nullities cancel:

```
D+p_0 = R+p_L.                                   (4)
```

Summing (2), while assigning zero charge to padding, gives

```
D+R+Sigma = N*(e+1).                             (5)
```

Eliminating D yields the endpoint-corrected exact identity

```
2*R+p_L+Sigma = N*(e+1)+p_0.                     (6)
```

For vertex endpoints, p_0=p_L=0. Equations (3)--(6) therefore prove

```
D = R,
2*R+Sigma = N*(e+1),
N <= R = D <= floor(N*(e+1)/2).                  (7)
```

No intermediate vertex hypothesis is used. This is stronger than merely adding
the source-bound `loss<=e`: the two endpoint conditions force the loss and gain
budgets to balance and give the factor one-half.

### Sharpness within bounded, irredundant, strictly feasible presentations

For every d>=1, use

```
0 <= x_i <= 3                         (0<=i<d)
x_i-x_(i+1) <= 1                      (0<=i<d-1).
```

There are n=3d-1 rows and e=2d-1. The all-zero and all-three points are vertices.
The all-ones direction is a row circuit: the d-1 independent added difference
rows annihilate it. The step between the two vertices is maximal. No nonzero
row is tight at both endpoints, so h=d and loss=gain=d. All four slack terms
vanish. With N=1, equality holds in (7): `2*d=e+1`.

The all-3/2 point is strict. Irredundancy is explicit: to violate a lower or
upper coordinate bound alone, use the corresponding all-zero/all-three point
and change that coordinate by -1/2 or +1/2. To violate only difference row i,
set coordinates through i to 2 and all later coordinates to 0. These witnesses
are checked exactly through d=8 by the regression suite. The construction and
argument apply in every positive dimension; the finite tests are not the
universal proof.

## 4. A genuine no-overhead edge certificate

Suppose the walk starts at a vertex and EACH genuine step satisfies

```
loss(w_i,w_(i+1)) <= 1.                          (8)
```

By (1) and maximality (3), `p_(i+1)<=p_i`. Starting with p_0=0, all checkpoint
self-nullities stay zero. Moreover, `h_i=p_i+loss_i<=1`. A nontrivial step then
has a one-dimensional carrier and is an ordinary edge, by the existing
carrier-to-edge theorem. Thus the ORIGINAL witness is already an edge/stay
walk: no portal selection, detour, or length inflation is required.

This proof also explains why feasibility is retained when converting zero
self-nullity back into vertexhood. The Lean candidate contains this converse
explicitly rather than silently identifying every checkpoint with a vertex.

### Automatic small-row-excess consequence

The verified maximal-step source bound is

```
h_i+d <= n+p_i.
```

Since `h_i=p_i+loss_i`, it gives `loss_i+d<=n`. Therefore (8) is automatic for
`n<=d+1`. Every padded maximal circuit walk from a vertex in such a presentation
is already an ordinary edge/stay walk. Boundedness, irredundancy, strict
feasibility, and an extreme destination are unnecessary for this consequence.

When n=d, no genuine maximal circuit step can occur in a vertex-start walk.
When n=d+1, genuine steps can occur but are edges. This does not address the
hard exactly balanced regime n=2d for d>=4.

## 5. Two safeguards against overinterpreting the budget

### Average one is not pointwise one

In the two-dimensional sheared cube

```
0<=t<=1,  0<=z<=1+t,
```

consider `(0,0) -> (1,1) -> (2,1)`. Both are maximal circuit steps. Their
`(p,q,h,loss,gain)` records are `(0,1,2,2,1)` and `(1,0,1,0,1)`.
Total loss and gain both equal the number of genuine steps, namely two.
Nevertheless the intermediate point is not a vertex, and the ORIGINAL two
segments are not edges of the parent. Hence an average-loss condition cannot
replace (8).

There is a two-edge rounded route `(0,0)->(0,1)->(2,1)`. This example does NOT
refute existence of a same-length replacement. It refutes the claim that the
original witness must consist of edges.

### Rank alone does not pay graph distance

For each m>=1, take endpoints `(-m,0),(m,0)`. At each half-integer
`x=-m+1/2,...,m-1/2`, place the upper and lower vertices
`(x, +/- (m^2-x^2))`, in their convex boundary order. The resulting strictly
convex polygon has n=4m+2 edges. Its horizontal top/bottom edges provide
nonzero normals neutral to the horizontal endpoint displacement, which is
therefore a row circuit. The endpoint step is maximal and has loss=gain=2.
The two boundary paths between the endpoints both have 2m+1=n/2 edges.

Thus circuit length one and total rank loss two coexist with unbounded graph
distance as n grows. A rank-only constant-factor route estimate is false. A
row-dependent polynomial estimate is NOT refuted. This is consistent with the
repository's existing polygon warning, not a new claim that polynomial
refinement is impossible.

## 6. Executed regression evidence

The standalone standard-library suite uses exact Fraction arithmetic. It ran
with ordinary Python and with optimized Python; the outputs are byte-identical.
Explicit validation does not depend on Python assertions.

The seeded walk sweep covers 228 walks on 19 models in dimensions 1--4, with
1,409 genuine steps and 285 padding occurrences. It includes 169 vertex-to-vertex
walks, 59 nonvertex-start walks, 117 walks with a nonvertex checkpoint, and 110
vertex-start witnesses satisfying the pointwise rank-one certificate. These
are seeded finite samples, not exhaustive walk enumeration.

Additional checks cover empty/all-padding witnesses, duplicated and zero rows,
two unbounded examples, the sharp family through d=8 with strict-feasibility
and irredundancy witnesses, the average-one counterexample, and polygon barriers
with n=6,10,14,22,34. Invalid nonmaximal, noncircuit, and infeasible witnesses
are explicitly rejected.

The trace hash is
`b9298d5a60a2f69727daa55930f6fd29e05a605b082180af7662bf1d8f579f91`.
The complete JSON output SHA-256 is
`294901d06e6d88177469a3dfa71be5a7283fe0e1641b04b49cbb07ae33892689`.

## 7. Formal verification boundary and next action

The new Lean file imports the verified checkpoint/progress/carrier modules and
contains proofs with no admission commands. It has NOT been compiled in this
session: no local Lean/Lake executable was present and the attempted toolchain
download was unsuccessful. Static source inspection and rational tests do not
establish kernel acceptance. No speculative GitHub Actions compiler loop was
started.

In the pinned repository, run

```
bash scripts/verify_circuit_walk_rank_budget.sh --checks-only
bash scripts/verify_circuit_walk_rank_budget.sh
```

The full local gate requires successful compilation and seven fresh axiom
reports, then writes a source-verification receipt. It never authenticates or
publishes. A successful source gate would still NOT be a standalone public
adapter or a Prove2Me verdict. The source remains a draft until that gate runs.

The global Open leaf remains
`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
(`73beca40-31bc-42d5-8350-5ec9ac28bd3e`). No new conjectural child is proposed.
The concrete research issue is now clearer: paying geometric portal/edge cost
for the rank-at-least-two events, without mistaking globally balanced rank
accounts for locally cheap routes. The conservation identity alone does not
supply that missing cost estimate.
