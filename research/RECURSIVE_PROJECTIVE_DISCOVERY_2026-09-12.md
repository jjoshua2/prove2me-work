# Automatic chart recovery and recursive projective product routing

## Scope, independence and status

This continuation follows merged, platform-accepted #203 on main
`a42d88d5a822428e9bb3965a7188e91ff06951d1`. The original #204 candidate is
preserved at `55edf3dee8f80685fe100467f57f4b95b20c9b5a`.
Both original Lean modules compiled unchanged against integrated #203.
The final proof source `fcbb02425dececaa9a8f7abd90c341ae99dbafac` moves the
geometric `ProductTree` predicate into a lightweight standalone definition,
expanding the row-shear and denominator expressions there. The recursive
induction, carrier adapter and separator proofs are unchanged.

The final targeted local build passes. Seven required declarations and 272
reports across dependencies use only standard logical axioms; the small-excess
input remains explicit. The standalone recursive proof also passes its own
standard-axiom audit, and the exact public composition typechecks. The public
interface stub is typechecking evidence. Prove2Me theorem
`4afd7668-51a9-4a5e-a991-2a02c53b9e1c` is **Proved**, with accepted submission
`7f2bba60-85ad-42d5-8a1a-eed656add3f5`; the exact source readback is preserved
in [the publication packet](publication_packets/recursive_projective_products/).
The [verification directory](verification/2026-09-12-recursive-projective/)
records fresh rational tests, the exact source and final hosted verification.

The full recognition-completeness proof, generated-witness formulas and infinite
family arguments remain mathematical proofs in this note; they are not all
formalized Lean declarations. The exact rational checker does not emit Lean
proof terms. No unproved platform child is added to the conjecture's root.

The contribution is an exact, finite chart-discovery method and its combination
with recursive cost-preserving geometric decompositions. Projective invariance,
linear rank-nullity, product graph additivity, and small-excess bounds are
classical/reused ingredients; no claim of classical novelty is made.

## 1. Recover the chart from a homogeneous rank-one separator

Let Q be a bounded full-dimensional polytope in R^d with an irredundant rational
facet description A_i y <= b_i. Translate a supplied strictly interior point to
0, so every b_i is strictly positive. Suppose a strictly positive vector w
satisfies sum_i w_i A_i = 0. Full column rank and this positive balance certify
boundedness: every recession direction has nonpositive evaluations, their
strictly positive weighted sum is zero, hence each evaluation is zero and the
direction vanishes. The origin certifies nonemptiness and full dimension.

Form homogeneous covectors

```
R_i = (A_i,-b_i) in R^(d+1).
```

They span the whole homogeneous space: the positive balance gives the nonzero
constant covector (0,-sum w_i b_i), and the spatial normals have rank d.
For a bipartition S,T of ALL describing rows, set U=span(R_S), V=span(R_T).
Search for

```
rank(U) >= 2, rank(V) >= 2,
rank(U) + rank(V) = d+2.                         (1)
```

Since U+V has dimension d+1, their intersection is exactly one line L. If its
nonzero vector is (v,t) with t != 0, normalize it to (c,-1), where c=-v/t.
This recovers ONE candidate chart by exact linear algebra; there is no
continuous optimization over c. If t=0, the infinity hyperplane passes through
the interior origin, so this line cannot give an admissible positive chart.

The spatial projection

```
q_c(a,t) = a+t*c
```

has kernel L and sends R_i to A_i-b_i*c, precisely the unshearing in #203.
The projected block spans are complementary. Indeed, if q_c(u)=q_c(v) for
u in U and v in V, then u-v lies in L, hence u lies in U intersect V=L and
the common image is zero. They span R^d, and their dimensions are rank(U)-1
and rank(V)-1. Choose bases of these two row-functional subspaces: in the dual
coordinate system the two groups of inequalities involve independent variables.
Once the chart's positivity is certified, their feasible set is an actual
Cartesian product, not merely a face cover or a graph approximation.

`PolynomialProjectiveSeparatorAlgebra.lean` records the kernel-line formula,
uniqueness of the normalized chart, and the complementary-image primitives.
The full rank-search recognition theorem is proved here; the Python search
checks these ranks exactly. No claim is made that the exhaustive search theorem
has been fully formalized in Lean in this PR.

### Why the candidate list is complete for one projective split

Conversely, suppose some positive projective chart, followed by an affine
coordinate change, identifies Q with a product of two bounded positive-
dimensional polytopes. Their facet groups define a bipartition S,T. In the
product chart, each group's spatial normals span its factor's dual space.
Boundedness gives a positive normal dependence within each group, whose RHS is
strictly positive by full dimensionality. Thus each homogeneous group contains
the constant/infinity line and has dimension factor_dimension+1. Their spans
meet exactly in that line and satisfy (1).

A general projective transformation introduces no additional candidates: after
translating the input interior point and subtracting its output image, its
numerator is linear and its denominator is a nonzero constant plus a linear
functional. Absorb the invertible numerator into the later linear coordinate
change and normalize the denominator. It is exactly the q_c/perspective form.

Therefore, enumerating every bipartition and checking its unique candidate
line finds every possible nontrivial positive projective product chart (up to
later affine coordinate changes). For rational input the recovered line, and
hence the normalized chart, is rational even if an initial equivalence was
described with real coefficients. Different bipartitions may give the same
line; deduplicate exact c vectors.

**Qualifications:** this geometric completeness statement assumes a genuine
irredundant facet description. Positive certificates remain sound on redundant
inputs, but a missed redundant presentation is not a geometric nonexistence
proof. The implementation does not remove rows, skips candidates producing a
tautological row, and exposes search caps. It never labels a capped search as
exhaustive. It enumerates all first-step chart candidates only with
`--max-side 0`. It does NOT claim a polynomial-time recognition algorithm or
that its recursive finest-component search minimizes over every possible tree.

## 2. Generate the positivity/boundedness evidence, not just the chart

Previously #203 required source/target denominator multipliers and source
boundedness evidence to be supplied separately. Here all source evidence is
derived from the TARGET positive balance and one target positivity witness.

Find nonnegative lambda with

```
sum lambda_i A_i = c,
L0 = sum lambda_i b_i < 1.
```

This certifies 1-c.y >= 1-L0 > 0 on Q. Define

```
W = sum w_i b_i > 0,   t = 1-L0 > 0,
A0_i = A_i-b_i*c,
beta_i = t*w_i + W*lambda_i.
```

Direct calculation gives beta_i>0 and sum beta_i A0_i=0. Full rank of the
unsheared rows follows from the surjectivity of q_c and the full homogeneous
rank. Thus the source description is nonempty, full-dimensional and bounded.

Choose alpha>0 sufficiently small that w_i-alpha*lambda_i>=0 for every i; the
implementation uses half the minimum positive ratio w_i/lambda_i. Put

```
mu_i = (w_i-alpha*lambda_i)/(W+alpha*t).
```

Then

```
sum mu_i A0_i = -c,
1-sum mu_i b_i = alpha/(W+alpha*t) > 0.
```

So mu supplies the SOURCE denominator certificate, closing both directions
of the chart. The case c=0 uses lambda=0 and works with the same formulas.
Every one of these identities and signs is rechecked independently by the
verifier; it does not trust the discovery code or an optimizer return status.

The lambda search first tries sparse supports, then enumerates independent
d-row dual bases exactly. Standard finite-dimensional LP duality guarantees a
basic optimum when Q is bounded and full-dimensional; hence a strictly positive
denominator on all of Q is detected by the exhaustive fallback. All arithmetic
is rational. The routine is exponential in the worst case and makes no
bit-complexity or fast-construction claim.

## 3. Recurse on the factors, allowing DIFFERENT charts

After one valid split, do not require every factor to be small-excess already.
Run the same discovery inside each factor, with its own recovered chart and
its own recentered coordinates. A tree leaf is discharged only when its
actual row count m and dimension h satisfy m-h<=3 and boundedness is certified.

At every proper split:

```
sum child_dimensions = parent_dimension,
sum child_row_counts = parent_row_count,
sum child_excesses = parent_excess.              (2)
```

The children are an actual product, so ordinary-edge routing costs ADD.
The positive projective chart and affine equivalence preserve those costs.
Induction on the finite tree gives

```
diam(Q) <= sum_leaf (m_leaf-h_leaf) = n-d.       (3)
```

This is a genuine additive resource argument for this certified class: no node
multiplies a recursive call's budget. Proper positive-dimensional splits give
at most d leaves and d-1 split nodes; each path has at most d-1 split steps.
These are certificate-size/dimension facts, not bounds on search work.

`PolynomialRecursiveProjectiveProducts.lean` defines `ProductTree` using actual
row identities, coordinate equivalences, positive chart domains and small-excess
leaves. Its induction proves the ordinary-edge bound, rather than defining a
certificate to mean that a diameter bound exists. It also feeds equivalent
intrinsic certificates for the ACTUAL selected clipping pairs to the existing
callback at safe total cost

```
D + n*r.
```

For target-rooted certificates r<=n-d and D=1, this is quadratic whenever all
selected carriers have such a certificate. That applicability is not assumed
for arbitrary polytopes and does not prove the root conjecture.

## 4. A family strictly beyond #203's one-chart small-block criterion

Fix 0<epsilon<1. For d>=1, define the triangular interval tower T_d by

```
0 <= x_1 <= 1,
0 <= x_i <= 1+epsilon*x_(i-1),   2<=i<=d.
```

It is bounded, full-dimensional, and has 2d genuine facets. The last coordinate
is an interval of positive affine width over T_(d-1). More generally, for a
bounded P and positive affine f(x)=1+c.x on P, the projective map

```
(x,t) |-> (x/f(x), t/f(x))
```

maps `{x in P, 0<=t<=f(x)}` EXACTLY onto `f_projective(P) x [0,1]`.
The inverse sends a base coordinate back to x and the interval coordinate s to
s*f(x). Both denominators are positive. Thus each tower splits into an interval
and a projective image of the preceding tower. Applying a new chart inside
that factor, repeatedly, gives a recursive interval product tree and diameter
d. This argument also identifies its face lattice with that of a d-cube.

### Why no single chart can expose all small factors when d>=5

For d>=3, the only nontrivial one-step projective factorization has dimensions
(d-1,1). Here is a direct proof, not an inference from a few numerical tests.

The two facets for coordinate i are the unique disjoint pair containing either
of them. Facets belonging to different Cartesian factors meet, so the two
facets in each opposing pair must belong to the SAME factor under any
projective product decomposition.

In the original tower coordinates the lower normals are -e_i and their RHS
is zero. They are unchanged by any normalized unshear A_i-b_i*c. Since they
form a basis, factor row-functional subspaces must be spans of a partition of
these coordinate directions. Each upper normal becomes

```
e_i - epsilon*e_(i-1) - c,     i>1,
e_1-c,                       i=1.
```

For coordinate k outside i's factor, its coefficient must vanish. If a chain
edge k -> k+1 crosses factors, this forces c_k=-epsilon. But every OTHER
index j outside k's factor would force c_k=0. Consequently the entire
complement of k's factor must be the singleton {k+1}.

A proper partition of the chain has a crossing edge. The isolated coordinate
k+1 cannot be internal to the chain: its outgoing crossing edge would require
its complement also to be a singleton, impossible for d>=3. Thus the only
isolated coordinate is d, with the other coordinates in one factor. The chart
is uniquely c=-epsilon*e_(d-1), and all other c coordinates are zero.

Its factors have row counts 2(d-1),2 and excesses d-1,1. For d>=5 the large
factor has excess greater than three, so #203's ONE-CHART criterion cannot
discharge it, regardless of which chart is proposed. Recursion can.

For epsilon=1/4 the exact program recovers these charts automatically. The
five-dimensional fixture requires two split nodes to reach leaf excesses
3,1,1 and obtains bound 5. Dimensions through 12 are tested; dimension 12
has 24 rows, nine split nodes, ten leaves and bound 12. With a one-excess leaf
threshold, the seven-dimensional example splits into seven intervals.

These towers still have connected affine normal matroids (the upper normals
link each consecutive pair of coordinate directions). At target 0 all upper
facets share the all-upper vertex, so the previous clique argument still gives
shortest-repair deficit at least d-2. Thus the new class is not merely the
bounded-deficit case in different notation.

## 5. Where the method honestly stops

Replace the open chain by a cycle, with constraints

```
0<=x_i<=1+epsilon*x_(i-1 mod d).
```

The four- and five-dimensional rational fixtures have NO homogeneous rank-one
bipartition at all, as checked exhaustively. Independent active-set vertex and
edge enumeration nevertheless gives cube graphs and diameters 4 and 5. The
implementation returns `unresolved`, NOT a lower bound or a false product
certificate. These are finite exact negative controls; a new universal cyclic
cube theorem is not claimed Lean-formalized here.

The subsequent [contractive feedback proof](CONTRACTIVE_FEEDBACK_BOXES_2026-09-12.md)
now supplies direct ordinary-edge routes for all these cyclic examples, in
every dimension, using the witness M*w<w. It also proves that the cyclic family
has no projective product split in d>=3. This is a paper proof with a separate
finite regression, not an additional Lean theorem or acceptance claim.

This sharpens the next mathematical target: route genuinely coupled systems
with no projective product separator, or derive a joint carrier-cost potential
that does not require a separator. Extending the tree by an unsupported
'coupled leaf is easy' constructor would merely hide the unsolved obligation
and must not be done.

## 6. Reproduction and verification handoff

Only Python's standard library is needed; the new checker is self-contained.
It never calls a network service or handles credentials.

```
python3 scripts/test_projective_factor_discovery.py
python3 scripts/projective_factor_discovery.py \
  research/triangular_tower_5d_input.json --output /tmp/tower-certificate.json
python3 scripts/projective_factor_discovery.py \
  research/triangular_tower_5d_input.json --verify /tmp/tower-certificate.json
```

Default discovery searches partition sides of size at most three, plus the
zero-chart affine factorization. `--max-side 0` enumerates all bipartitions;
this is exponential, not a recommended default for large inputs. Each
candidate's positivity search may also use an exponential dual-basis fallback.
A capped failure remains explicitly partial. The independent verifier only
checks the produced tree, not any assertion of optimality or search exhaustion.

Executed checks: 32 positive certificates; exhaustive one-step chart searches
for towers in dimensions 3 through 7; 120 independently enumerated vertices,
256 edges and 2,720 ordered graph-pair distances; 32 source-to-target vertex
maps; and 15 negative controls. Those controls include malformed balance,
non-interior input, floating-point numbers, corrupt inverse/row/denominator
certificates, an invalid excess-four leaf, capped-search diagnostics, and the
genuinely cyclic unresolved examples. Counts for the cyclic graph checks are
reported separately and not inflated into the positive graph totals.

The verified targeted Lean gate is

```
lake build Solutions.PolynomialProjectiveSeparatorAlgebra \
  Solutions.PolynomialRecursiveProjectiveProducts
```

Audit all seven explicitly printed new theorem dependencies, allowing only the
repository-standard logical axioms; the classical small-excess input stays
explicit. The full recognition/completeness proof, witness-generation algebra,
and infinite tower/non-single-chart arguments are mathematical results in this
note, not all formalized Lean declarations. Individual JSON certificates are
not emitted as Lean proof terms. Do not confuse the independently verified
rational checker with a kernel certificate.

The final hosted gate is run `34712133611` on source `fcbb024`. An initial
dispatch selected stale source `55edf3d` immediately after the push; that run
`34712025298` was cancelled, and the correct remote ref was confirmed before
redispatch. It is not verification evidence. No workflow or Lean pin changes
were needed. Authenticated publication status is preserved in the packet and
STATUS.md; local compilation alone does not establish platform acceptance.
