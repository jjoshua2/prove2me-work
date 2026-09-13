# Coherent cycle cancellation removes the resonance denominator

## What changes after the gain-lattice result

This add-only continuation starts from PR #210 at
`4d82742bf8acd4905bb2933bec09839a8d3ed7e9`. It leaves the gain-lattice, signed,
network and Minkowski implementations unchanged. The new route wrapper reuses
the exact original-H gain shadow solver; dependency hashes are in the receipt.

The preceding theorem bounded every inverse entry by Gamma/eta, where eta was
a lower bound on nontrivial cycle gain defects. Its affine-invariant example
showed why a uniform all-basis separation parameter cannot be recovered in
general. Neither statement implies that the relevant NORMAL CONES become narrow.
The signs of the positive cone generators contain information that a condition
number discards.

The new result controls the cones directly. Dense magnitude-balanced support
blocks may be joined through coherently directed single-cycle blocks. With
Gamma the product of the multiplicative distortions of the unbalanced cycles,
every vertex normal cone is at least

    tau = 1/(2 Gamma^2 d^(3/2))

wide, in one globally fixed coordinate gauge. There is NO divisor involving the
minimum of |1-G_cycle|. In particular, Gamma<=2 gives the classical derived
ordinary-edge diameter bound 256d^3, uniformly in how close any cycle product
is to one. Different cycle products need not be powers of one common base.

The exact class is closed under actual endpoint-common-face restriction. Thus
an h-dimensional carrier inherits 256h^3, unlike the previous ambient-calibrated
gain estimate that retained its original dimension parameter. This is a new
sufficient routing regime, not an unconditional Polynomial Hirsch result.

The graph/cone argument below is mathematical; two new Lean files supply finite
algebraic and route-accounting cores but remain UNCOMPILED. The analytic diameter
step is explicitly classical, not a new axiom or newly best general theorem.

## 1. The exact structural certificate

Every nonconstant row has one nonzero coefficient, or two coefficients of opposite
sign. A binary homogeneous equality has form x_v=g_r*x_u, g_r>0, oriented from
its negative coefficient to its positive coefficient. Unary rows are arbitrary
upper/lower bounds. Zero rows and duplicate positive-proportional normals are
allowed. All original inequalities remain in the route problem and verifier.
Only the normal-ray graph uses one representative per positive-proportional row.

Choose a spanning forest T of the undirected binary support multigraph. Propagate
positive coordinate scales s_v=g_r*s_u on T, so every forest gain becomes one.
For each nonforest row, list its fundamental cycle, with a traversal and exact
multiplicative gain G_C (invert a row gain when traversing it backwards).

The certificate requires:

* A fundamental cycle with G_C=1 can have any orientation and can overlap other
  balanced fundamental cycles.
* A cycle with G_C!=1 must be coherently directed, and its edges must be disjoint
  from the edges of EVERY other fundamental cycle.

Thus balanced blocks can be dense; the support graph need not be a cactus. A
particularly transparent subclass is a directed cactus, where each undirected
edge lies on at most one simple cycle and every cycle is coherently directed.
Parallel opposite-direction rows can form a two-edge cycle.

Why this finite certificate controls all simple cycles: every simple cycle is
a symmetric difference of fundamental cycles. An isolated nonunit fundamental
cycle contributes either all of its edges or none, because no other fundamental
cycle can cancel one of them. If a simple cycle contains all those edges, it
must be that cycle itself. Every remaining simple cycle uses only forest rows
and unit-gain chords; its gain is one in the forest gauge. Equivalently, each
non-balanced biconnected block is just its isolated directed cycle. Balanced
biconnected blocks may contain arbitrary overlapping cycles.

The verifier checks forest acyclicity and spanning, all original-row scaling
identities, the complete nonforest-row cover, simple/closed cycle traversals,
exact cycle gains, coherent orientation where necessary, and edge-disjointness
of each nonunit cycle from all the other fundamental cycles. It does not enumerate
all bases or vertices. Missing cycles or an incoherent nonunit cycle are rejected.

Set

    Gamma = product_C max(G_C, 1/G_C) >= 1.                   (1)

Balanced cycles contribute one. In the global forest gauge, every simple path
has gain magnitude between 1/Gamma and Gamma: its nonunit factors come from
distinct chords. Every unbalanced simple cycle is one of the certified cycles,
so its gain is in that same interval. Arbitrary original row scalings and
coordinate scales have been removed without changing the face graph.

There is no gain_base input and no exponent-lattice hypothesis.

## 2. Every independent basis has only two kinds of components

Let B be ANY nonsingular d-row basis of the globally gauged normals. Partition
its coordinates into connected binary-support components. Full rank forces each
component's number of rows to equal its number of coordinates. Connectivity
then leaves exactly two possibilities:

1. A binary tree with exactly one unary row.
2. A connected unicyclic binary graph with no unary row.

In the second case, a cycle of gain one would leave a homogeneous degree of
freedom and contradict nonsingularity. Its cycle is therefore one of the
isolated coherently directed nonunit cycles certified above. A dense balanced
block cannot introduce an extra nonsingular cyclic component.

For the proof of cone width, a second, BASIS-DEPENDENT diagonal gauge normalizes
a spanning tree of each component. Choose its smallest scale to be one.
Ratios between its coordinates are simple path gains in the GLOBAL model, so
its condition number is at most Gamma. This secondary gauge is only an analysis
tool; it is transported back before making a uniform statement about the normal
fan. Using a different uncorrected metric at each vertex would be invalid.

Positively rescale individual rows in the secondary gauge. Every tree row is
now e_v-e_u, and every unary row is +/-e_u. In a cyclic component, all but one
cycle row have this unit-difference form. The closing row is e_head-G*e_tail,
where G is the total directed cycle gain and G!=1.

## 3. The small cycle defect cancels out of the cone margin

Let a_j denote these secondary-gauge basis rows and u_j their dual columns:
<a_i,u_j> is one for i=j and zero otherwise. A vector c is in their positive
cone exactly when every <c,u_j> is nonnegative.

### Tree with a unary pin

Choose c_component=sum_j a_j over that component. Every dual margin is one.
The inverse columns are signed indicator vectors of connected subtrees, so
||u_j||<=sqrt(d). The center norm is at most sqrt(2) times the component size.

### Coherently directed unicyclic component

The oriented cycle rows telescope:

    sum_cycle a_j = (1-G)*e_tail.                            (2)

All coefficients in this sum are POSITIVE. Let the remaining rows in that
component be its off-cycle tree edges, and choose

    c_component = sign(1-G)*e_tail + sum_off-cycle a_j.        (3)

Equation (2) gives a positive representation with cycle coefficients
1/|1-G| and off-cycle coefficients one. Therefore

    <c_component,u_j> = 1/|1-G|   for a cycle row,
                       1          for an off-cycle row.     (4)

Deleting an off-cycle row leaves one unit-gain free subtree, so its inverse
column has norm at most sqrt(d). Deleting a cycle row leaves a tree containing
at most the one remaining exceptional edge. Its inverse entries have magnitudes
at most max(1,G)/|1-G|; branches inherit their attachment coordinate. Thus

    ||u_j|| <= Gamma*sqrt(d)/|1-G|   for a cycle row.          (5)

Combining (4) and (5), the normalized positive margin is at least
1/(Gamma*sqrt(d)). The arbitrarily small cycle defect cancels from the ratio.
It must NOT be estimated separately as a small singular-value parameter.

The vector (3) itself has no large cycle coefficient after cancellation. Its
norm is at most one plus sqrt(2) times the number of off-cycle edges. This is
at most twice the component size.

### Assemble components and return to one global metric

Use these centers on their disjoint coordinate blocks. The complete center c
has norm at most 2d and every dual margin divided by dual norm is at least
1/(Gamma*sqrt(d)). Cauchy--Schwarz therefore puts a ball of radius
1/(Gamma*sqrt(d)) around c inside the basis cone. Normalize c to unit length:
the secondary-gauge cone is at least 1/(2 Gamma d^(3/2))-wide.

Transport through the inverse secondary diagonal. A linear map can reduce this
unit-centered ball radius by at most its condition number, which is at most
Gamma. Hence, in the SINGLE global forest gauge,

    every independent basis cone is tau-wide,
    tau = 1/(2 Gamma^2 d^(3/2)).                             (6)

At a possibly nonsimple vertex, choose any independent active basis. Its cone
lies inside the full vertex normal cone, so (6) holds there too. No assumption
of simplicity, a lower cycle-gap bound, or a bounded number of vertices enters
this argument. Full-dimensional pointedness is required when applying the
analytic theorem below; given endpoint vertices, the intrinsic carrier has it.

## 4. A direct demonstration of the distinction from inverse conditioning

In dimension two take the four inequalities

    x>=0, y>=0, y-x<=1, (1+epsilon)x-y<=1, epsilon>0.         (7)

This is a quadrilateral with vertices
(0,0), (0,1), (1/(1+epsilon),0), and (2/epsilon,2/epsilon+1).
All four inequalities are genuine facets. The nearly resonant two-row cycle
basis is feasible at the last vertex, not merely an irrelevant infeasible basis.
Its normalized inverse has an entry 1+1/epsilon.

Nevertheless, its cone has a unit-centered ball with a fixed positive radius.
The explicit cone witness has squared dual margin at least 1/2, independent
of epsilon. The forest-normalized total transport product is 1+epsilon, tending
to ONE as the inverse tends to infinity.

The unoriented lines in (7) also realize the previous four-row cross-ratio
obstruction (after switching a row sign and relabeling coordinate lines).
That obstruction is to all-basis relative separation, which is sign-invariant.
It does not force the POSITIVE cones of the oriented inequalities to be narrow.
This is not a contradiction or a workaround through infeasible bases: the very
same feasible bad basis is already wide in the original coordinate scale.

The code tests epsilon=2^-8,2^-40,2^-120,2^-240, for cycle gain both above and
below one. The inverse blow-up is checked exactly, along with the positive cone
margin. A same-direction nearly parallel two-row cycle fails coherent orientation
and is rejected. Ignoring row signs would lose this essential distinction.

## 5. Heredity in the actual endpoint face

Collect every inequality tight at both requested endpoints. Its homogeneous gain
graph decomposes into consistent free components and pinned components. A unary
row or a nonunit cycle pins its component. On a free component, coordinates have
form x_i=offset_i+s_i*t_C with s_i>0. This is an onto affine parametrization of
the common equality space, not a relaxation.

Substitute into ALL original inequalities. Rows between free components remain
opposite-signed binary rows. Rows within one component become constant or unary;
rows joining a pinned component to a free one become unary. A positive rescaling
normalizes a small nonzero unary coefficient, even when it contains 1-G.
This cannot create a small-angle problem in one dimension.

Graphically this contracts consistent equality components and removes pinned
ones. Balanced blocks stay balanced. An isolated coherent cycle either survives
as a shorter coherent cycle of the SAME gain, becomes unary, or disappears.
Contractions cannot manufacture a new mixed cycle across blocks. Consequently

    Gamma_face <= Gamma_parent.                             (8)

All nonconstant restricted rows are strict at the endpoint midpoint. Otherwise
nonnegative endpoint slacks would force the row tight at both endpoints, so it
would already be a defining equality. Thus this is an intrinsic full-dimensional
model of the smallest common face. Its endpoints remain vertices.

The certificate is hereditary in the intrinsic dimension h, not merely through
an inherited ambient separation estimate. Repeating (6) in the intrinsic model
gives tau_face>=1/(2 Gamma_face^2 h^(3/2)). The exact wrapper constructs this face,
rechecks its graph certificate, and explicitly verifies (8). It never assumes an
ambient route stays inside the carrier.

## 6. Ordinary-edge diameter and selected-carrier consequence

The external theorem used is Dadush--Haehnle, *On the Shadow Simplex Method for
Curved Polyhedra*, arXiv:1412.6705, Theorem 3 / Theorem 11: an h-dimensional pointed
polyhedron whose vertex normal cones are tau-wide has graph diameter at most
(8h/tau)(1+ln(1/tau)). It applies to ordinary edges and does not require simplicity.
The paper explicitly separates this existence claim from efficient degenerate
implementation. We do not claim that theorem as new.

When Gamma<=2, (6) permits tau=1/(8h^(3/2)). Therefore, for h>=1,

    diameter <=64 h^(5/2)*(1+ln8+(3/2)ln h) <=256 h^3.       (9)

The last inequality uses ln8<=3 and ln h<=2(sqrt(h)-1), so the parenthesis is
at most 1+3sqrt(h)<=4sqrt(h). A point carrier has zero cost.

The result is independent of how closely cycle gains approach one. It also
requires no common exponent lattice. For example G1=1-2^-80 and G2=1-3^-60
are both less than one, but their powers of two have valuations -80 and +4.
If they were integer powers of one q>1, their exponents would both be negative;
cross-multiplication would equate positive integer powers of G1 and G2, impossible
from these opposite valuation signs. Even a nonrational common base would not
fix that integer-power identity.

For arbitrarily many cycles one can take independent rational deficits with
sum at most 1/2; product(1-deficit)>=1-sum(deficit) gives Gamma<=2. Dense balanced
blocks and arbitrary original positive coordinate/row rescalings do not change
these cycle products. Large Gamma is allowed by the certificate but does not
receive the fixed 256h^3 bound.

Finally, if the SAME actual carriers in the verified full-availability clipping
certificate have these models, sum h_i<=3e with e=n-d. Thus

    sum local_cost_i <=256 H^2 sum h_i <=768 H^2 e,
    assembled cost <=D+768 H^2 e.                            (10)

The target-rooted specialization is 1+768d^2(n-d). Applicability to arbitrary
carriers is NOT proved. The new Lean file makes the cubic-rate composition
generic in K; (10) is its K=256 specialization. It consumes actual local routes
and count evidence, not model labels or an imported analytic axiom.

## 7. Exact construction, independent verification, and executed examples

The structural constructor supplies a forest, diagonal gauge and full list of
fundamental cycles. The checker does not invoke that forest search. For each
basis visited by the route, the constructor builds the center (3) and transports
it back. The independent numerical cone verifier recomputes the inverse and
checks, for every dual column u_j,

    <c,u_j> >0,
    <c,u_j>^2 >= tau^2 ||u_j||^2 ||c||^2.

These inequalities use exact rational arithmetic and prove a whole ball in the
cone without numerical square roots. They do not infer width from a small set
of test directions. The all-basis theorem above does not rely on visiting every
basis; these certificates independently audit the formulas on actual examples.

The route constructor reuses the existing arbitrary-gain shadow engine, including
its finite symbolic RHS lexicographic tie breaking. Reported vertices and edges
belong to the ORIGINAL inequalities. The existing verifier checks all original
rows, shared active rank d-1 and endpoint blockers at every nonstationary pivot.
The new wrapper additionally validates the parent and actual-face structural
certificates and every visited cone witness.

The finite endpoint-objective sampler is NOT the random distribution used in
the published expected-length proof. No uniform polynomial pivot count or runtime
is claimed for this sampler or for its capped degenerate endpoint-basis search.
A returned route's actual length is checked separately from the existence bound.
No global vertex enumeration is used for the larger examples.

Representative exact outputs:

| Input dimension | Rows | Unbalanced coherent cycles | Constructed edges |
|---|---:|---:|---:|
| 12 |28|5|12|
| 24 |58|11|24|
| 32 |78|15|32|
| 12, with a dense balanced core |58|2|23|

The dense core has 21 overlapping balanced fundamental cycles and is not a
cactus. The first two exceptional cycle gains in the larger examples are
1-2^-120 and 1-3^-60. Their inverse singularities are not replaced by a positive
uniform gap. The sparse connected five-dimensional small example has eleven
rows and forty vertices, so it is not a cube. Three additional cases recover
unknown positive coordinate scales and row permutations, including factors2^180.
The displayed routes are not asserted shortest.

The final execution checks 6,562 basis subsets, with 1,539 nonsingular cones
independently verified using Gaussian elimination. Libraries through dimension
five, including the dense balanced-block library, are exhaustive; the dimension
six library uses 1,600 sampled subsets. The structural proof, not sampling,
extends to all dimensions and bases.

Seven independent original-H graph enumerations give 93 vertices,188 edges and
2,793 ordered graph distances. Their 1,443 constructed routes contain3,965 edges
and two stationary pivots. All nonpoint endpoint faces (1,350 cases) satisfy the
independently rechecked contraction certificate. Seven larger/scaled examples
bring the total to1,450 route certificates and4,077 ordinary-edge occurrences.
Nineteen invalid/forged cases are rejected. The exact source-hashed receipt
records these counts; the tests regenerate the large input and route fixtures.

## 8. Formalization boundary and next problem

Two new Lean candidates supply coherent row telescoping, the positive normalized
cycle ray, cancellation of the dual denominator, squared-margin interpretation,
whole-ball inclusion from a dual frame, linear transport of cone balls, and the
generic actual selected-carrier cubic assembly. They are NOT compiled in this
session. The all-basis block classification, hereditary model extraction and
external analytic diameter theorem remain written proofs / exact implementations,
not a single new end-to-end Lean diameter theorem. No hosted verification,
platform submission, new root child or Prove2Me acceptance is claimed.

The missing general cases include noncoherently oriented resonant cycles and
unbalanced cycles that interact through a common block. These may give genuinely
narrow normal cones rather than the harmless broad-cone resonance handled here.
A large total transport product can also spoil the bound. Neither a complete
edge-direction dictionary nor a uniform inverse bound is required for the new
regime, but that does not make it universal.

The next direction should distinguish a positive near-dependence (a potentially
wide cone) from a signed cancellation that actually pinches feasible cones.
The previous cycle-gap obstruction is not the final boundary: coherent positive
cancellation already crosses it, even for unrelated gain scales and a feasible
basis with inverse entries of size2^240.

Primary external theorem: Daniel Dadush and Nicolai Haehnle,
https://arxiv.org/html/1412.6705 , Theorems3 and11. The analytic theorem is cited,
not added to Lean as an axiom. The remainder above is the explicit argument
for the new structural certificate and its stated scope.
