# Signed two-variable normals: bounded inverse geometry without balanced sign cycles

## Contribution and exact scope

This is an add-only continuation of the direct-carrier work in PR #210. It does
not replace either of the existing network implementations. Those recognize
positive diagonal scalings of ordinary difference constraints. The present
class permits same-sign rows and negative signed cycles. A typical example is

    x_i >= 0,  x_i+x_j <= 1,

with a nonbipartite constraint graph. It is not reducible to ordinary differences
by assigning signs to coordinates: an odd cycle prevents consistent switching.
No assertion is made that such a polytope cannot have some unrelated dense
network representation under a more general affine transformation.

After positive row/coordinate scaling, each nonzero row has one or two entries
in {-1,1}. All right-hand sides may be arbitrary real numbers for the mathematical
results and rational numbers for the implementation. Redundant rows, nonsimple
vertices, implicit equalities and unbounded polyhedra are allowed. A requested
route needs two feasible vertices; lineality in an irrelevant ambient space is
not silently treated as a vertex.

The main mathematical fact is that every nonsingular square basis B of these
rows has

    (B^-1)_ij in {0, -1, 1, -1/2, 1/2}.                     (1)

This gives a global delta-distance bound 1/sqrt(2d), despite determinants as
large as 2^floor(d/2). Applying the CLASSICAL wide-normal-fan diameter theorem of
Dadush--Haehnle gives a safe explicit ordinary-edge bound 36d^3. After restriction
to the endpoints' actual common face, d is replaced by its dimension h.

This is a derived application of an established theorem, not a claim to have
invented a new shadow-simplex diameter theorem or proved the full Polynomial
Hirsch Conjecture. The exact rational implementation below follows a generic
parametric objective with symbolic right-hand-side tie breaking. It is NOT the
random sampler used in the cited expected-length proof. We distinguish the
uniform existence result from the particular finite routes actually produced.

## 1. Homogeneous signed components and inverse columns

A homogeneous two-variable row with unit coefficients says z_j=s*z_i, where
s is +1 or -1. A unary row says z_i=0. For each connected component, choose a
root and propagate signs along a spanning tree.

If every remaining edge agrees with the propagated signs and no unary row
occurs, the component is balanced and unpinned. Its kernel consists of one
free parameter times its sign vector. If a unary row occurs, that parameter
is zero. If a non-tree edge disagrees with the propagated signs, traversing
the corresponding cycle says z_root=-z_root, so the parameter is also zero.
Consequently

    kernel dimension = number of balanced, unpinned components.              (2)

This holds for dependent row collections, disconnected graphs, parallel edges
and the empty collection. It is not ordinary graph connectivity. A triangle
of equations z_1+z_2=z_2+z_3=z_3+z_1=0 has trivial kernel despite lacking a unary
row. The old pinned-network-component test would miss that fact.

Now delete row j of a nonsingular d-row basis B. The remaining rows have rank
d-1, so (2) supplies exactly one unpinned balanced component. Let g have its
propagated signs on that component and zero outside. Thus g has coordinates
in {0,+1,-1}, all other rows annihilate g, and row j does not. Since row j has
at most two unit coefficients,

    (B g)_j is one of -2,-1,1,2.

Dividing g by that value gives the j-th column of B^-1. This proves (1) without
bounding a full determinant and without enumerating all bases.

An alternative determinant description is consistent with this proof: square
basis components are trees pinned by one unary equation, or unicyclic components
whose cycle is sign-unbalanced. Their determinants have magnitude one or two,
respectively. Determinants multiply across components. In dimension64, the
block diagonal matrix with32 blocks [[1,1],[1,-1]] has determinant magnitude
2^32=4,294,967,296, yet every inverse entry has magnitude at most1/2. Using a
bound quadratic in the largest subdeterminant would lose this structure.

The implementation computes inverse columns by this deleted-row graph method.
It verifies B*column=e_j exactly for every column and checks the inverse alphabet.
Independent Gaussian elimination checks all nonsingular small test bases and
the large determinant example. The all-dimension justification remains the
structural proof above, not an extrapolation from those tests.

## 2. From inverse bounds to an explicit polynomial edge diameter

Let a_1,...,a_d be a basis of the normalized signed rows, and let u_j be column j
of B^-1, interpreted in Euclidean space. Then

    <a_i,u_j> = 1 when i=j and 0 otherwise,
    ||u_j|| <= sqrt(d),     ||a_j|| <= sqrt(2).

The distance of a_j to the span of the other basis rows is 1/||u_j||. Its
relative distance is therefore at least

    1/(||a_j|| ||u_j||) >= 1/sqrt(2d).                      (3)

Every independent subset extends to a full basis when the row span is the
whole space. Removing some of the comparison rows can only increase distance
to their span. Hence (3) is a GLOBAL delta-distance property of the row set,
not merely a property of bases seen during one route or of feasible bases.

For completeness, the cone-width step can also be seen directly. Put c=sum a_i.
For any w with ||w||<=1/sqrt(d), the expansion

    c+w = sum_i (1+<w,u_i>) a_i

has nonnegative coefficients by Cauchy--Schwarz. Thus the radius1/sqrt(d) ball
about c is in the positive cone of the basis. Since ||c||<=sqrt(2)d and c is
nonzero, normalizing c yields a unit-centered ball of radius at least

    tau = 1/(sqrt(2)*d^(3/2)).                              (4)

At a nonsimple vertex, choose any independent active basis. Its cone lies in
the full vertex normal cone, so the same width lower bound holds. No assumption
that all vertices are simple is used.

**External theorem actually used.** Dadush and Haehnle, *On the Shadow Simplex
Method for Curved Polyhedra*, arXiv:1412.6705, Theorem3 / Theorem11, prove that an
h-dimensional pointed full-dimensional polyhedron with tau-wide normal cones
has ordinary graph diameter at most

    (8h/tau)*(1+ln(1/tau)).                                (5)

The result includes unbounded pointed polyhedra and does not require simplicity.
The computational efficiency of their sampler/pivot implementation has additional
qualifications in the degenerate case; existence of a short edge path does not.
Their Lemma5 gives the equivalent delta/h cone width implication and Lemma30
records the inverse-column interpretation of delta. We use their published
result, not a new unsupported shadow-walk assertion.

Substitution of (4) into (5) gives

    8sqrt(2)*h^(5/2) * (1 + (ln2)/2 + (3ln h)/2).            (6)

For h>=1, ln h=2ln(sqrt(h)) <=2(sqrt(h)-1), ln2<=1, and sqrt(2)<=3/2.
The parenthesis in (6) is at most3sqrt(h). Therefore

    ordinary-edge diameter <= 36h^3.                       (7)

This constant is intentionally conservative. Formula (6), of order
h^(5/2) log(h+1), is the sharper consequence. The point case h=0 has cost zero.
A safe explicit polynomial is more convenient for the repository's natural-number
route budgets; no optimal constant or new best bound for this class is claimed.

The analytic theorem (5) is not yet a formalized import in this workspace. The
new Lean candidates prove signed-path, inverse-normalization, dual-frame cone,
and route-accounting cores. They do not silently introduce (5) as an axiom or
claim that a compiled arithmetic adapter constitutes the entire theorem (7).

## 3. Exact hereditary face models, not an ambient metric assumption

Let x,y be the actual endpoint vertices. Collect ALL original rows tight at
both. These define the smallest common face. Use x as an affine origin. Its
homogeneous equality system has the component representation (2).

Pinned components have no free variable. On each unpinned balanced component C,
write

    z_i = x_i + sigma_i * t_C,     sigma_i in {+1,-1}.

This maps onto the full equality solution space, not merely into a convenient
subspace. Substituting into every original inequality gives its exact restriction.
A row between different free components still has two unit coefficients. A row
inside one component becomes zero or ±2 times its variable. A row with only one
free endpoint has coefficient ±1. Positive rescaling of a unary ±2 row restores
unit magnitude. Thus the class is closed under taking the actual common face.

Every nonconstant restricted inequality is strict at the endpoint midpoint:
if it were tight there, linearity and nonnegative endpoint slacks would make it
tight at both endpoints, hence already one of the defining common equalities.
So the quotient is full dimensional in exactly h free coordinates. The endpoint
vertices remain vertices, giving full row rank and pointedness. Applying (7)
in THIS affine coordinate model yields an ordinary-edge route inside the same
common face. Affine coordinates need not preserve Euclidean conditioning; the
condition estimate is reapplied after constructing the signed intrinsic model.
Affine maps preserve the face graph, which is all the diameter claim requires.

The code discovers this quotient from the endpoints, including odd-cycle-pinned
components, and binds every restricted row to its original row. It does not
replace the original polyhedron by a relaxation. A test pins an entire odd-cycle
component and leaves a one-dimensional carrier; another turns a same-component
binary row into a coefficient-two unary row.

## 4. Recognition beyond ordinary network balance

For input rows with at most two nonzero rational coefficients, solve the positive
coordinate scaling equations

    s_j/s_i = |A_ri|/|A_rj|

along each support edge, and verify every cycle. When consistent, x_i=s_i*z_i
followed by positive row rescaling makes all nonzero coefficients ±1. Signs are
NOT discarded in the polyhedral model. They remain signed graph relations, and
negative cycle products are permitted.

This is an exact necessary and sufficient recognizer for these positive-diagonal
and row-scaled unit-magnitude descriptions. It accepts same-sign constraints,
sign-unbalanced graphs, single-coordinate rows and zero rows. It does not claim
to recognize an unknown dense affine change of coordinates or all two-variable
systems. Four shuffled, rationally rescaled signed examples check that the
transformation is recovered without being supplied.

The distinction from arbitrary positive gains is sharp even for very small
imbalances. Consider the two rows

    [1,-1], [-(1+epsilon),1].

Their determinant has magnitude epsilon and some inverse entries have magnitude
at least1/epsilon. With epsilon=2^-80, the coefficients are extremely close to
balanced, but the half-integral inverse property fails dramatically. The exact
recognizer rejects that unbalanced absolute cycle. This is a conditioning and
recognition counterexample, NOT evidence of large graph diameter: adding x_1<=1
gives a small bounded triangle.

A February2026 primary paper, Dadush--Kober--Koh, *On Circuit Diameter and
Straight Line Complexity*, arXiv:2602.05699, derives a strongly polynomial
CIRCUIT diameter bound for general two-variables-per-inequality systems. That
result does not justify an ordinary-edge claim for general gains. Our use of
(5) is what supplies the edge theorem for the narrower, exactly recognized class.

## 5. The implemented shadow route and symbolic degeneracy handling

The input consists of original A,b and the two requested vertex coordinates.
No full vertex set, edge-direction dictionary, Minkowski sum, strict point,
or boundedness witness is required. Vertex rank is checked by the signed-kernel
model. The actual common-face quotient is formed as above.

The routine uses independent active row bases at the endpoints and objectives
that are positive combinations of those bases. It follows the parametric
objective c(t)=(1-t)c_start+t*c_target. For a current basis B, solve

    lambda(t)=B^-T c(t).

While all lambda_i are nonnegative, that basis vertex maximizes the objective.
At the first zero multiplier with negative derivative, release that row and
move in -B^-1 e_i. An exact minimum-slack ratio chooses the entering constraint.
The algorithm uses the half-integral basis inverse constructor, not an ambient
vertex-graph search.

Nonsimple vertices require care. The routine conceptually uses RHS

    b_r(epsilon)=b_r+epsilon^(r+1),

but never substitutes a floating epsilon or changes a reported input inequality.
Each ratio is a sparse rational coefficient dictionary in epsilon, compared by
its first nonzero coefficient. Endpoint basis selection considers independent
subsets of the endpoint's active rows until it finds a symbolically feasible
basis, subject to an explicit cap. This is not whole-polytope vertex enumeration,
but it may still be exponential in a highly degenerate endpoint's active set.

All bases traversed are feasible for sufficiently small positive epsilon. Their
limits are feasible vertices of the ORIGINAL polyhedron because their original
basis equations have full rank. A basis exchange retains h-1 independent rows.
If its two limiting vertices coincide, it is recorded as a stationary pivot,
not charged as an edge. Otherwise, their shared original tight rows have rank
h-1, with leaving and entering endpoint blockers. The entire equality face is
therefore their segment, an ordinary edge. Common-face lifting preserves this
edge and all original endpoint-common facets.

The verifier independently checks the original feasibility of every endpoint,
all inverse identities, multiplier intervals, symbolic ratio comparisons,
basis replacements, blocker inequalities, original shared tight rank, reported
coordinates, and the requested final endpoint. Omitting a zero pivot is not
permitted in the basis chain even though zero pivots contribute no edge cost.

**Algorithmic boundary.** The recorded integer objective weights are seeded
finite genericity trials, not the exponential perturbation distribution used
in Dadush--Haehnle's expected-length proof. We do not claim a uniform polynomial
runtime or pivot bound for this PARTICULAR deterministic sampler. Genericity,
endpoint-basis and pivot caps return a failed search, not geometric nonexistence.
The successful certificates prove their actual edge counts; the separate
mathematical argument proves existence of a route bounded by (7). Both are
true, but they are not silently identified as the same algorithmic guarantee.

## 6. Exponentially many genuine directions in a sign-unbalanced example

Use d>=3 variables, their d lower bounds x_i>=0, and d upper inequalities

    x_0+x_1<=1, x_1+x_2<=1, x_2+x_0<=1,
    x_0+x_i<=1 for i=3,...,d-1.

There are exactly2d genuine facets. Strict interior is obtained by taking all
coordinates1/4. Each lower and upper row has an independently available relative
interior; no row is being counted just as a redundant description artifact.
The system is bounded because nonnegativity and incident pair bounds bound
every coordinate by1. Its upper signed graph contains an odd triangle.

Let u=e_0. For every subset S of {3,...,d-1}, put

    v_S=(1/2,1/2,1/2, (1/2)*1_S).

The common tight rows are x_0+x_1=1, x_0+x_2=1 and, for each leaf, its upper row
when in S or its lower row when outside S. These d-1 rows have independent
normals. Their homogeneous kernel is one signed component. The additional
source lower row x_1=0 and target upper row x_1+x_2=1 bound opposite endpoints.
Thus [u,v_S] is an ordinary edge for EVERY S.

Its direction is proportional to (-1,1,1,1_S). Distinct S cannot give parallel
lines because the first coordinate fixes the scale. There are at least

    2^(d-3)

genuine edge directions with only2d inequalities, and the signed graph cannot
be switched to a balanced difference graph. In dimension64 that is128 rows
and at least2^61=2,305,843,009,213,693,952 directions. The test certifies selected
such edges without enumerating them. This is a limitation of polynomial-size
COMPLETE direction dictionaries, not a hard diameter example. It also separates
the new signed condition from merely reusing an ordinary network star.

## 7. Actual selected-carrier aggregation

The verified full-availability certificate from #206/#209 fixes actual portal
pairs before asking for routes and satisfies sum h_i<=3e, where e=n-d. Suppose
each of those actual carriers has an exact affine signed-unit model. Applying
(7) inside the model supplies an ordinary parent-edge route of cost<=36h_i^3.
If h_i<=H, then

    sum cost_i <=36H^2 sum h_i <=108H^2 e.

The SAME certificate assembles a route of cost

    D+108H^2 e;    at D=1,H=d:  1+108d^2(n-d).               (8)

This is a cubic sufficient carrier regime, not a bound for arbitrary carriers.
The basis-angle theorem does not automatically supply a signed representation
of an unrelated H-face. The new Lean aggregation module consumes actual routes
and their numerical costs; it does not assume that (5) has already been proved
in Lean or that generic labels are geometric models.

## 8. Executed evidence and formalization boundary

The exact tests cover2,660 signed row subsets in dimensions1--4 and1,213
nonsingular bases,429 of which have half-integral inverse entries. All component
ranks and inverse matrices agree with independent Gaussian elimination. The
squared relative-distance bound is checked on every basis row. The64-dimensional
2^32 determinant specimen is checked separately.

Small independent H-basis enumeration builds seven polyhedra including odd-cycle
fractional stable-set systems, a coupled rotated-box system, an implicit-equality
line, a genuinely unbounded strip and duplicate rows. It computes complete
vertex lists and graphs independently before comparing every generated route.
The receipt records exact totals rather than inferring them from a supplied
candidate list. Larger cases do not enumerate their ambient graphs.

Representative executed routes:

- A24D,300-row signed odd-tree system with dense additional cuts:49 ordinary
  edges and one stationary basis pivot;40 visited bases use half entries.
- A48D,119-row coupled rotated-block model:60 ordinary edges and12 stationary
  pivots. The model is not treated as a Minkowski sum or a direction list.
- Four positive diagonal rescalings and row permutations recover the signed
  representation automatically.
- An odd-cycle-pinned actual face has intrinsic dimension one.

The full receipt includes all source hashes, small-instance counts, large
certificates and16 rejected inputs in
`SIGNED_BASIS_CHECK_2026-09-12.json`. Rejections include false pivots,
unsupported gain cycles, dense rows, changed endpoints, a diagonal offered as
an edge, invalid dual weights, and exhausted computational budgets.

Two new Lean modules contain signed-path transport, odd-cycle pinning,
inverse-column normalization, dual-frame ball and separation facts, and the
selected-carrier aggregate. They are UNCOMPILED candidates. The all-basis
component extraction, full analytic normal-width theorem, symbolic-shadow
algorithm and coordinate quotient are mathematical arguments / exact executable
certificates, not all complete new Lean declarations. No local or hosted Lean
acceptance, new platform child, or Prove2Me status mutation is claimed.

## Primary references

Daniel Dadush and Nicolai Haehnle, On the Shadow Simplex Method for Curved
Polyhedra, arXiv:1412.6705, especially Theorem3 /11 and Lemmas5 and30.
Primary full text read: https://arxiv.org/html/1412.6705
Conference source: https://doi.org/10.4230/LIPIcs.SOCG.2015.345

Daniel Dadush, Stefan Kober and Zhuan Khye Koh, On Circuit Diameter and Straight
Line Complexity, arXiv:2602.05699, February2026. This result concerns CIRCUITS for
general two-variable inequalities, not an ordinary-edge bound for arbitrary gains.
Primary full text read: https://arxiv.org/html/2602.05699

The next structural question is how to control conditioning or an alternative
row-retirement potential when absolute gain cycles are inconsistent. Merely
being numerically close to a balanced system cannot justify the inverse bound.
The current contribution supplies a rigorous intermediate class with arbitrary
sign cycles and exact original-edge certificates, without claiming that the
remaining general gain problem has been solved.

## Final executed totals

The final run verifies 533 route certificates and 1,098 actual ordinary-edge
occurrences across the small, additional, and explicit odd-star suites. There
are 73 stationary symbolic pivots; they are not charged as edges. Independent
small original-H enumeration gives 59 vertices, 136 edges and 831 ordered graph
distances across seven models, including a genuinely unbounded signed strip.
The graph-kernel audit checks 2,660 row subsets and all 1,213 nonsingular bases
among them; 429 bases use half-integral inverse entries. Sixteen malformed or
forged cases are rejected. All figures are execution evidence for these finite
inputs, not a universal runtime bound or a new Lean verdict.
