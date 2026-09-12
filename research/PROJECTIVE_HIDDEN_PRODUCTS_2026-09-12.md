# Beyond #202: projectively hidden products at large support deficit

## Scope and dependency boundary

The user assigned PR #202's Lean repair, verification, and publication to another
agent and asked for further mathematics. This continuation leaves #201 and #202
unchanged. It works from the existing affine row-block and graph interfaces on
main `65dc76dd2a2e9cc01a3e0ae3f64464d4eebfbdd3`, not from a new open child.

**Status:** complete mathematical argument and 450 lines of new Lean proof
candidates; the new modules have NOT been compiled or accepted by Prove2Me.
Exact rational tests were actually executed; their receipt is separate.

This is an extension of the repository's sufficient routing criteria, not a
claim that projective invariance is a new classical theorem. The point is to
avoid mistaking coupling of a particular H-presentation for geometric routing
hardness. We give both a positive, checkable routing criterion and an unbounded
family that defeats the conjunction of small-deficit and affine-factor tests.

## 1. A stronger stress test than an ordinary cube

For d >= 2, choose c in R^d with every c_j > 0 and set

    Q_c = { y : y_i >= 0 and y_i + c dot y <= 1 for all i }.

There are 2d irredundant facets. Define

    f_c(x) = x / (1 + c dot x),
    g_c(y) = y / (1 - c dot y).

For P=[0,1]^d, both maps are well-defined on the respective polytopes:

    1 + c dot x >= 1 on P,
    1 - c dot y >= 1/(1 + sum_j c_j) on Q_c.

For the second assertion multiply the i-th upper inequality by
c_i/(1+sum c_j) and sum. This gives c dot y <= sum c_j/(1+sum c_j).
The maps are inverse and f_c(P)=Q_c, as can also be checked inequality by
inequality. Section 2 proves that they preserve vertices and ordinary edges.
Thus the graph of Q_c is the d-cube graph and its diameter is exactly d.
Explicit routes are obtained by flipping differing binary coordinates and
mapping each intermediate vertex through f_c.

### Why affine row blocks cannot see it

The lower normals are -e_1,...,-e_d, a basis. Each upper normal e_i+c has a
nonzero coefficient in EVERY one of these basis directions. Consequently the
row-normal vector matroid has a single connected component.

Here is a basis-independent argument rather than merely an observed detector
failure. Suppose the normals could be partitioned into two nonempty groups
with complementary linear spans. The basis normals -e_j are distributed among
those spans. The direct-sum decomposition of an upper normal is its unique
expansion in this basis. Since every coefficient is nonzero, whichever span
contains that upper normal must contain all basis directions. The other span
would then be zero, contradicting its nonzero row. The same argument rules
out any nontrivial direct-sum factorization of the normals. Therefore Q_c is
not affinely equivalent to a nontrivial Cartesian product.

It is nevertheless COMBINATORIALLY a product, and projectively a product. Do
not call it combinatorially indecomposable or an actual hard-diameter example.

### Why the shortest-repair support deficit remains large

At target 0, precisely the d upper rows are target-slack. Every upper row face
contains the same opposite vertex

    w = (1,...,1)/(1+sum_j c_j).

Their parent-vertex intersection labels form a clique. A chordless mixed path
can use at most two of these labels: among three, the first and last form a
nonconsecutive chord. Hence EVERY shortest repair certificate in the current
construction has r <= 2 and

    g = (n-d)-r = d-r >= d-2.

Thus both g and the largest AFFINE row-block excess grow arbitrarily large,
even though diameter is d. Adding "normal matroid connected" to the residual
branch does not remove cube-like easy geometry. The correct notion must at
least allow projective changes of chart, or use more combinatorial information.

## 2. Projective graph transport with no hidden geometric assumptions

Work in a real vector space and let l be linear. Write

    D(x) = 1+l(x),  U = {x : D(x)>0},  f(x) = x/D(x).

The opposite chart is f_{-l}(y)=y/(1-l(y)). Direct substitution gives

    1-l(f(x)) = 1/D(x),
    f_{-l}(f(x)) = x                 whenever D(x) != 0.

Therefore f is injective on U and carries U into U_{-l}. U is convex.
For x,y in U, a,b >= 0, a+b=1, and z=ax+by, we have

    D(z) = aD(x)+bD(y) > 0,
    f(z) = [aD(x)/D(z)] f(x) + [bD(y)/D(z)] f(y).

The new coefficients are nonnegative and sum to one; they are both strictly
positive when a,b are. Applying the same calculation to the inverse proves

    f([x,y]) = [f(x),f(y)],
    f((x,y)) = (f(x),f(y)).

The notation for the open segment agrees with Mathlib's definition, including
the coincident-endpoint case. No claim of affine preservation of the original
segment parameter is made; the explicit coefficient reweighting is essential.

For any P contained in U and C contained in U, the two segment identities and
injectivity imply

    IsExtreme(f(P),f(C)) iff IsExtreme(P,C).

To see the nontrivial direction, pull an open-segment witness back using the
open-segment image identity. Convexity keeps its preimage in U, where
injectivity identifies it with the original witness. Apply the extreme-set
property and map the endpoint back. Singletons give vertex preservation;
closed segments give ordinary edge preservation. Mapping every point of a
padded edge walk therefore preserves its exact budget.

Importantly, the map need NOT be globally injective: the total Lean definition
uses inverse-zero convention outside U, but the proof never reasons there.
A positive chart is not an arbitrary projection or circuit map.

## 3. A row-level certificate instead of an exponential vertex table

Let the SOURCE presentation be

    P = {x : a_i dot x <= b_i}.

For a candidate c, form the TARGET rows

    a'_i = a_i + b_i c.

Then the exact slack identity is

    b_i - a'_i dot f_c(x) = (b_i - a_i dot x)/(1+c dot x).    (1)

Assume source positivity 1+c dot x>0 on P and target positivity
1-c dot y>0 on Q={y : a'_i dot y<=b_i}. Equation (1), applied also to the
inverse, proves f_c(P)=Q. Graph transport proves DiamLE(Q,B) whenever
DiamLE(P,B). It transports a proved graph bound; it does not assume the
conclusion as a new graph-isomorphism hypothesis.

Both positivity premises admit finite rational certificates. Supply
nonnegative weights mu,nu such that

    sum_i mu_i a_i = -c,   sum_i mu_i b_i < 1,
    sum_i nu_i a'_i = c,   sum_i nu_i b_i < 1.

Summing valid inequalities yields lower denominator margins
1-sum mu_i b_i and 1-sum nu_i b_i, respectively. These are SUFFICIENT
certificates; failure to supply one is not evidence that a chart is invalid
or that the polytope is hard.

For the cube family with c positive, use mu on the lower rows equal to c_i,
and nu on the upper rows equal to c_i/(1+sum c_j). No numerical LP solver
or approximate zero decision is needed.

### Hidden-product routing theorem

Suppose unshearing the input rows a'_i-b_i c gives the existing certified
independent factors with dimension h_j, row count m_j and

    h_j <= m_j <= h_j+3.

The established small-excess theorem gives each factor diameter <=m_j-h_j.
The existing product theorem sums them to n-d. The new positive-projective
transport preserves this exact bound:

    DiamLE(Q,n-d).

There is no restriction on total excess, number of factors, or support deficit.
The source need not be a cube: projective images of arbitrary products of
bounded excess-at-most-three factors qualify. The CLI checks the source's
boundedness/nonemptiness using the existing full-rank, positive-balance and
feasible-point certificates.

The new criterion is a certified preprocessing step, not a theorem that a
suitable c can always be found. General chart discovery is NOT implemented.
An affine translation/change of coordinates may be applied separately using
the existing affine transport, so charts fixing the origin are a useful
normal form rather than a claim covering every projective map verbatim.

## 4. Connection to actual carrier costs

Use the criterion on the actual portal-pair common-face coordinate model,
after a verified equivalent irredundant presentation is chosen. If this model
is a certified projective image of small independent blocks, its local
ordinary-edge budget is the sum of source block excesses. The existing affine
coordinate lift and extreme-face routing lemma then give the requested parent
route for that SAME portal pair. Feed that route to DeferredClipCertificate's
existing callback. Do not switch portal pairs or charge unused pairs.

For the Q_c family, every common face is the projective image of a cube face;
its portal distance is the number of differing free binary coordinates.
The complete parent already has a direct d-edge bound, so recursive splitting
is unnecessary for this stress test.

This does not provide a uniform bound on the sum for arbitrary coupled
carriers. It removes a representation-dependent false obstruction and enlarges
the rigorously routable large-deficit class. It does NOT assert arbitrary
normal-connected carriers have large diameter, or that all combinatorial cubes
are projectively equivalent to the standard cube.

## 5. Files and verification handoff

- `PolynomialSegmentChartTransport.lean`: segment-chart extreme sets, vertices,
  ordinary adjacency, and padded graph diameter transport.
- `PolynomialPositivePerspective.lean`: inverse formulas, explicit segment
  reweighting, positive-domain chart, and edge-diameter transport.
- `PolynomialProjectiveRowBlockRouting.lean`: exact H-row shear/slack identities,
  denominator multiplier certificates, and hidden-small-block routing.
- `projective_row_block_certificate.py`: exact rational certificate generation
  and independent checking, reusing `scripts/row_block_certificate.py`.
- `test_projective_row_blocks.py`: reproducible positive and negative controls.

The new CLI deliberately does not drop rows. Existing redundancy certificates
must NOT be copied blindly across a shear when their RHS combination is a
strict inequality. Do equivalent normalization separately, or re-certify it.

Executed checks: 30 base certificates, 16 nonorthogonal rational coordinate
changes, 24 normal-connected examples, 252 mapped vertices, 10 independent
active-set vertex enumerations, 642 exact adjacency edges, 10,920 graph-pair
distances, 1,260 segment-reweighting identities, and 9 negative controls.
Corruption of a denominator certificate, omitted coupling, changed chart,
invalid inverse, duplicate rows, floats and an infinity-crossing chart are
rejected. A genuinely coupled truncated-cube source remains UNRESOLVED by the
small-block criterion; the checker does not turn a failed factor test into a
spurious bound. These finite checks do not verify the universal Lean source.

Commands in the repository:

    python3 scripts/test_projective_row_blocks.py
    python3 scripts/projective_row_block_certificate.py research/projective_cube_4d_input.json
    lake build Solutions.PolynomialSegmentChartTransport \
      Solutions.PolynomialPositivePerspective Solutions.PolynomialProjectiveRowBlockRouting

Fix ordinary elaboration errors locally. Inspect the transitive axioms of ALL
new declarations, with the classical small-excess result an explicit input.
No new workflow, dependency pin, platform submission or credential operation
was made. Local proof compilation and platform acceptance remain distinct.

## 6. Next substantive mathematical target

Move the coupling test to homogeneous facet data (a_i,b_i), not merely the
affine normals a_i. For this chart, inverse normalization is the exact rank-one
update a'_i-b_i c. A useful next constructive theorem would recognize a c and
small independent factors from a polynomial-size homogeneous certificate,
or certify a genuinely coupled residual after these chart changes are allowed.
The present work already verifies any proposed c without listing all vertices.

Even such recognition would not solve the remaining arbitrary-carrier routing
problem. Joint-cost bounds must also handle polytopes outside the projective
product class. Do not create an open platform child asserting universal
projective factorization; it is not justified.

### Classical context, not imported as an axiom

Gouveia, Macchia, Thomas and Wiebe, *The Slack Realization Space of a Polytope*,
SIAM J. Discrete Math. 33(3), 2019, arXiv:1708.04739v4, Section 2, treats
projective equivalence and positive slack scaling. Our row identity (1) is a
special explicit chart instance. The repository contribution is the direct
ordinary-edge transport and checkable hidden-product criterion, not discovery
of projective invariance itself.

Primary source: https://arxiv.org/html/1708.04739v4
