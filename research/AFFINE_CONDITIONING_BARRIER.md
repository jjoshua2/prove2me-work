# An exact affine-conditioning obstruction, and a positive gain-balancing test

## 1. Status and conjecture-facing point

Baseline: `338d1f9e1cc20df86998efa5f0dc6e92916329e8` in
`jjoshua2/prove2me-work`. PR #275 follows #274's signed-normal work. The new
81-line scalar theorem passed the FIRST prepared Lean compilation and axiom
check at proof SHA `ff9b0743f31b0db6adbcd078a2447180f0a8f7d4`, run
`35052375246`. All three compile exits are zero and the three printed
declarations use only `propext`, `Classical.choice`, `Quot.sound`.

The separate trusted publisher stopped with `Platform skill version changed;
refresh the skill before publishing.` No authenticated ACCEPTED/Proved verdict
or publication receipt was produced. The guard is NOT bypassed. This is a
compiled/audited scalar result and written geometric corollaries, not a new
Prove2Me-accepted polytope theorem. The scalar source has not been edited after
its first successful gate. The mathematical explanation below does not inherit
platform acceptance from any earlier packet.

A tempting extension of #274 would seek an affine chart making every original
feasible normal basis quantitatively well separated, then apply a known
conditioning-based diameter theorem. The construction here proves that there
is NO positive lower bound depending only on dimension and genuine facet count
for that particular best-chart distance parameter. It does so on bounded
simple polytopes whose actual graph diameters are linear. A one-vertex coupling
cut also gives nonproduct examples. Bad conditioning is not a graph-distance
lower bound and does not refute Polynomial Hirsch.

The positive companion recognizes exactly when arbitrary magnitudes in rows
with at most two nonzero coefficients can be removed by a positive diagonal
change and positive row rescalings. This extends access to the previous
signed-root arguments in a checkable way, rather than assuming a hidden chart.
Its cycle obstruction excludes only diagonal balancing. It must not be confused
with the independent ALL-affine obstruction proved by the four-ray identity.

## 2. The distance parameter and what affine changes mean

For linearly independent normals a_1,...,a_d define their relative distance
parameter as the minimum of

    dist(a_i, span{a_j:j != i}) / ||a_i||.

The local delta-distance property asks for the same bound at every feasible
basis; the global property asks for every independent row subset. These are
Dadush--Haehnle's definitions, not introduced here. Positive row rescaling does
not change either relative distance. An invertible affine change of primal
coordinates transforms all normals by one invertible linear map; translations
change only right sides. Thus a claim uniform over all positive-definite Gram
matrices of a normal pair covers every affine chart, including dense mixing.

This parameter is stronger than some normal-cone width assumptions. In
particular the cited paper explains that small delta need not imply a narrow
normal cone. We DO NOT claim to refute all possible fan-width, projective,
new-realization or route-local conditioning arguments.

## 3. Exact two-pair metric theorem (the Lean target)

Let 0<e<1, and let a,b be linearly independent in any real Euclidean space.
Set X=||a||^2, Y=||b||^2, Z=<a,b> and D=XY-Z^2>0. The squared sines of the pairs
(a,a+e*b) and (b,b+e*a) are

    s1^2=e^2 D/[X(X+2eZ+e^2Y)],
    s2^2=e^2 D/[Y(Y+2eZ+e^2X)].

The denominators are positive, since

    X(X+2eZ+e^2Y)=(X+eZ)^2+e^2D.

If X>=Y, then

    X(X+2eZ+e^2Y)-D
       =(Z+eX)^2+(1-e^2)X(X-Y)>=0.

Therefore s1^2<=e^2. If Y>=X use the symmetric identity. This proves the
upper bound on min(s1,s2) for EVERY metric, not a search over finitely many
charts. For X=Y=1, Z=-e both squared sines are exactly e^2. That matrix is
positive definite and is the Gram matrix of some real independent a,b.
Consequently the best possible minimum of the two relative separations is
EXACTLY e. The proof does not require a rational square root realization of
the attaining metric.

The public scalar theorem `Hirsch.affine_pair_conditioning_optimum` states the
universal inequality and an attaining positive-definite witness. Euclidean
interpretation, feasible-facet realization and graph facts are proved in this
note, not silently included in the scalar Lean statement.

## 4. Genuine bounded simple polytopes realize the bad pairs

For 0<e<=1/2 take

    O_e={|x|<=1, |y|<=1,
         |x+e*y|<=1+e/2, |e*x+y|<=1+e/2}.

Let t=(1+e/2)/(1+e). The eight cyclic vertices are

    (1,-1), (1,1/2), (t,t), (1/2,1),
    (-1,1), (-1,-1/2), (-t,-t), (-1/2,-1).

Put the facet normals in the cyclic order

    (1,0),(1,e),(e,1),(0,1),
    (-1,0),(-1,-e),(-e,-1),(0,-1).

Each vertex has exactly its two adjacent rows tight and satisfies all others
strictly. The midpoint of each adjacent-vertex segment is a strict
relative-interior witness for its original facet. Thus every listed row is a
genuine facet, every vertex is simple, and the graph is the eight-cycle with
diameter four. Completeness follows from intersection of the eight displayed
halfplanes in their cyclic supporting order; small tests additionally enumerate
all square active systems independently.

The two bad pairs are not arbitrary unused rows: (1,0),(1,e) meet at (1,1/2),
and (e,1),(0,1) meet at (1/2,1). After ANY affine change they still form feasible
bases. Section 3 gives local delta<=e in every chart.

For the metric [[1,-e],[-e,1]], the six pairs of the four unoriented normal
lines have squared sines among e^2, 1-e^2 and 1. Because e<=1/2 their minimum
is e^2. Therefore both best local and best global delta are exactly e, not
merely bounded above by an arbitrarily small number.

For d>=2, form P_(e,d)=O_e times [-1,1]^(d-2). It has 2d+4 genuine facets and
2^(d+1) vertices. Product graph edges change exactly one factor, so distances
are the octagon cyclic distance plus the cube Hamming distance. Diameter=d+2.
The above two bad pairs extend to feasible d-row bases by adding cube rows.
Distance to the span of all other basis rows is no greater than distance to
one paired row. Thus local delta<=e after EVERY invertible d-dimensional affine
map. The block metric [[1,-e],[-e,1]] plus the identity on other coordinates
attains e, for local and global properties.

At fixed d and fixed m=2d+4, e can be arbitrarily small. Hence even an
arbitrary positive f(d,m), much less an inverse polynomial, cannot be a universal
best-affine-chart delta lower bound. All old facets are genuine, so pruning
redundancies cannot evade this example. It does not prevent replacing this
realization by a different combinatorially equivalent one.

## 5. A coupling cut removes the Cartesian-product explanation

Let w=((1,-1),-1,...,-1) in the product, and use the exposing functional

    f(x)=x_1-x_2-sum_(j>=3) x_j.

Its value at w is d. Every other product vertex has deficit at least 3/2:
the two adjacent octagon vertices have deficit3/2, and a cube flip has deficit2.
Thus f<=d-1/4 truncates ONLY w and leaves every other vertex strictly feasible.
It replaces w by d new points, one on each incident old edge, at the exact
fraction (1/4)/(f(w)-f(neighbor)) of that edge. The new facet is a simplex.
The other original facets remain genuine, as certified by their unchanged
interior witnesses; the average of the new points witnesses the new facet.

Call the truncated polytope Q_(e,d). It is simple, has 2d+5 genuine facets, and
has 2^(d+1)+d-1 vertices. For d>=3 it is not combinatorially a nontrivial
Cartesian product. Indeed a simplex facet in a positive-dimensional product
can occur only when one factor is a segment and the other is a simplex: every
face of a product is a product of faces, and a nontrivial product is not a
simplex. Such a prism has d+2 facets, unlike Q_(e,d). This is Cartesian-product
indecomposability only; Minkowski or projective indecomposability is not asserted.

The feasible vertices carrying the two bad normal pairs are not cut. Therefore
EVERY affine chart of Q_(e,d) still has local delta<=e. We do not assert that
the attaining product metric gives equality for this extra-row system.

Any old shortest route is transported through the truncation by replacing an
occurrence neighborA-w-neighborB by three edges through two ports on the new
simplex facet. This adds at most one step. For a new endpoint, use the old route
from w, switching once on the new simplex if its port differs from the desired
exit. Two new endpoints are adjacent. Thus

    diam(Q_(e,d))<=diam(P_(e,d))+1=d+3.

The tested pair starts at the new port toward octagon vertex1 and ends at
opposite octagon vertex4 with all cube coordinates+1. Following that direction
uses d+2 edges. Collapsing every new port to w sends each new edge to an old
edge or a stay, so old product distance d+2 supplies a matching lower bound.
Both tested endpoints share NO original facet. In dimension32 there are69
genuine facets, a SHORTEST34-edge selected path, and a35 all-pairs upper bound,
while e=2^-160 bounds best affine local delta. The whole graph is not enumerated.

## 6. Exact recognition of the positive diagonal-balancing case

Suppose each nonzero original row has one or two nonzero coefficients. Seek
positive scalars s_i and positive row weights w_r such that every nonzero
coefficient of w_r*a_r*diag(s) is +1 or -1. On a pair row r with support{i,j}
this is equivalent to

    s_j=(|a_ri|/|a_rj|)*s_i.

View that positive rational ratio as the gain on oriented edge i->j. Such
scales exist iff the product of gains along EVERY closed walk is one. Necessity
is telescoping. For sufficiency choose a spanning forest, set one scale per
component to1 and propagate along the tree. The non-tree consistency equalities
are exactly the fundamental-cycle conditions, so every edge then holds.
Normalize each row by w_r=1/(|a_ri|s_i). Unary rows impose no cycle condition.

The producer returns either those scalars or an actual row-labeled closed walk
whose gain product differs from one. The independent consumer multiplies the
original coefficients and checks either all row identities or that closed
walk. It runs no graph search, LP, numerical logarithm or tolerance check. The
arithmetic operations and bit growth are polynomial in the explicit rational
row system. Signs do not affect magnitude balancing. A failed cycle proves
ONLY that a positive diagonal chart with the SAME coordinate supports does
not exist; a dense affine map can change support and is not excluded by it.

For a positive certificate, x=diag(s)*y and positive row scaling give an exact
polytope isomorphism. Original edges and graph distance are preserved. Hence
the existing signed-root angle theorem from #274, and its explicitly attributed
Dadush--Haehnle diameter specialization, apply without imposing a small RHS
alphabet. The old unit-box coordinate-level executable has narrower input
requirements; we do not claim to have run it on arbitrary reparameterized
boxes merely from this recognition result.

Tests include diagonal scale ratios2^140 and2^620. Both recognized examples
are deformed coordinate presentations of an ordered-cube simplex, with a
separately checked single original edge from0 to the all-upper endpoint.
These show true positive recovery despite huge numerical scales. They are
not claimed as hard new diameter examples or new simplex algorithms.

## 7. Executed evidence and honest boundaries

The metric tests use600 rational independent vector pairs and compare all1200
squared sine formulas with independent SymPy projection calculations. Five
attaining metrics include e=2^-160; every pair of distinct underlying normal
lines is checked in each attaining metric.

Five complete original product H-graphs in dimensions2,3,4 use699 square
active systems,72 vertices and112 edges. All700 distinct endpoint pairs are
checked:2048 returned edge occurrences match independently computed shortest
lengths. Three dense affine re-encodings preserve their original-row path
certificates. Large product paths in d16,32 have18,34 edges respectively, with
all36,68 genuine-facet anchors checked. A separate full3D truncated graph has
18 vertices and confirms the five-edge selected path; d16/32 coupled examples
check37/69 facet anchors and18/34 original edges without full graph enumeration.

The gain test matches an independent exact nullspace computation on256 systems:
161 balanced and95 inconsistent. The reference uses magnitude linear equations,
not the production gain-tree traversal. Eighteen malformed input/certificate
controls fail. The separate saved audit disables all constructors, gain
recognition, elimination and inverse discovery and checks7 product records,
3 coupled records,3 dense affine routes,8 gain records and2 balanced simplex
route records, totaling150 original edges.

These tests do not establish a new universal correctness theorem for Python or
JSON. The scalar Lean audit covers only its exact public type. Neither product
geometry, coupling-cut indecomposability, graph distances nor the gain-graph
algorithm is silently included in that audit. No negative graph-distance result
is inferred from a small angle or a failed balancing test.

## 8. Evidence lifecycle and next target

The first comment trigger is #275 comment5691648630. The bot resolved proof
SHA ff9b0743f31b0db6adbcd078a2447180f0a8f7d4 and run35052375246. The verifier
completed successfully. The downloaded artifact10429507451 has SHA256
`ae81fe723057ae61b2d140c3fbaced0e624db60b955e5fdf844cfb1f085248ae`; its complete
five-file manifest was recomputed and matches. Driver, solution and statement
compiled; the proof audit contains only standard logical axioms. The target
statement's deliberate placeholder is not an admission in solution.lean.

Publication failed at the trusted skill-version guard, before a usable receipt.
The version guard, publisher, credentials and allowlist are unchanged. No
second trigger was posted. Keep the PR draft until the supported skill refresh
and safe publication path are resolved; preserve the exact proof and check for
any existing registration before a future resume. There is no ACCEPTED or live
Proved claim for this packet. No historical root/leaf record was freshly polled.

The surviving general question is not whether every realization can be fixed
by a well-conditioned affine chart: this particular delta premise is false.
A route-local treatment of ill-conditioned regions, a different geometric
invariant, or a justified change of realization remains possible. None is
assumed here. The earlier obstruction to universal polynomial total-size
forward stellar flagification remains in force.

Primary source for conditioning definitions and sufficient shadow guarantees:
Dadush and Haehnle, *On the Shadow Simplex Method for Curved Polyhedra*,
arXiv:1412.6705v1, Definition4, Lemma5 and Theorems3/6. The paper explicitly
separates local/global distance properties from the weaker cone-width notion.
Classical gain consistency, product graphs and vertex truncation are used with
proofs above; no historical novelty or record-diameter claim is made.
