# Fixed detour slack cannot supply a uniform additive-spill theorem

## Status and principal result

This is a mathematical continuation of PR #208 at
`200682cdce2f68f99cde3042f4bd68b23e42ee5e`, not another proof of its conditional
recurrence. It adds files to that same active line; existing #208 sources and
#205/#206/#207 are unchanged. No workflow, pin or platform record is changed.
Two new Lean modules are **uncompiled candidates**. The complete infinite
polyhedral argument is written below; the generic transport and slack-certificate
cores, not the whole cyclic application, are expressed in Lean. Exact tests
are separately identified in the receipt.

For every fixed even dimension d>=4 and every fixed pair of nonnegative integers
(k,b), sufficiently large even n give an explicit simple rational d-polytope
and endpoint pair for which:

* every repair in #208's first-edge/available-facet family, with at most k extra
  region transitions, has total child intrinsic excess at least **2(n-d)**;
* a two-leg repair attains that lower bound, so it is the exact minimum;
* an explicit adaptive repair has n/2 ordinary edges and child excess n/2-1,
  hence **conserves** the parent excess when n is in the stated regime.

Thus **no fixed detour allowance k and fixed additive spill b can work uniformly
in this repair family**, even in one fixed dimension. This refutes the tentative
constant-k strengthening, NOT the existence of bounded-spill repairs with
input-dependent slack, NOT every cap/center/trace in the radial construction,
and NOT Polynomial Hirsch. It also does not make 2(n-d) a lower bound on actual
edge distance: it is a lower bound on the selected carriers' excess sum.

The family works in dimensions six, eight, ten and higher as well as four.
The concrete 8D, 40-facet example with k=4 has parent excess32, minimum child
mass64, and so fails b=2 (budget34). The explicit alternative has20 ordinary
edges and mass19. Its two-leg upper witness has child dimensions6 and2, so the
construction does encounter the dimension-at-least-six carrier regime.

## 1. A complete rational realization, not an assumed graph

Let d=2r be even, n>d, and set

    v_i=(i,i^2,...,i^d),  i=0,...,n-1;
    mu=(1/n) sum_i v_i;
    P(n,d)={x: (v_i-mu).x <= 1 for every i}.

The normal rows sum to zero and have rank d, so their all-ones positive balance
excludes every nonzero recession direction. The origin is strict, and P is
bounded and full-dimensional. Each original inequality is a genuine facet:
the nonnegative polynomial (t-i)^2 exposes v_i in the moment-curve hull, or,
equivalently, its normalized coefficients give a feasible polar point with
only row i tight. The standard face/polar correspondence justifies the facet
statement; the coordinate and sign argument below is also sufficient for
all vertex certificates used here.

For x, the slack polynomial is

    s_x(t)=1-(v_t-mu).x.

It has degree at most d, and the mean of s_x(i) over i=0,...,n-1 is exactly1.
A vertex has at least d independent active rows. A nonzero polynomial of degree
at most d has at most d distinct roots. Thus each vertex has exactly d tight
rows; the presentation is simple. Its active set K has size d.

### Facets/signatures are matchings on a cycle

The polynomial with these d roots is a nonzero multiple of
prod_{j in K}(t-j). Requiring one common nonnegative sign on ALL integer labels
forces the roots to come in adjacent pairs around the n-cycle:

    K is the union of r pairwise disjoint cycle edges.

For a positive leading coefficient the successive pairs (a1,a2),(a3,a4),...
must be consecutive integers, because the polynomial is negative between each
such pair. For a negative leading coefficient the outermost roots must be0
and n-1, and the intervening pairs (a2,a3),(a4,a5),... must be consecutive.
These are exactly the matchings that use the wrap edge {n-1,0}. Conversely each
ordinary consecutive-root factor (t-i)(t-i-1) is nonnegative at every integer;
the wrap factor t(t-(n-1)) is nonpositive on the label interval. Adjust the
single overall sign to get a nonnegative polynomial, zero exactly on K.

Write this polynomial as p_K(t)=sum_{j=0}^d c_j t^j and let

    a_K=(1/n) sum_i p_K(i)>0.

Then the vertex is explicitly

    x_K=-(c_1,...,c_d)/a_K,
    1-(v_i-mu).x_K=p_K(i)/a_K.                      (1)

No matrix inversion or other vertices are needed to construct x_K. Its active
rows have rank d: a null direction would give a degree-at-most-d polynomial
vanishing at all d roots and with zero mean. It would be a scalar multiple of
p_K, whose mean is positive, so the scalar and direction must be zero.

The number of such vertices is n/(n-r)*binomial(n-r,r), the number of r-edge
matchings on an n-cycle. This formula is used to refuse oversized complete
incidence enumerations, not to justify treating a partial vertex list as complete.

### Actual edges and carrier size

Two vertices sharing d-1 active rows have a common equality face of dimension
one, hence their segment is an ORDINARY edge. No circuit-length replacement
is used. General exact vertex/edge kernel certificates are the second Lean
module; numerical ranks are checked by rational elimination.

For signatures S,T let K=S intersect T. Their minimal common face has dimension
h=d-|K|. In a simple irredundant polytope, each row outside K that intersects this
face gives a distinct intrinsic facet of it. This follows locally at any common
vertex: active facets are independent, so adding one nonfixed row lowers face
dimension by one, and two different rows cannot give the same codimension-one
trace. Let U_K be the union of all vertex signatures containing K. Consequently

    minimum intrinsic row count M=|U_K|-|K|,
    carrier excess delta=M-h=|U_K|-d.              (2)

In particular delta<=e=n-d. These are true facet counts, not padded inherited
presentations or arbitrarily assigned mass tags.

## 2. The new geometric lemma: a free domino forces full excess

Let S be one endpoint signature, a matching of r cycle edges, and let K be the
common signature of the two endpoints. Suppose an edge of that matching is
disjoint from K. Remove it. The remaining (r-1)-edge matching covers K.

**Extension lemma.** Given any partial cycle matching with r-1 edges and any
requested row j, one can add one matching edge, with possible local rematching,
so that every previously covered row AND row j are covered.

Proof: if j is unmatched, start at j; otherwise start at any unmatched row.
Move clockwise until another unmatched row is reached. After the first free
row, any matched row must be paired with the next clockwise row: it cannot be
paired backwards, since the preceding row is either the initial free row or
already paired with its own predecessor. Thus the segment alternates unmatched
and matched edges and ends at another free row after an odd number of edges.
Flip the matching along this alternating path. Every old matched row remains
covered, and two free rows become covered. If j was initially covered it stays
covered; otherwise it is the first new row. There are at least n-d+2>2 free
rows before extension, so the traversal cannot run out of free endpoints.

Apply this for every row j. Each resulting d-row matching gives a vertex of
P by (1), contains K, and contains j. Therefore U_K consists of ALL n rows.
Equation (2) now proves

    a free matching edge disjoint from K => delta=e.        (3)

The implementation produces the alternating-path witnesses rather than
assuming this assertion from a lookup table. It also verifies them against
independently enumerated rational polytopes in small dimensions.

### Light transitions are metrically local

Call a transition light when delta<e, heavy when delta=e. By contraposition
of (3), every matching edge in either endpoint signature must touch K during
a light transition. Thus every new row is either retained or is adjacent on
the n-cycle to a retained row. In both directions,

    every row in S is at cycle distance <=1 from some row in T.             (4)

A heavy transition can make a long jump. But if the pair is routed inside an
actual proper facet it still retains at least one row: S intersect T is nonempty.
This weak retained-row condition is all that the lower-bound argument needs.

## 3. Far-separated signatures require two heavy transitions

A general finite transport lemma suffices. Suppose a chain of signatures has
L transitions. Light transitions satisfy (4), and every heavy transition has
nonempty endpoint intersection.

If there is no heavy transition, repeated application of (4) places a final
row within distance L of a source row. If there is exactly one heavy transition,
choose a row retained across it. Propagate this row backwards to the source
and forwards to the destination through the light transitions. The two lengths
sum to L-1. The metric triangle inequality gives a source/target row pair at
distance at most L-1. Therefore

    minimum distance between endpoint supports > L
        => at least two heavy transitions.                (5)

This does not identify the row-label metric with polytope graph distance.
It is a lower bound on the number of expensive carrier occurrences in a bounded-
length signature chain. The first new Lean module proves the abstract finite
metric/signature theorem and the resulting mass sum >=2*threshold. It permits
repeated labels and counts each occurrence separately.

## 4. Exact minimum 2e for every fixed detour allowance

Take n=2m and the two signatures

    S0={0,1,...,d-1},       ST={m,m+1,...,m+d-1}.

Assume m>d. Both are r-domino matchings. Their minimum cyclic label distance is

    gap=m-d+1.                                             (6)

Use exactly #208's repair family: take one original ordinary edge from the
source to w; then a walk through facets not containing the source; finish in
a facet containing the target; choose any shared vertex as each portal.

The available-facet graph is complete. Indeed, for any two distinct row labels
p,q, the nonnegative polynomial (t-p)^2(t-q)^2 has degree4<=d; normalized as in
(1), it gives a feasible point in the two row faces. Their bounded nonempty
intersection contains a vertex, so the two labels are adjacent.

The facet entered on the first edge cannot be a target facet in the separated
parameter regime: an ordinary edge is light and all its rows remain within one
cycle step of the source. Its region distance to a target facet is therefore1.
A walk with slack at most k has at most k+2 charged facet occurrences. Including
the initial original edge, its portal-signature chain has at most k+3 transitions.

If

    m >= k+d+3,                                             (7)

then gap>=k+4. By (5), every repair has at least two heavy transitions. The
initial original edge has excess1<e, so both heavy occurrences are charged
children. Thus

    total child excess >=2e.                               (8)

This remains true after optimizing ALL first-edge choices, allowed region
walks and overlap portals. It is not just a failure of a greedy policy.

### Matching upper certificate

There is always a two-leg geodesic repair achieving equality in (8). Choose

    W={n-1,0,1,...,d-2},
    Z={n-1,0} union {m,m+1,...,m+d-3}.

S0--W is an ordinary edge. Route W to Z in facet n-1 and Z to ST in facet m.
W intersect Z={n-1,0}, while Z intersect ST is the d-2-row target block.
Each common set leaves a free domino at an endpoint, so both child excesses
are exactly e by (3). Their dimensions are d-2 and2. The two region labels are
adjacent and the second contains ST, so this has zero extra region slack.
The lower bound (8) is therefore the exact optimum, not just a coarse estimate.

For any fixed k,b and any fixed even d>=4, choose m large enough to satisfy
(7) and e=2m-d>b. Then 2e>e+b. This proves that no uniform fixed pair (k,b)
can meet #208's local bounded-spill condition on this family.

The scope is deliberately narrow and precise. It does not rule out a different
cap/center/trace construction, variable slack, variable grouping, or a bounded-
spill selection theorem without a constant-slack restriction. The actual
diameters of cyclic polars are classical and polynomially bounded; they are
not new Hirsch counterexamples.

## 5. A constructive repair with growing slack and exact conservation

The positive answer is explicit. Slide the consecutive block one position at
a time:

    S_j={j,j+1,...,j+d-1},       j=0,...,m.

Each is a matching, and successive signatures share d-1 rows. Equation (1)
constructs their rational vertices directly. They form m ordinary edges.
After the first edge, charge transition S_j--S_(j+1) to row j+d-1 for
j=1,...,m-1. These are distinct available facets, and each pair really lies
in its assigned facet. Every charged carrier is the edge itself, of excess1.

Thus

    actual edge count=m=n/2,
    child excess sum=m-1 <= e=n-d,
    region slack=(m-1)-2=m-3.                              (9)

The dimension assumptions above imply m>d, so the conservation inequality holds.
This is a one-internal-node instance of #208's AdditiveRepair certificate with
b=2 (in fact the root needs no additive spill). The existing unmodified verifier
accepts these certificates in five fully enumerated cases.

Conversely, if a repair has mass<2e, it has at most one heavy transition. Equations
(5)--(6) imply k+3>=m-d+1, i.e.

    required slack >=m-d-2.                                (10)

Our explicit slack m-3 is within d-1 of that necessary lower bound. Therefore
for fixed dimension the required slack is **Theta(n)**, not merely unbounded.
This is a resource-certificate slack lower bound, not a lower bound on edge
length or on the complexity of finding some unrelated short route.

The generic near-geodesic contact cap (k+3)e becomes quadratic with growing k.
The constructed route does not pay that worst-case envelope: its ACTUAL carriers
are edges and their mass is directly m-1. Any extension that uses input-dependent
slack must likewise retain actual pair costs instead of substituting the loose
contact cap everywhere.

### Large exact certificates without enumerating the graph

The algorithm uses the root polynomial of each S_j and its average evaluation.
It checks all n original inequalities, active rank d and shared rank d-1 for
every returned vertex/edge. It does not need the full vertex list.

Among the executed examples:

* d8,n40,k4: fixed-slack minimum mass64, parent budget32+2, explicit20-edge route
  with mass19 and slack17.
* d12,n80,k20: fixed-slack minimum mass136, explicit40-edge route with mass39.
* d8,n200,k40: fixed-slack minimum mass384, explicit100-edge route with mass99;
  the full matching graph has60,843,250 vertices and is NOT enumerated.

No claim is made that these constructed routes are shortest for all displayed
parameters. The small fully enumerated tests independently compute endpoint
distances; the large tests certify only the stated ordinary-edge routes.

## 6. Executed tests and precise formalization boundary

The committed receipt records actual counts and SHA-256 hashes. The tests check
all1,066 partial matching supports in their stated small ranges and12,820
requested-row augmentations. There are15,521 carrier-pair checks, including
1,606 light transitions and387,718 explicit full-carrier row witnesses.

Independent rational active-basis enumeration checks2,124 bases,306 vertices,
and934 ordinary edges in four descriptions (dimensions4,6,8), agreeing with
both the matching criterion and the explicit polynomial coordinates. The old
#208 optimizer computes25 root minima; separate label-walk enumeration audits
352 admitted walks for selected minima. Five adaptive trees pass the existing
unmodified bounded-additive-spill verifier.

Six larger non-enumerating examples certify232 explicit vertices,226 edges and
27,564 evaluations against original inequalities. Nineteen invalid or forged
controls are rejected, including false slack, costs, polynomial witnesses,
changed endpoints, incomplete incidence enumeration and floating-point data.
JSON round trips are verified as well as in-memory rational certificates.

The two Lean candidates formalize: finite metric propagation across light
transitions; the retained-row bridge; the two-heavy-occurrence mass bound; and
finite supporting-kernel vertex/ordinary-edge criteria with consecutive-root
factor signs. The matching classification, alternating-path construction,
cyclic carrier-excess dichotomy and full infinite obstruction are proved in
this note but not all packaged as Lean declarations. Exact JSON verification
is not kernel verification, and the new modules have not been compiled here.

## 7. Literature, interpretation and next direction

The moment-curve/matching realization is classical. A. M. Maksimenko,
"The diameter of the ridge-graph of a cyclic polytope," Discrete Mathematics
and Applications 19(1),47--53 (2009), DOI10.1515/DMA.2009.003, gives an exact
classical diameter formula. We do not claim a new diameter result for cyclic
polars, and do not use the publisher's ambiguously rendered formula in any
certificate. Primary source checked: https://doi.org/10.1515/DMA.2009.003.
The work here concerns the cost of the proposed portal/excess certificate
restriction, not the already studied diameter of this family.

The previous finite evidence for slack1/b2 does not extend universally. The
correct research target must permit genuinely adaptive-length low-cost portal
chains, or charge only the unresolved high-dimensional part while separately
routing known easy carriers. The fixed-additive-spill recurrence in #208 remains
valid and useful; its geometric existence premise without a fixed-slack cap
is still open. This continuation supplies a necessary stress test and a direct
solution for that stress family, not another cosmetic reduction in the mission
dependency graph.
