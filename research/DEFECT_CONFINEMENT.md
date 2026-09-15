# Confined facet defects: a parameterized ordinary-edge bound beyond flag polytopes

## Status, hypotheses, and what is new here

This is a written mathematical argument plus exact rational research software.
It is NOT a Lean-compiled theorem, an authenticated Prove2Me acceptance, or a
proof of Polynomial Hirsch. It reuses the actual unchanged #258 original-H
combinatorial segment and its exact intersection/edge auditors. It does not
modify path selection, substitute a supplied vertex graph, or assume a cheap
repair. The new quantitative statement controls the visited subset of vertices
when only a specified set of facets can be revisited.

Let P be a simple bounded full-dimensional d-polytope with m genuine original
facets. Write e=m-d. Choose a set B of k exceptional original facet labels and
let g=m-k be the number of other, protected labels. Require either:

**Global input-side condition.** Every inclusion-minimal empty intersection of
original facets having at least three members is WHOLLY CONTAINED in B.

**Execution-local condition.** In every recursive link graph actually visited
by a specified Adiprasito--Benedetti combinatorial segment, every missing
triangle has all three of its labels in B. All pair/triple intersections are
interpreted after adjoining the locked original labels of that link.

The global condition implies the local one for every segment and every pair
of endpoints. The local condition can be smaller, but is a certificate about
that execution, not a promise that future executions use the same small B.
Neither condition merely says B HITS each missing face. That weaker hypothesis
cannot protect the other two vertices of a missing triangle. Nor does a bound
on the SIZES of missing faces imply a bound on the union of their labels.

For either condition, a loop-erased original-edge route delivered by the segment
has length at most

    U(m,d,k) = sum_{s=max(0,d-g)}^{min(k,d)} binom(k,s)*(g-d+s+1) - 1
             <= (e+1)*2^k - 1.                                (1)

For k<=min(d,e), the exact expression simplifies to

    U(m,d,k) = 2^(k-1)*(2e-k+2)-1   if k>=1;
    U(m,d,0) = e.                                                (2)

Thus fixed k gives a LINEAR ordinary-edge bound in facet excess, and
k=O(log m) gives a polynomial bound. The theorem does not assert such a small
exceptional set exists on arbitrary polytopes. Constants and size are measured
in the ORIGINAL facet description, not a projected extension.

This is an extension of the partial-nonrevisiting mechanism, not a claim of
historical priority for every consequence. The exact scoped result and its
proof are given here rather than attributed to a literature theorem that
has different hypotheses. Classical sources and relevant differences appear
at the end.

## 1. Why all nonexceptional labels are nonrevisiting

Work in the normal simplicial boundary dual to P. Fix a protected vertex label
w. Adiprasito--Benedetti's Section 3 first constructs a segment by recursive
link paths, with a shortest graph path of anchors called its necklace. Their
Lemma 3.1 proves that if a current path facet contains w and a later necklace
anchor is adjacent to w, then the intervening path remains in the star of w.
The only use of flagness in that induction is to fill the triangle made of w
and two consecutive anchors. We spell out the localization needed here.

Induct simultaneously on recursive dimension for this star-containment claim
and for the one-interval property of w. If w is locked, every child contains
it. The zero-dimensional case is immediate. If both occurrences lie in the
same child segment, use induction in that actually visited link. Otherwise
let p_i and p_j be the associated anchors. Both are adjacent to w. Necklace
geodesicity gives j-i<=2. A gap of two would make w a distance-reducing target
of the earlier child; since that child stops at its FIRST target hit, w would
already force an earlier next-anchor transition, a contradiction. Thus the
relevant anchors are consecutive. The three edges wp_i,wp_{i+1},p_ip_{i+1}
form a triangle in the current visited link. Since w is protected, the local
hypothesis fills this triangle. Consequently p_{i+1} belongs to the star of w
in the earlier anchor's link. Apply the inductive star-containment statement
to that child, and the within-child one-interval statement at the later end.
This establishes no reentry of w across the transition. The final common-
target-anchor recursion has the identical decomposition. All link calls used
by the induction are child calls of the actual construction, not unvisited
links assumed certified without evidence.

This proves that the times at which each protected original facet is active
form one interval. It requires filled triangles containing THAT facet in all
of the relevant visited links, not filled triangles involving every label.

For the global condition, take a missing triangle T={a,b,c} in link(S). Each
S+pair from T is a face, whereas S+T is not. Choose an inclusion-minimal nonface
N inside S+T. N must contain all three elements of T, since deleting any one
of them leaves a face. Hence |N|>=3 and N is contained in B; therefore T is
contained in B. This proves local confinement without enumerating an execution.
It also proves that the same protected labels stay protected after passing
to any face link.

The executable consumer additionally CHECKS the protected one-interval property
in the actual returned path. That is an independent consistency check; it does
not replace the geometric implication just proved or claim its Python checker
has been formalized. An invalid local triangle table is rejected even if an
incidental short path happened to avoid reentries.

## 2. Count visited signatures rather than all possible vertices

First erase loops chronologically whenever a complete active d-set repeats.
The endpoints and original adjacency are preserved. Removing time intervals
cannot introduce a new leave-and-reenter event for any protected label. After
this operation every full active set appears at most once.

Fix S subset B of cardinality s and restrict the route to vertices whose active
exceptional set is exactly S. Their protected active sets all have cardinality
d-s. Consider any member G_j after the first in this subsequence. If every
label in G_j had already appeared at an earlier member, its one-interval
property would force it to be active at the immediately preceding member as
well. Thus G_j is contained in that previous protected set. Equal cardinality
would make the two protected sets equal and, together with the same S, would
repeat a full vertex. That contradicts loop erasure.

Therefore EACH subsequent occurrence of signature S introduces at least one
protected label not previously used in this subsequence. The first uses d-s
of the g available protected labels. There can be at most

    1 + g-(d-s) = g-d+s+1

vertices of this signature. Feasible s satisfy 0<=s<=k and 0<=d-s<=g. Summing
over all possible S proves (1). Every summand factor is at most e+1, proving
the simpler inequality. When 0<=k<=min(d,e), all s=0,...,k occur in the sum;
using sum binom(k,s)=2^k and sum s*binom(k,s)=k*2^(k-1) proves (2).

A further refinement uses any CERTIFIED impossible exceptional subset. Let K_B
be any family of exceptional signatures containing all those that can actually
occur at original vertices. Then the same proof gives

    L <= sum_{S in K_B, 0<=d-|S|<=g} (g-d+|S|+1)-1.             (2a)

It suffices to exclude subsets containing a known empty original intersection;
we do not need to know every minimal nonface. The consumer uses only the original
separated_rows from already-checked strict-dual exclusion witnesses. It does NOT
turn emptiness of S+T in a link into a claim that T alone is empty. Enumeration
of exceptional signatures is capped at16 labels; above that it retains (1).
This optional refinement consumes no additional LP calls.

This is not the old claim that the full polytope or a target-deleted relaxation
has few vertices. Exponentially many vertices may exist, but the one-interval
property constrains which ones can occur with each exceptional signature.
The argument applies to ANY facet-exchange path with the protected-interval
property, not just a segment. The geometric condition is what supplies that
property for the constructed route. An arbitrary later reentry repair does
not inherit it unless it is checked again.

The conclusion is a route-length/existence bound. It does not bound the work
of constructing and then erasing a possibly longer raw path, recognizing a
small global B, solving LP queries, or enumerating the extra local triangles.
We do not silently substitute the loop-erased output length into an existing
raw-output-sensitive runtime theorem.

## 3. Stability under nonproduct geometric modifications

A useful family can retain a small exceptional set without remaining a Cartesian
product. We use the following elementary stellar-subdivision fact on the dual.

Suppose all minimal nonfaces of size>=3 are contained in B, and uv is an edge
with BOTH u,v outside B. Stellar-subdivide that edge, introducing z. The old
minimal nonfaces of size>=3 persist unchanged. The new minimal nonfaces are
only pairs: uv itself, and zw whenever uw or vw was an old missing pair.

Indeed, an old face not containing uv survives, and no high minimal nonface
can contain u or v by hypothesis. A face z+T exists precisely when T does not
contain uv and T+uv was an old face. If T+uv fails, a minimal old nonface N is
contained there. If N meets u or v, it must be a pair, producing the stated
missing pair zw. Otherwise N is already in T, so z+T is not a new MINIMAL
nonface. This proves the full classification, not just that one test path
retains its old labels. By polarity, sufficiently shallow codimension-two
truncations between two protected facets preserve the same exceptional core.
The new facet label z is protected as well.

## 4. Explicit all-dimensional nonproduct family with only three exceptions

For d>=3 and coordinates x_0,...,x_(d-1), put S=x_0+x_1+x_2 and impose

    0<=x_i<=1                                      for every i,
    S<=5/2,
    S-x_j<=5/2-delta_j, delta_j=2^(-(j+1))          for 3<=j<d.       (3)

There are m=3d-2 genuine facets and e=2d-2. The exceptional labels are precisely
the three upper-coordinate facets x_0=1,x_1=1,x_2=1. Their triple intersection
is empty, but every pair intersects. ALL other minimal empty facet intersections
have size two. Consequently every pair of original vertices has the delivered
segment bound

    L <= 7e-6 = 14d-20.                                           (4)

Here (2) first gives8e-5, but the exceptional triple cannot itself be an active
subset. Removing its e+1 state capacity using (2a) gives7e-6. All its proper
subsets are allowed; no stronger implicit signature deletion is used.

Proof of the presentation and complete minimal-nonface claim follows from actual
shallow cuts, not finite extrapolation. Start with the cube and cut its face
x_0=x_1=x_2=1 by S<=5/2. The first three-dimensional factor is a cube with one
vertex truncated. Its only high minimal nonface is the upper triple, and its
other minimal nonfaces are opposite-coordinate pairs and the cap paired with
each of the first three lower facets. Extra interval factors add only pairs.

In increasing j, the next inequality in (3) cuts the ridge cap intersect x_j=0.
The unused coordinate x_j is still an independent interval. The current S-values
at vertices belong to {0,1,2,5/2} together with the earlier 5/2-delta_i. Since
delta_j is smaller than every preceding delta_i, the new cut violates exactly
the old vertices on cap and x_j=0 and contains no old vertex on its hyperplane.
It is therefore a shallow simple ridge truncation. Both facets are protected,
so the stellar lemma applies at every step. This proves simplicity, preservation
of all old facets, existence of each new facet, and the claimed minimal nonfaces
in every dimension. Coordinate bounds give boundedness, and x_i=1/2 gives a
strictly feasible point.

The initial cut leaves 10*2^(d-3) vertices. The cap is a triangular prism product:
its vertex count is 3*2^(d-3), and every untouched extra lower facet meets half
of these. Truncating cap against an extra lower facet removes 3*2^(d-4) simple
vertices and replaces each by two; the cap after truncation retains that same
triangular-product combinatorics. Thus for d>=4 the final vertex count is

    V=(3d+11)*2^(d-4);     V=10 when d=3.                         (5)

For d=12 this is 12,032 vertices on 34 original facets, while (4) is 148 edges
for EVERY endpoint pair. That is a written class bound, not a claim that all
those pairs or all vertices were enumerated.

The family is not combinatorially a nontrivial Cartesian product. The hypergraph
on facet labels, joining the labels of each minimal nonface, is connected:
the upper triple, coordinate-opposite pairs and cap-to-lower pairs connect the
initial truncated-cube factor; each new cap/extra-lower missing pair connects
another interval component, and new facets have missing-pair links into it.
A Cartesian product would make the dual boundary a nontrivial join, splitting
all minimal nonfaces across disjoint components. The connected hypergraph
excludes that. This is COMBINATORIAL product indecomposability, not an assertion
of Minkowski indecomposability or difficult diameter.

### Exact specialized witness producer, not a trusted face oracle

The large tests use no vertex graph. The generic #258 LP producer is used for
d=6 and d=8. For d=12 an additional untrusted producer exploits (3) to construct
intersection witnesses using a scalar interval for S. Locked first-three lower/
upper rows give the sum interval; cap or cut equalities and extra-coordinate
locks refine it. Pick a feasible S and allocate the first three coordinates in
[0,1], then use x_j=max(0,S-5/2+delta_j) unless it is fixed at an endpoint.

Absent intersections contain an explicit missing pair or the upper triple.
For the triple, the cap is a strict dual certificate: sum first-three uppers
has maximum at most 5/2<3. All missing pairs have one- or two-row certificates:
for example cap+lower_j is bounded by cut_j at 5/2-delta_j<5/2;
cut_j+upper_j is bounded by the cap at 5/2<7/2-delta_j; and cut_j+lower_i
for i<j is bounded by cut_i+lower_j at 5/2-delta_i<5/2-delta_j.
Every supplied answer is rechecked by the unchanged original-row consumer.
The exact recursive segment code and the new confinement consumer are unchanged
between generic and specialized producers. Dimensions 3,4,5 have complete
label-path agreement between the two. We do NOT claim a completed generic
LP replay for dimension12 or any polynomial bound for arbitrary instances.

## 5. Verification layers and reproducibility

`defect_confinement.py` checks every triangle in every used recursive link,
not merely the first missing triangle. The additional intersection table is
independently audited against original rational A,b. It verifies the original
#258 segment, replays its BFS and recursion, checks protected-label intervals,
then builds the exceptional-signature count with explicit fresh-label witnesses.
It is not a global flag recognizer, a minimal-core optimizer or a new selector.
The standalone interval-count routine also receives exhaustive and randomized
facet-exchange-path controls unrelated to polytopes.

`test_defect_confinement.py` reconstructs all active-square systems independently
for the family in dimensions3/4/5, cross-checks a complete shallow-clipping
transcript and its minimal nonfaces, and proves every row genuine by strict
facet anchors. It tests21 endpoint pairs per dimension. The larger d6/8/12 runs
use no full vertex graph. A tiny input-only fixture reuses14 named test inputs
from #258; their complete raw segments and new local certificates are produced
AFRESH, rather than counting old acceptance records as a new execution.

Further nonflag controls have actual reentries. The known 3D/eight-facet
moment-polar has a six-label core. Products in dimensions4 and6 preserve that
core, as does a cross-factor protected-ridge truncation making a nonproduct
four-polytope. The raw segments reenter an exceptional facet, while the protected
intervals and count remain valid. Merely selecting one facet that hits a missing
triangle is explicitly rejected. The report retains cases with large local k:
we do not replace them by k=3 or claim a uniformly small parameter on the holdouts.

The final completed suite checks83 geometric routes and28,568 used-link
triangles. Its family d3/d4/d5 stages have63 endpoint pairs,162 original edges
and1,532 independent square systems; their observed routes are shortest but
that property is not asserted for all dimensions or inputs. Fourteen historical
inputs are reconstructed afresh. Three additional holdouts have actual
exceptional-facet reentries. The d6,d8,d12 selected family paths have6,8,12 edges
and certified signature bounds64,92,148. Their construction-proved vertex counts
are116,560,12,032, not enumerated reference graphs. The standalone state lemma
has1,638 randomized interval-path and9,466 exhaustive small-path checks. Seven
malformed or unsupported controls fail and23 saved full audits pass with all
geometric production disabled. Every test field is recorded, including larger
local exceptional sets on holdouts.

The final report provides all route/certificate counts and source hashes.
The complete fixture contains detailed original-H certificates; a clean replay
must match all numeric fields except timings and the fixture byte-for-byte.
Audit replays disable LP, inversion, basis generation and intersection production;
BFS/recursion replay still occurs. None of this is Lean-extracted verification.

    python3 scripts/test_defect_confinement.py --large
    python3 scripts/defect_confinement.py input.json segment.json --output confined.json

The new input-only fixture is `fixtures/defect_reference_inputs.json`. All three
older code dependencies remain byte-identical. No accepted proof, pending
submission, compiler pin, workflow or credential configuration is changed.

## 6. Literature, precise scope, and the next quantitative obstacle

Adiprasito--Benedetti, *The Hirsch conjecture holds for normal flag complexes*,
arXiv1303.3598, Section3 and Lemma3.1, supplies the classical construction and
flag nonrevisiting mechanism. The protected-label specialization and signature
count above are spelled out rather than assumed under the name of that theorem.
https://arxiv.org/abs/1303.3598

Labbé--Manneville--Santos, *Hirsch polytopes with exponentially long combinatorial
segments*, arXiv1510.07678, proves both a banner-complex bound (Theorem3.9) and
exponential examples for EVERY combinatorial segment (Theorem4.5). Neither is
reproved or advertised as this contribution. The exceptional-label parameter
is different from banner size. For (3), the three exceptional uppers, the cap,
and all extra uppers form a critical nonface clique of cardinality d+1: all
pairs meet, and removing one exceptional upper gives a vertex. Thus small
k=3 does not force a small banner threshold as dimension grows. Conversely
bounding individual missing-face sizes does not bound their union.
https://arxiv.org/abs/1510.07678

This result supplies a genuine parameterized class bound for arbitrary endpoint
pairs, not an unconditional solution for all polytopes. The global exceptional
set can be large: a d-simplex has one high minimal nonface containing all d+1
facet labels despite diameter1. Large k is not a diameter lower bound. On the
published long-segment families, some parameter or hypothesis must leave the
fixed-k regime; the current work does not implement those families or defeat
their lower bound.

The remaining useful question is whether an arbitrary carrier can be routed
with a controlled LOCAL exceptional signature supply, or whether a repair/
different construction can reduce that supply with bounded cost. Do not insert
k=O(log m), a polynomial number of signatures, or a cheap reduction as an
unproved premise while claiming Polynomial Hirsch. What is now derived is the
quantitative payoff WHEN confinement is established, with an explicit nonproduct
all-dimensional family and a certificate checker for that condition.
