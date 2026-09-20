# Every zonotope completion can be intrinsically expensive

## Current status and formal boundary

The GENERAL direction-inheritance/lower-bound theorem in Sections 1-2 is now
ACCEPTED in #319: theorem da8f6dad-a557-46a6-99ad-11ef6d2e5a9c, submission
eff892fe-babc-4217-ae49-2eb46336d233, authenticated publisher readback Proved.
The unchanged saved candidate passed its first compiler/axiom/publication gate.
Read the packet's accepted-evidence.md and raw receipts for actual verification.

Sections 3-5 give a separate complete written argument for a family with exactly
2d original facets, original diameter d, and EVERY compact-summand zonotope
completion having global diameter at least 2^d-1. The all-dimensional family,
facet count, direction count and translation application are NOT additional Lean
theorems in this packet. Finite tests are separate from kernel verification.
This is not a Polynomial Hirsch counterexample. The older local-only version
and metadata are retained in the exported original preparation bundle.

## 1. A summand edge cannot lose its direction

Let C be any finite set in R^d, P=conv(C), Q a nonempty compact set, and
Z=P+Q=sum_i[0,w_i]. Convexity of Q is not needed; compact convex summands are
included. C need not be a vertex list. If [u,v] is a nondegenerate whole exposed
face of P, then some nonzero w_i is parallel to D=v-u.

Suppose not. Choose a coordinate j with D_j nonzero and define

    pi(x)=x-(x_j/D_j)D.

This linear map kills D and has kernel span(D). Let f expose exactly [u,v] in
P. Then f(D)=0, f(pi(x))=f(x), and f(u-c)>0 for every c in C off that edge.
Apply the accepted finite sign-preserving regularization theorem to all pi(w_i)
and all pi(u-c). It gives k nonzero on every nonzero member, preserving every
already nonzero sign of f. Set g=k composed with pi.

By the supposed absence of the direction D, each nonzero w_i has pi(w_i) nonzero,
so g is regular on all nonzero zonotope generators. Also g(D)=0: it is constant
on [u,v]. The preserved positive corner gaps imply g(c)<g(u) off the edge, and
convexity extends g(x)<=g(u) to P. Both u and v therefore maximize g on P.
Compactness supplies a maximizing q in Q. Both u+q and v+q maximize g on the
ACTUAL sum Z. They are distinct, contradicting the regular singleton-face result.

This is a transverse projection used in objective construction. It does not
project a polytope walk or turn arbitrary projected cube edges into original
edges. Actual equality P+Q=Z, rather than containment, is used to maximize on Z.
A translated zonotope gives the same written consequence: translate Q by the
opposite translation to obtain the coefficient normalization. Translation
preserves compactness, exposed segments and lengths of walks. That translation
extension is explained here, not claimed as another compiled lemma.

## 2. Every completion inherits an intrinsic lower bound

Select r exposed edges of P with pairwise distinct unoriented directions.
The preceding theorem supplies parallel nonzero generators. Distinct original
directions cannot use parallel selected generators, so the selection is injective
and every generator list has at least r entries and at least r directions.
Accepted #317 constructs opposite actual vertices of Z such that EVERY
feasible-point walk between them through nondegenerate whole exposed segments
has at least r steps. Thus

    diameter(Z) >= number of distinct unoriented edge directions of P.

The Lean packet constructs the selection, proves injectivity, and applies the
actual accepted direction-to-step proof; it does not assume inheritance or a
path-cost oracle. The original genuine edge family and whole sum identity remain
structural inputs. Accepted #316 supplies path existence separately. This is a
global completion lower bound, not a lower bound on the original summand or on
every pair of completion vertices.

## 3. An explicit original-H family with only 2d facets

Fix d>=1 and 0<epsilon<1/2. In coordinates x_0,...,x_(d-1), define

    0 <= x_0 <= 1,
    epsilon*x_(i-1) <= x_i <= 1-epsilon*x_(i-1)  (1<=i<d).

These are the ORIGINAL 2d inequalities. Induction puts every feasible coordinate
in [0,1]. Each conditional interval has width at least 1-2epsilon>0, so its two
bounding rows cannot both be tight at any feasible point. The body is closed
and bounded; the all-half point is strictly feasible and proves full dimension.

Every original row is a genuine facet. Set all other coordinates to 1/2, and set
x_i at the chosen lower or upper boundary determined by x_(i-1), or at 0/1 for
i=0. Every other inequality remains strict because epsilon<1/2. A neighborhood
within this supporting hyperplane remains feasible, giving a (d-1)-dimensional
face. There are exactly 2d facets, not just 2d presented constraints.

At an extreme point the active rows span the d-dimensional dual space: otherwise
a nonzero active-kernel vector and finite positive slack margins permit feasible
motion in both directions. At most one row from each coordinate pair is active,
so exactly one is active in each pair. Conversely any selection of one per pair
gives a triangular full-rank system with diagonal coefficients +1 or -1. Its
unique solution is feasible and extreme. Thus there are exactly 2^d vertices,
indexed by Boolean choices b_i, with

    x_0=b_0,
    x_i=epsilon*x_(i-1)       if b_i=0,
    x_i=1-epsilon*x_(i-1)     if b_i=1.

The complete vertex description is derived, not assumed from a test table.

## 4. All edges and their distinct directions

Fix all selected boundary choices except at coordinate k. Earlier coordinates
are determined. Let x_k range over its full conditional interval and propagate
the fixed later affine boundary formulas. This is exactly the feasible equality
slice of the other d-1 original rows. Its endpoints are the two Boolean choices
at k, and its open part makes both k-th inequalities strict. Summing the common
original row functionals exposes the ENTIRE nondegenerate segment.

There are no other edges. The polytope is simple, with one full-rank active row
per coordinate pair at every vertex. Equivalently an open point of a one-face
has d-1 independent active rows, with at most one per pair; exactly one pair is
unfixed, yielding the segment above. Its graph is therefore the d-cube: every
edge changes one Boolean choice and all such changes are available. Its graph
diameter is exactly d.

Orient a k-edge from its lower to its upper k-th endpoint and normalize its first
nonzero component to one. The direction has

    D_j=0  (j<k),   D_k=1,
    D_j=epsilon^(j-k) product_(l=k+1..j)(1-2b_l)  (j>k).

Prefix choices before k do not affect this direction. Tail choices are recovered
from D_j/(epsilon*D_(j-1))=1-2b_j, so coordinate k supplies exactly 2^(d-k-1)
directions. Different k have different first nonzero coordinates and cannot be
parallel. Normalization to +1 already identifies opposite orientations, giving

    number of distinct unoriented edge directions
      = sum_(k=0..d-1) 2^(d-k-1) = 2^d-1.

There are d*2^(d-1) edges; many prefix variants are parallel. The lower bound
uses distinct directions, not the larger raw edge inventory.

## 5. Consequence for ALL zonotope completions

Every nonempty compact Q for which this P_d+Q is a zonotope satisfies

    diameter(P_d+Q) >= 2^d-1,
    number of distinct generator directions >= 2^d-1.

P_d itself has exactly 2d facets and diameter d. At d8 the completion lower bound
is255 versus16 original facets and diameter8; at d16 it is65535 versus32 facets.
These are evaluations of the all-dimensional written argument, not enumerations
of the large completion graphs.

No selection strategy can produce, for EVERY n-facet polytope, a same-space
compact-summand zonotope completion whose GLOBAL diameter is bounded by one fixed
polynomial in n or in n,d: at n=2d that polynomial cannot dominate 2^d-1.
Invertible affine coordinate changes do not remove the distinct directions or
change segment adjacency. This extends the earlier bad-canonical-cube-completion
obstruction to EVERY zonotope completion of this deformed-cube family.

It does not refute Polynomial Hirsch: the original graph has short cube routes.
It does not exclude paying only for the steps surviving contraction, suitable
endpoint-sensitive use of a large completion, non-zonotopal completions, or a
different original-edge argument. Higher-dimensional constructions with arbitrary
projection are outside this same-space Minkowski statement. Accepted #318 gives
a separate stronger restriction on certain compatible endpoint lifts when a
specific rich Boolean generator family is required; it is not repeated here.

## 6. Executed checks, not a second formal family theorem

Eighteen complete small H models use epsilon=1/4,1/3,2/5 and d1..6. All3822
square active systems were solved independently, producing378 vertices and963
edge occurrences. Whole supporting faces were checked against all reference
vertices (46422 comparisons), and1092 row checks validate unique-facet witnesses.
All4092 endpoint distances through d5 equal Boolean Hamming distance. The complete
distinct-direction counts equal2^d-1.

Sixty-four selected edges in d8/16/32/64 are checked against all original rows
and exact active/common-row ranks, without enumerating their full vertex/direction
sets. Twenty-eight actual planar completions use either one sufficiently long
segment per original direction or all ordered point pairs. Erosion inequalities
construct Q, and all P+Q vertex sums reconstruct Z exactly. These are complete
planar whole-set equality checks, not containment-only checks or a general
minimal-completion theorem.

The unchanged script audits82 saved edges and28 saved completions with their
family/edge/completion producers disabled; seven malformed controls fail.
Two current full runs, including a clean script-only replay, reproduce the saved
9885-byte report and303297-byte fixture exactly. Supporting Python and JSON are
not Lean-extracted or formally verified. The script's old uncompiled-status text
is historical; the separate raw accepted receipt is authoritative for the generic
Lean theorem. Full outputs and original local preparation are in the export.

## Provenance and remaining formal work

The accepted945-line source reuses629 lines from #317 and the81-line #313
regularization section byte-for-byte. The new inheritance and injection argument
passed first-attempt pinned compilation, five standard-only transitive axiom
reports, and authenticated publication. No accepted target was resubmitted.
The concrete deformed-cube formalization remains separate from that achievement.

Classical background, with no historical-priority claim: Gaertner, Helbling,
Ota and Takahashi, Large Shadows from Sparse Inequalities, arXiv:1308.2495;
Deza--Pournin, Diameter, decomposability, and Minkowski sums of polytopes,
arXiv:1806.07643; Deza--Pournin--Sukegawa, The diameter of lattice zonotopes,
arXiv:1905.04750. The complete argument used here is supplied above independently;
this is not a claim of an exhaustive literature review or a new best diameter bound.

Read ZONOTOPE_COMPLETION_OBSTRUCTION_HANDOFF.md before further work. The generic
inheritance interface is complete; do not resubmit it or create a duplicate child.
