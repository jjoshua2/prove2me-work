# Cone-face descent: explicit costs for apex-preserving low-rank clipping

Continuation of the simultaneous-clipping / one-ray program, 2026-09-09.
Repository: `jjoshua2/prove2me-work`.

## Evidence boundary

This note gives an ordinary mathematical proof. Its general polyhedral theorem
has NOT been formalized in Lean. The executed rational tests certify selected
finite instances and explicitly construct their routes; they are not proof by
testing. No literature-priority claim is made.

A separate part of this branch compiles and repairs the preceding bounded-
clipping and horizon-helper Lean candidates. Those compiler results do not
verify the theorem in this note. Read `ClippingVerificationProgress.md` for
that independent verification status. No Prove2Me action is performed; the
user handles publication. No new Open child is introduced.

## 1. Replace unknown face costs with geometric descent

The preceding pointed-unbounded argument gives D+1+sum(final cut-face diameters).
But a once-truncated cone over an N-gon is a pyramid. Its cut face has diameter
floor(N/2), while its whole graph has diameter two through the old apex. One
large intrinsic face charge can be arbitrarily worse than two inherited edges.

Here the repair supports are faces of the OLD CONE containing the apex. The
route pays for actual graph steps before entering a smaller cone face. Those
prefix costs are bounded by independent subsets of NEW rows, without assuming
any unknown intrinsic diameter.

## 2. Exact hypotheses

Let C be a pointed polyhedral cone with apex o. Work in its affine span and
write C={x : A_j(x-o)<=0 for all old rows j}. Old rows may be redundant; C need
not be simplicial. Add m cuts a_i(x-o)<=b_i, with EVERY b_i>0, such that the final
polytope P is bounded. Thus the apex is strictly retained by every new cut.

For a vertex v of P, H_v denotes its smallest old-cone face, its *carrier*.
Put k(v)=dim(H_v), and G_v=P intersect H_v. Let r be the rank of the new normals
restricted to the direction space of C. Define R=max_v k(v). We prove R<=r<=m.

The old facet count, ray count, and ambient dimension do not occur in the bound.
This is a path-length statement, not a claim that enumerating vertices or face
lattices takes polynomial time. The zero-dimensional case P={o} is immediate.

## 3. The explicit bound

For 0<=k<=m set

    E(m,0)=0,
    E(m,1)=1,
    E(m,k)=floor((m+2)/2)+sum_{j=3}^k binom(m,j),  k>=2.

Every final vertex v has an ordinary P-edge path to o of length <=E(m,k(v)).
The path descends through nested old-cone carrier faces, never returning to a
larger carrier after a strict dimension drop. Consequently

    dist_P(u,v) <= E(m,k(u))+E(m,k(v)),
    eccentricity_P(o) <= E(m,R),
    diam(P) <= 2 E(m,R) <= 2 E(m,r)
            <= 2 sum_{j=1}^r binom(m,j)
            <= 2 ((m+1)^r-1).

This is polynomial for FIXED new-cut rank r, with no assumed face-diameter
budgets. If r grows to m, the simple bound is 2(2^m-1), not fixed-polynomial
Hirsch. Small-rank consequences are radius<=1 / diameter<=2 at rank one, and
radius<=floor((m+2)/2) / diameter<=m+2 at rank two. Any two cuts give radius<=2
and diameter<=4, irrespective of the cone's ambient dimension.

Optimality of every all-pairs constant is not claimed. The planar rank-two
apex eccentricity is sharp on the checked family below.

## 4. Carriers are genuine final faces

Let J(v) be the old rows tight at v. Then

    H_v=C intersect {A_j(x-o)=0 : j in J(v)}.

Every remaining old row is strict at v, so v is in relint(H_v). Each old row
is a supporting inequality also valid on P. Therefore G_v=P intersect H_v is
a genuine face of P, and its graph edges are P graph edges. No arbitrary slice
edge or circuit segment is being treated as a parent edge.

Strictness of the new cuts at o leaves a small relative neighborhood of o
inside H_v feasible. Thus dim(G_v)=dim(H_v)=k(v). In positive dimension, the
apex is on the relative boundary of the pointed cone H_v.

If a vertex w of G_v is on that relative boundary, its carrier H_w is a proper
face of H_v. Hence H_w is contained in H_v and k(w)<k(v). The dimension drop is
a proved consequence of the geometry, not a supplied rank-descent assumption.

## 5. Count only relative-interior vertices of one carrier

Fix a k-dimensional carrier H. At a vertex x of P intersect H in relint(H),
all non-universal old rows are strict. The active new rows must span the dual
of H's direction space. Otherwise a nonzero vector annihilating those rows
allows small feasible displacements in both directions through x, contradicting
extremeness. This proves k<=rank(new rows restricted to H)<=r and thus R<=r.

Choose k independent active new rows at each such vertex, using a fixed order
to resolve ties. Those k equalities determine at most one point in aff(H).
Different vertices cannot be assigned the same k-element subset, so

    number of relative-interior vertices of P intersect H <= binom(m,k).  (A)

An instance-specific bound can count independent restricted bases only. The
exact checker constructs these injective assignments and checks their ranks.
The total number of cone faces, rays, or final vertices may be arbitrarily large;
(A) only counts interior vertices of ONE current carrier.

## 6. Escape once, then descend

For k>=3, take a simple graph path inside the compact polytope G=P intersect H
from the current v to o; qualitative graph connectivity suffices. Stop at its
first vertex w on the relative boundary of H. All preceding vertices lie in
relint(H) and are distinct. The prefix edge count equals their number, so (A)
gives a cost at most binom(m,k).

Now recurse inside the true final face P intersect H_w. Its carrier dimension
is smaller. All later vertices lie in the boundary of H, so no earlier
relative-interior vertex is revisited. Each carrier dimension is charged at
most once, even when dimensions are skipped. This is a nested path, not a
branching recursion over every face.

Repeating the count to dimension zero gives sum_{j=1}^k binom(m,j). The low-
dimensional base cases below improve it. The selected path is not asserted
monotone for every linear objective, and no strongly polynomial pivot rule is
claimed.

## 7. Ray and polygon base cases

A one-dimensional pointed carrier is a ray. Its bounded clipping, strictly
retaining o, is a segment [o,v]. This is a P edge, so cost one recovers the
pyramid's inherited-edge shortcut without paying the base diameter.

A two-dimensional pointed carrier is a wedge with two true boundary sides.
Redundant old rows do not create more sides. Adding m halfplanes gives a
polygon with at most m+2 sides. Its graph is a cycle; the shorter boundary arc
to o costs at most floor((m+2)/2). Since this polygon is P intersect H, every
arc step is a parent edge.

Add the binomial prefix charges above this base case to obtain E(m,k). It is
nondecreasing on 0<=k<=m, and E(m,k)<=sum_{j=1}^k binom(m,j); for k>=2, use
floor((m+2)/2)<=m+binom(m,2). Finally, list each subset of {1,...,m} of size at
most r in increasing order and pad with zeros to length r. This injects them
into words over {0,...,m}. Removing the empty subset proves the (m+1)^r-1 bound.

## 8. Apex removal defeats even rank-one / two-cut bounds

Take the cone over the N-gon whose rays pass through (i,i^2,1), i=0,...,N-1.
Impose 1<=z<=2. These are two new cuts of normal rank one, but they remove the
apex. The resulting frustum has the graph of an N-gonal prism, of diameter
floor(N/2)+1. The old cone complexity can make this arbitrarily large.

The checker reconstructs N=4,8,12,16,24 exactly, obtaining diameters
3,5,7,9,13. This falsifies dropping apex retention, not the present theorem,
the preceding one-ray theorem, or Polynomial Hirsch.

## 9. Executed exact certificates

Reproduce with

    python3 scripts/test_cone_carrier_descent.py --output /tmp/carrier.json
    python3 scripts/check_carrier_regression.py /tmp/carrier.json

The checker uses Fraction, exhaustive candidate vertex/recession-ray bases,
exact tight-row ranks, and graph searches. It verifies carrier dimensions,
independent-basis injections, true final-face edges, first-boundary prefixes,
strict dimension drops, and every final explicit cost bound. It builds root
paths for every vertex and checks all unordered endpoint pairs (including
identical pairs). All-pairs walks may repeat a root-path segment; loop erasure
can only improve them. Actual graph diameters are computed for comparison,
not passed into the new route budget.

Final coverage: 40 apex-preserving rational instances; 695 vertices; 8,813
unordered pairs; 484 used carriers; 655 independent-basis vertex certificates;
five separate apex-removal falsifiers. Every constructed route passed.
Two complete local runs reproduced the full JSON byte-for-byte, SHA-256
`8ea13789aa3f0763d28ec5814b6b93ca241ba7a2dab569a97389413d8aab5514`.

A preliminary 38-instance run passed before two designated Dantzig roots were
added. One utility-extraction attempt failed due to a missing `cube_rows`
import; it was repaired before both complete final runs. No failed attempt is
counted as verification.

Concrete comparisons:

| Case | Previous final-face bound | New explicit bound | Actual diameter |
|---|---:|---:|---:|
| Pyramid over 24-gon | 13 | 2 | 2 |
| 5D cone over 4-cube, five rank-two cuts, 49 vertices | 21 | 6 | 5 |
| 6D orthant, six rank-two cuts, 42 vertices | 15 | 8 | 5 |

The planar six-cut instance is an eight-cycle with apex eccentricity four,
attaining the planar base bound. The 4D/5D Dantzig tangent-cone cases include
both generic roots and the designated source tight sets {3,4,5,6} and
{0,1,2,3,5}. The designated cases have carrier dimensions four and five at the
estranged targets. They explicitly forbid assuming low carrier dimension or
new-row rank in the general balanced problem.

These finite tests are exact rational hull/graph certificates, not Lean hull
formalizations or proof of a universal theorem. The general proof is above.

## 10. Relation to the formal open frontier

This is a non-cyclic sufficient geometric result with explicit cost control,
not another hypothesis that a cheap connected network exists. No ancestor
theorem, global polynomial diameter, or arbitrary circuit-to-edge conversion is
assumed. At a tangent cone of P rooted at u, new rows are the rows not tight at
u; cone carriers correspond to common faces of u and the routed vertex.

The existing common-face/effective-row toolkit may help identify low-rank
pieces, but low rank is not automatic: the designated Dantzig tests enforce
that boundary. A global proof still needs a valid decomposition into such
pieces with controlled total cost, or a better bound on independent active
bases encountered in high-dimensional carriers. The binomial sum remains
exponential when its rank parameter grows with input size.

The next falsifiable target is to control the total independent-new-cut bases
encountered along SELECTED nested carriers, or bypass expensive carriers using
additional true inherited routes. Test candidate claims against the designated
Dantzig endpoints and apex-removing frusta before adding platform children.
The formal `Hirsch.polynomial_edge_refinement_of_circuit_walks` leaf is unchanged.

## Provenance

The cap-cost obstruction and tangent-cone setup come from the preceding
`UnboundedClippingOneRay.md` packet. Rational Dantzig coordinates come from the
PR #50 regression utility. The pointed H-polyhedron utility is extracted from
the preceding unbounded checker, retaining its assumptions. External searches
did not establish literature priority for this rank-sensitive formulation;
no priority inference is drawn from that.
