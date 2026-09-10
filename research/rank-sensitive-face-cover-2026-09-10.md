# Rank-sensitive face covers and the recursive averaging barrier

## Scope and verification

This is research on the existing edge-diameter frontier, not a proof of
Polynomial Hirsch and not a new Prove2Me decomposition. No Prove2Me call,
credential use, theorem submission, or publication is part of this work.

The finite Python certificate checks were executed with exact integer/Fraction
arithmetic: 2,000 weighted covers, 28 cube primal/dual certificates through
dimension 7, and 21,296 proper-face dual constraints passed. These checks do
not verify the Lean files. Lean status must be taken from the final gate's
actual result, not inferred from the existence of source files or #print commands.

## 1. Repair of the previous pair-face candidate

Run 34519385197 failed in two places. `IsExtreme.mono` was applied directly to
the second row face instead of first forming the intersection as an extreme
subset of the parent. Also, `S.card - 1 + 1 = S.card` needed positivity of
`S.card`, rather than a bare `rfl`. Both source repairs are included.

## 2. The codimension incidence lemma

Let P = {x : a_i dot x <= b_i}, with finitely many rows in R^d. If x is a
vertex and U is any normal subspace of rank r, then

    #{ i : a_i not in U and a_i dot x = b_i } >= d - r.

Proof: restrict the linear row-evaluation map to U-perp, retaining only the
tight rows outside U. This map is injective. Indeed, a vector in its kernel
annihilates the retained rows; it also annihilates rows in U by orthogonality.
It therefore annihilates every row tight at x. The existing finite-perturbation
vertex theorem forces it to be zero. Comparing dimensions proves the claim.

This handles redundant H-presentations and does not require simplicity.
The count is of row indices; it is not a claim that all counted rows are
linearly independent of one another.

Lean declaration:
`HirschRankFaceCover.tight_rows_outside_subspace_card_ge_codim`.

## 3. Saturation is necessary for genuine geometric descent

For an extreme face F, define U_F as the span of *all* row normals whose
equations hold throughout F. Do not use only the rows initially selected to
name the face.

For a_i outside U_F, the section G = F intersect {a_i dot x = b_i} is a proper
subset of F, and U_F is strictly contained in U_G. Normal rank therefore
strictly increases. G can be empty; this does not assert the existence of a
nonempty useful child or a cheap collection of children.

Exact regression: in [0,1]^3, the valid redundant inequality -x-y <= 0 exposes
the edge F={(0,0,z):0<=z<=1}. Its selected normal (-1,-1,0) has rank one.
The normal (-1,0,0) is independent of that normal, yet imposing -x=0 leaves F
unchanged. The saturated span already contains both -e_x and -e_y and has
rank two, so our definition rejects this false descent.

Lean declarations include `faceRowSpan_lt_rowSection` and
`faceRowSpan_finrank_lt_rowSection`.

## 4. Weighted averaging, without hidden parent hypotheses

Give extreme subfaces F_i nonnegative integer weights w_i. Suppose every
vertex of F is covered with total weight at least q>0. Assume a child diameter
bound B_i only when w_i>0. Shortest-path incidence counting gives

    diam(F) <= floor( sum_i w_i (B_i+1) / q ) - 1.

This certificate remains conditional on child bounds and connectivity. It does
not assert that a cheap cover exists. Rational covers are representable by
clearing denominators.

Zero weight really removes a face: it incurs no +1 charge and needs no
intrinsic diameter hypothesis. This matters because a row whose equation
already holds on F can otherwise make the alleged child bound a bound on F
itself.

Combining this with the codimension lemma, select only a_i outside U. Then

    diam(F) <= floor( sum_{a_i outside U} (B_i+1) / (d-rank U) ) - 1.

Use U_F for proper rank-increasing sections. The statement assumes rank U<d;
it does not divide by zero or silently treat the terminal case as progress.

## 5. A general obstruction to purely recursive averaging

Let V be the full vertex set being covered. Suppose every positive-weight
child is charged at least its own vertex count:

    B_i + 1 >= |V intersect F_i|.

Summing the coverage condition over *all* vertices, rather than only vertices
of a chosen shortest path, gives

    q |V|
      <= sum_{v in V} sum_{i: v in F_i} w_i
       = sum_i w_i |V intersect F_i|
      <= sum_i w_i (B_i+1).

Consequently the certificate output satisfies

    floor( sum_i w_i (B_i+1) / q ) - 1 >= |V| - 1.

This lower bound is on the **certificate output**, not on actual diameter.
It permits arbitrary subface choices, mixed ranks, and weights. Thus a scheme
that starts with singleton bounds and obtains every larger-face bound solely
by this averaging formula cannot bootstrap itself below vertex counting.

Equivalently, any strict improvement must use a positive-weight child with
B_i+1 < |V intersect F_i|. That first improvement needs independent geometry.
It cannot be created merely by better incidence bookkeeping.

Lean declarations:
`weighted_cover_cardinality_lower_bound`,
`averaging_budget_ge_card_sub_one`, and
`improving_certificate_requires_improving_child`.

## 6. Cube stress test: even exact bounded-dimensional seeds are insufficient

A d-cube has actual diameter d: each edge flips one coordinate, and differing
coordinates can be flipped successively. Its rank-sensitive recursive facet
certificate with singleton seeds instead obeys

    B_0=0,   B_d=2(B_{d-1}+1)-1,
    hence B_d=2^d-1.

There is a stronger exact optimization result for this certificate model.
Supply exact cube diameters for every face of dimension at most k, where
0<=k<d, and propagate above that using weighted face covers. Even allowing
*all proper faces of every rank* and arbitrary nonnegative rational weights,
the optimum is

    B_d = (k+1) 2^(d-k) - 1.

Primal certificate: use every k-face with weight 1/binomial(d,k). Each vertex
belongs to binomial(d,k) such faces; there are binomial(d,k) 2^(d-k) of them.
The total cost is (k+1) 2^(d-k).

Dual certificate: put mass (k+1)/2^k on every cube vertex. For an r-face,
the dual mass is (k+1) 2^(r-k). This is at most its child cost: r+1 for r<=k,
and exactly (k+1) 2^(r-k) for propagated r>k. The inequality for r<k follows
because (r+1)/2^r is nonincreasing. Primal and dual values agree exactly.
Induction on d justifies the propagated child costs, beginning with the given
exact seeds.

Examples (formula, not new enumerations):

| d | largest exact seed k | optimal averaging certificate | actual diameter |
|---|---|---|---|
| 8 | 0 | 255 | 8 |
| 8 | 2 | 191 | 8 |
| 8 | 7 | 15 | 8 |
| 16 | 2 | 49,151 | 16 |
| 20 | 2 | 786,431 | 20 |

The full mixed-rank optimization statement is proved above in ordinary
mathematics and checked by exact finite primal/dual certificates through d=7.
The Lean barrier module formalizes the general vertex-count obstruction and
the singleton-seeded recurrence; it does not formalize the entire cube face
lattice or the mixed-rank optimization theorem.

## 7. Decision for continued work

Keep the rank and weighted-cover lemmas as reusable certificates, but do not
expand a hierarchy of rank-r intersection lemmas expecting polynomial
complexity to emerge automatically. The obstacle persists on simple cubes
and under optimal weighting; it is not just degeneracy.

A useful next result must inject a genuinely non-counting geometric estimate:
for example an independently established product/separable-face bound (the
repository already has a product-walk theorem), or a constructive routing
argument that controls useful progress rather than charging a whole recursive
cover. Neither structure is assumed to exist for arbitrary H-polytopes here.

Reproduce the exact finite checks:

    python3 scripts/test_rank_face_cover_barrier.py --max-dimension 7

Targeted Lean check:

    lake build Solutions.PolynomialBalancedPairFaceCover \
      Solutions.PolynomialWeightedFaceCover \
      Solutions.PolynomialRankSensitiveFaceCover \
      Solutions.PolynomialFaceCoverBarrier

The pinned environment remains Lean 4.30.0 and Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f.
