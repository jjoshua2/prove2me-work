# Three-dimensional carrier refinement

Supplement to `ConeCarrierDescent.md`. This is an ordinary mathematical proof,
with separately executed rational certificates, not a Lean-formalized result.
The six-module Lean audit concerns the earlier clipping theorem and helpers,
not the carrier theorem or this refinement. No Prove2Me action is involved.

## Statement

Keep the apex-preserving bounded cone-clipping hypotheses of the main note.
Write m for the number of added cuts. The cost of a three-dimensional carrier
can be sharpened from binom(m,3) to

    min(binom(m,3), 2m-2).

Thus replace the j=3 summand in E(m,k), whenever k>=3, by this smaller number.
The other terms are unchanged. In particular, for new-normal rank r<=3 and
m>=3, the resulting diameter bound is at most

    2 floor((m+2)/2) + 2 min(binom(m,3),2m-2) <= 5m-2.

Rank one and rank two retain the sharper bounds two and m+2 respectively.
For exactly three cuts, the sharper expression gives diameter at most six.
The constants are not asserted optimal. This does not control unrestricted rank.

## Proof: discard old inequalities only for the vertex COUNT

Fix a three-dimensional old-cone carrier H. Its direction space has dimension
three. On aff(H), form R using only the m new inequalities, discarding the old
cone inequalities that are not universal on H. The strict apex makes R
full-dimensional and nonempty in this affine space.

Every vertex of P intersect H in relint(H) is a vertex of R: the active new
normals already span the three-dimensional dual, and their equalities determine
that point uniquely. If no such vertex exists there is no positive-dimensional
prefix to count. Otherwise those same normals imply that R has zero lineality,
so R is a pointed three-dimensional polyhedron.

If R is bounded, it has at most m facets. If R is unbounded, cap it with one
hyperplane sufficiently far away to keep every original vertex. A linear
functional strictly positive on its nonzero recession cone gives such a cap:
choose its level above all original vertices and an interior feasible point.
The resulting bounded three-dimensional polytope has at most m+1 facets and
contains all the original vertices as vertices. This uses ordinary polyhedral
compactification only; it does not use the clipping diameter theorem.

A three-dimensional polytope with V vertices, E edges and F facets satisfies
Euler's identity V-E+F=2. Every vertex has degree at least three, so 3V<=2E.
Combining them gives

    V <= 2F-4 <= 2(m+1)-4 = 2m-2.

Consequently there are at most 2m-2 relative-interior vertices in P intersect H.
Combine this with the independently proved binomial count and apply the same
first-boundary prefix argument from the main note. Carrier dimensions strictly
drop, so the three-dimensional term is paid at most once per endpoint route.
The polygon base cost remains floor((m+2)/2), proving the formula above.

IMPORTANT: R is used only to count vertices. No edge of R is used as an edge of
P. The constructed routes still run inside genuine final faces P intersect H.
Discarding constraints for path construction would be an invalid shortcut.

## Exact tests

`python3 scripts/test_carrier_euler_refinement.py --output /tmp/euler.json`

The checker reuses all 40 instances and all 8,813 unordered endpoint pairs.
For each of 37 encountered three-dimensional carriers it chooses an exact basis
of the universal old equalities, enumerates all triples of new inequalities,
solves the resulting square rational system, and checks feasibility against
all new inequalities. This enumerates the vertices of R within aff(H), not a
floating-point approximation to R and not an induced subgraph pretending to
be a relaxation. It checks that every relevant interior vertex is among those
vertices and that their number is at most 2m-2. The actual parent-edge routes
from the main suite satisfy every refined endpoint and pair budget.

Two complete independent executions reproduced the output byte-for-byte:

    SHA-256: 6ae805853a90ac7d08b1fc381c9713fab12adcb058512379d5f85439c00a4f6e

These tests do not prove Euler's formula or the universal geometric theorem.
Their role is to validate the concrete carrier count, the relaxation boundary,
and the emitted routes in the examples. The general proof is given above.
No literature-priority claim is made.
