# Compact models are not ordinary-edge routing certificates

## Delivery and scope

PR #241 commits the existing bounded-image representative packet at
90f7d8a7acd078558e18df0737d20014ef80b0e5. Its publication-comment call was
blocked before posting, and the subsequent comment readback was empty. No
compilation, axiom audit, registration or platform verdict is asserted.
The 398-line mathematical source is unchanged. This note and the new exact
regression do not upgrade that status or constitute a new public theorem.

## A concrete obstruction to the wrong diameter inference

The classical construction in Gärtner, Helbling, Ota and Takahashi,
*Large Shadows from Sparse Inequalities*, arXiv:1308.2495 (Definition 11,
Lemma 12), provides a compact d-dimensional Klee–Minty cube with 2d facets
whose planar projection retains all 2^d vertices. The source is the primary
research paper, https://arxiv.org/html/1308.2495, not a secondary summary.

We use epsilon=1/4 and rows

    0<=x_1<=1,
    epsilon*x_(j-1)<=x_j<=1-epsilon*x_(j-1).

Project using (c.x,x_d), with c_j=epsilon^(3(d-j)) for j<d and c_d=0.
The regression derives exact original-row positive exposing multipliers for
individual vertices and independently reconstructs the entire image polygon
in dimensions 2 through 12. The all-dimension shadow property is classical,
not a result newly inferred from those finite computations.

Here is the consequence relevant to this project. Encode a source vertex by
its lower/upper choices. The reflected binary ordering by x_d places the
all-zero vertex at position0 and the choice with its last TWO bits1 at
position2^(d-1). These are opposite vertices of the polygon. In the original
cube, however, flipping just the last bit and then the penultimate bit gives
a TWO-edge route between them. The second step projects to an interior chord
for d>=3, not an edge of the image.

The all-dimension distance claim does not rest on extrapolating the tests.
Inductively, appending a zero bit sends all previous heights monotonically
into [0,epsilon], while appending a one bit sends them in reverse order into
[1-epsilon,1]. These intervals are disjoint, so the reflected ordering is the
strict height order. The classical exposing normals all have first planar
component +1, putting every projected vertex on the right boundary chain.
The left boundary is therefore just the edge joining the height extremes.
The first vertex of the upper reflected block is the bit vector whose last
two bits are one, at boundary index 2^(d-1). The cycle distance is consequently
exactly half its 2^d vertices, while the source cube path flips just two bits.

At d=12, the extension has24 facets and the requested source-graph distance
is2. The image has4096 genuine facets and the requested image-graph distance
is2048. This is not a Hirsch counterexample: using24 as the image facet count
would be incorrect. Nor does it contradict the special Minkowski edge-lift
results #239/#240. It shows why an arbitrary compact coefficient model cannot
be substituted for their specific decomposition/support hypotheses.

The obstruction survives even when every extension vertex is visible and the
projection is injective on vertices. Checking vertex correspondence alone is
therefore insufficient to transport graph routes.

## Positive certificate: when a lifted step really is an image edge

Let Q={x:A_i x<=b_i} be bounded and let x,y be independently verified adjacent
vertices. Write J for their common active rows, whose rank is d-1. Suppose
Gx!=Gy and there is a linear functional f on the IMAGE coordinates and
strictly positive lambda_j for j in J such that

    G^T f = sum_(j in J) lambda_j A_j.

For every u in Q, f(Gu)<=sum lambda_j b_j, with equality exactly when ALL J
rows are tight. That whole equality face is [x,y]. Therefore the exposed face
of GQ is exactly G([x,y])=[Gx,Gy], a nondegenerate ordinary edge. This proves
the step without inspecting any other projected vertex or constructing the
image's full inequality description.

The new producer tests the two possible planar normal orientations. Its
independent auditor binds the projected endpoints to the original coordinates,
checks the original positive support identity, and checks the common-row
triangular rank certificate. An exact planar hull separately confirms which
original edges are accepted. It does not assume that every extension edge
must pass this test. This is a sufficient exact step certificate, not an
existence theorem promising a short sequence of such steps.

## Executed evidence

Across dimensions2..12, every vertex and original cube edge is enumerated:
8188 exposed-vertex certificates,45056 original edges,8188 certified image
edges, and36868 original edges correctly rejected as projected chords. For
dimensions2..5,1360 independent all-point objective comparisons also confirm
strict exposure. Eight corrupt/invalid cases are rejected, including an actual
extension edge falsely presented as an image edge and altered image coordinates.

At dimensions16,32,64, only11 selected original support certificates per case
and the two-edge extension path are checked. The enormous image counts and
distances in those rows are consequences of the cited classical construction,
NOT enumerated data. The largest fully reconstructed image is the4096-gon.

Run `python3 scripts/test_projection_edge_gap.py` from the repository or full bundle.
The receipt is PROJECTION_EDGE_GAP_TESTS.json. This test is exact rational
computation, not Lean compilation or an extracted/verified Python program.

## What the pending representative theorem does usefully preserve

Its support/tight-row preservation implies a stronger facewise statement:
when the whole image is bounded, the SAME chosen mass cap preserves the image
of every face specified by original tight resource and coordinate rows.
For any point in such a face, choose its promised representative; all defining
equalities stay tight, so it remains in that face. The other inclusion is
immediate. This written corollary depends on the pending theorem and is not
separately compiled or published.

Even this facewise image equality must not be confused with a short-route
statement. The compact counterexample above already has every source face
available. What is missing is a polynomial count of ORIGINAL image-edge
certificates along the needed route.

The next geometric target should exploit the accepted genuine Minkowski
bridge/sweep structure or another original-edge-preserving construction.
A small number of auxiliary rows, a bounded fiber representative, or a short
coefficient-space route alone cannot discharge the arbitrary-carrier theorem.
