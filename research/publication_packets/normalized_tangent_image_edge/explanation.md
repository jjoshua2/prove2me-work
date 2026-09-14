# From a normalized tangent image to a genuine original-image edge

## Exact formal statement and what is not assumed

The target is Hirsch.normalized_tangent_slice_lifts_to_image_edge. It works
with a finite original H-system P={z:a_i(z)<=b_i}, a linear map G and a feasible
anchor x. The anchor is tight on precisely J. Finite positive weights and an
image-row factorization provide

    h G = -sum_(i in J) lambda_i a_i,    lambda_i>0,
    G(v) = sum_(i in J) a_i(v) W_i.

Thus h is positive on every nonzero projected active-cone direction, even when
that source cone has lineality. Given a uniquely exposed point r of the
height-one IMAGE tangent slice, h(r)=1, and an attained maximal ray endpoint
G(y)=G(x)+tau*r, tau>0, the theorem constructs the ORIGINAL image exposer

    ell = f-f(r)h.

Its entire support slice on G(P) is exactly [G(x),G(y)]. That segment is
nondegenerate and an actual Mathlib IsExtreme subset; any objective c with
c(r)>0 strictly improves along it. Neither source vertexhood, source adjacency,
one-dimensional source face, source compactness, nor a supplied original-image
edge or exposer occurs as a hypothesis. Lower-dimensional images are allowed.

The theorem also proves the exact active-cone image equality

    G{v:a_i(v)<=0 for i in J}
      = {s*(G(z)-G(x)):s>=0,z in P}.

It does not merely use a tangent-cone closure identity or assume that a vector
satisfying some active rows is actually realizable. Finite strict slacks
construct a small positive feasible step for EVERY such vector.

The normalized-slice support and maximality over all lifts remain explicit
witness interfaces in the formal statement. They are not claimed to be
constructed by this Lean file. In the accompanying executable method, #247's
fibre-dual construction supplies the slice support, and exact primal/dual
certificates supply the maximal ray length. Finite column identities specialize
the quantified linear-map identities via the accepted #246 basis principle.
The Python producer/parser/LP implementation is not Lean-extracted, and the
full algorithm's termination is not a new formal theorem in this packet.

## Proof of the edge implication

For v in the active cone, h(Gv)=sum lambda_i*(-a_i(v))>=0. If this is zero,
every selected a_i(v) vanishes, and the image-row factorization gives Gv=0.
For positive height t, divide v by t. The normalized-slice support bound gives
f(Gv)<=t*f(r). Equality forces Gv=t*r. Therefore ell<=0 on the whole image
cone, with equality precisely on the selected nonnegative ray.

Every original feasible z has z-x in that cone. Consequently ell supports
G(P) at G(x), and equality forces G(z)=G(x)+s*r with s>=0. The all-lift ray
maximum gives s<=tau. Conversely convex combinations of the actual feasible
lifts x,y realize every point of the asserted segment. This proves BOTH
inclusions of the entire exposed slice, not just the feasibility of a line.
The support-slice extremeness argument is the same elementary proof as #246.

## Constructing the inputs without a supplied neighboring vertex

The new software takes A,b,G and two image endpoint vertices u,v. It first
constructs the strict image target objective c via the accepted #247 fibre
method. It separately certifies boundedness of the IMAGE by dual bounds on
both signs of every G-coordinate. The source may have unbounded fibres and
no vertices at all.

At each current image vertex u:

1. Find its fibre's forced original rows, a feasible anchor strict off those
   rows, and an image exposing normal. Check G=W A_J by finite columns.
2. Reverse the normal to get the positive height h, and consider the source
   system A_J d<=0, h(Gd)=1. Its image is a compact vertex figure even when the
   source normalized system is unbounded. Indeed if s_i=-a_i(d), then
   sum lambda_i*s_i=1 and Gd=sum (lambda_i*s_i)*(-W_i/lambda_i), so the image
   lies in a finite hull. This is only a CONTAINMENT; not every listed hull
   point is realizable, and there is no resulting m-bound on the ray count.
3. Maximize c(Gd), then successively maximize each image coordinate on the
   previously optimal face. There are p+1 exact optimization certificates.
   The final image point is unique, hence an extreme point of the normalized
   image slice. The source point itself need not be unique or extreme.
4. Reapply #247 to that slice and final image point r, obtaining the actual
   slice exposer f. The source image-row factorization checks that the entire
   selected support face has the singleton image r.
5. Maximize tau over ALL original lifts z satisfying Gz=u+tau*r and tau>=0.
   The target direction supplied a feasible normalized start, and strict
   slacks guarantee a positive original step. Bounded image gives finite
   attained ray length. Exact primal/dual equality certifies this length.
6. Apply the tangent-to-edge argument. Repeat at the new image vertex until
   the requested target. Strict objective improvement forbids revisits.

There is no original/source graph or neighboring image vertex input. On a
bounded polyhedral image, finitely many vertices and strict improvement give
finite mathematical termination when the exact subroutines complete. The
implementation has explicit LP and route caps. Neither a polynomial iteration
count, strongly polynomial algorithm nor a polynomial Hirsch diameter bound
is claimed. The number of auxiliary LP pivots is distinct from the number of
actual original-image edges returned. Facet budgets for the conjecture must
still count ORIGINAL IMAGE facets, never extension rows.

## Two shortcuts specifically excluded

An optimal normalized direction need not be an extreme ray. In the square's
positive-quadrant cone with h=x+y and c=x+y, (1/2,1/2) is an optimal slice point
but leads to the square diagonal. The unique-image-ray check rejects it; the
image-coordinate refinement instead selects an actual ray. This is consistent
with the classical distinction between ascent directions and edge directions.

A single source ray can stop before the image edge ends. In [0,1]^2 mapped by
(z1,z2)->z1+z2, a chosen direction increasing z1 alone hits z1=1 while its image
can continue to2 by increasing z2. The maximal-length LP therefore ranges over
all lifts, not x+tau*d. Adding a free source coordinate destroys all source
vertices without changing that image or the successful selection.

## Executed evidence and its limits

The completed regression checks297 route certificates/428 original-image edge
occurrences. Nine independently reconstructed small hulls have49 image vertices,
62 edges and291 ordered distances. All291 ordered endpoint pairs are routed;
1012 independent incident-edge comparisons verify the chosen normalized slope
is maximal. The small source graphs contain32 edges that do NOT project to
image edges. Two returned pentagon routes are nonshortest, explicitly retained.

Six additional cases cover paired-coordinate cube images in dimensions2,4,8,
source lineality/no source vertices, a2^-120 thin projection, a lower-dimensional
image and a hidden dense affine source chart. They return20 edges, including
12 occasions where a fixed-source ray would stop prematurely and18 source-lift
steps that are not source edges. Twenty malformed/capped cases are rejected.
The auditor still passes with all LP/discovery/elimination entry points disabled.
These results are exact software tests, not individually kernel-checked JSON.

## Provenance and verification discipline

Base main f9d96dd153a0b880bc26cbc28f00911f2dd8d642 includes the newly accepted
#241 bounded-image representative theorem; that result is not reproved here.
The old #247 and #246 source/receipts remain unchanged. #244's owner retains
the distinct Minkowski core-walk assembly. No workflow, pin, secret or permission
change is part of this continuation.

The finite slack proof is adapted from #247's accepted local_kernel_steps,
replacing selected equalities of the direction by one-sided inequalities.
The image-cone and normalized-to-original-edge connections are the new formal
interfaces. The normalized slice support itself uses #247, not a new generic
strict-support existence theorem competing with #238.

Local Lean/Lake is unavailable and public toolchain DNS failed in this runtime.
The285-line standalone source and its exact type-matched Mathlib-only metadata
are prepared for the guarded final compilation/axiom/publication flow. Five
explicit axiom printouts cover the proof chain. Until that actual gate returns,
the code is an uncompiled candidate; Python success is not compilation.

## Classical primary background

Ken Clarkson, CIS677 lecture7, convexity and cone/slice correspondence:
https://kenclarkson.org/cis677/lecture/7/index.html

E. Andrew Boyd (1995), Resolving degeneracy in combinatorial linear programs:
steepest edge, steepest ascent, and parametric ascent, Mathematical Programming68,
155--168, DOI10.1007/BF01585762. The distinction between an ascent direction and
an actual edge direction is important here; no priority for standard vertex-figure
geometry or a new worst-case bound for a simplex pivot rule is claimed.
