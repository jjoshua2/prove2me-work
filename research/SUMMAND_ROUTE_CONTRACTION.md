# Safe route transfer under actual Minkowski decomposition

## What this contributes after the moment-family route

The accepted moment theorem supplies actual exposed-edge walks in one structural
class. Transporting those walks through an arbitrary linear projection is not
safe: source edges can become interior diagonals. The present candidate isolates
a different transfer that is geometrically sound for actual convex Minkowski
summands. This is reverse transfer, not the earlier fibre-lifting construction.
Its complete Lean source remains blocked at two elementary tactic sites; consult
the handoff and failure record rather than treating this written argument as an
ACCEPTED platform result.

Let R=P+Q={p+q:p in P,q in Q}. For each actual extreme point z of R, any
representation z=p+q has p extreme in P and q extreme in Q. A nontrivial convex
decomposition of a component would translate to one of z. The representation
is unique: if z=x+y also, then z is the midpoint of x+q and p+y, both in R.
Extremality gives x+q=z and hence x=p,y=q. This argument needs no finite point
list, rank witness or maximizing-objective oracle.

## Why an entire sum edge gives entire component faces

Let [z0,z1] be a nondegenerate exposed face of R, with z0=p0+q0,z1=p1+q1.
Take a continuous linear functional f exposing exactly that sum segment.
Comparing x+q0 with z0 shows f(x)<=f(p0) for all x in P, and similarly for Q.
Equality of f(z0) and f(z1) forces both endpoint components to attain their
factor maxima. All cross-sums of component maximizers therefore lie in [z0,z1].

Write D=z1-z0. The cross-sum p1+q0 gives

    p1-p0=alpha D,  0<=alpha<=1,
    q1-q0=(1-alpha)D.

Now let x be ANY maximizer of f in P. Both x+q0 and x+q1 are in the whole sum
segment, so write them as z0+sD and z0+tD with s,t in [0,1]. Subtraction and
D!=0 give t=s+1-alpha. Therefore 0<=s<=alpha. If alpha=0, x=p0. Otherwise
x=p0+(s/alpha)(p1-p0), so x is on [p0,p1]. Convexity proves the reverse inclusion.
Thus the whole P-support face equals [p0,p1], not just some subsegment containing
the endpoints. Swap P,Q for the other factor. The same objective exposes both.

At alpha0 or alpha1 one factor is stationary; at intermediate alpha both move
in the same direction. Cancellation cannot disguise a diagonal. A nonstationary
component is a nondegenerate exposed segment and therefore an original edge.

## Compress the finite walk, with no extra cost

Apply the unique decomposition to every vertex z_i of a given actual sum walk.
The preceding result gives a_i=a_(i+1) or a genuine factor edge, and likewise
for b_i. Delete consecutive equal points separately. The accepted finite
schedule-compression lemma proves that endpoints and all genuine edges are
preserved and that each factor walk has length at most N.

The bound is per factor, not on the sum of their lengths. For two parallel
segments a single sum edge can yield one edge in each summand. A point summand
can instead lose every step and give a zero-edge route. Repeated vertices and
nonshortest paths are allowed, because only consecutive stationary transitions
are removed. Zero-dimensional and zero-length cases are included.

## Precisely what is and is not assumed

The theorem assumes convex P,Q and an actual finite exposed-edge vertex walk
in their exact Minkowski sum. It constructs component vertices, uniqueness,
support faces, cooriented coefficients and compressed original-edge walks.
It does NOT assume any of those component objects as certificates.
No boundedness, compactness, closedness, finite-hull, full-dimensionality or
simplicity premise is needed.

To turn this into a uniform diameter transfer for independently specified
factor endpoints, one still needs suitable sum-vertex lifts and a controlled
route between them. To use a tractable sum as a universal model for arbitrary
polytopes, one also needs existence and a controlled original-facet budget for
that model. None of those tasks is solved or silently included here. In
particular this is not an unrestricted Polynomial Hirsch proof.

A concrete negative control separates this from arbitrary projection: under
(x,y,z)->(x+z,y+z), the simplex conv(0,e1,e2,e3) maps to a square, but its edge
[e1,e2] maps to the diagonal [(1,0),(0,1)], not an exposed square edge.

The contraction phenomenon and diameter consequences for polytopes are
classical; see Antoine Deza and Lionel Pournin, Diameter, decomposability,
and Minkowski sums of polytopes, arXiv:1806.07643, Canadian Mathematical
Bulletin62(4),2019,741-755, DOI10.4153/S0008439518000668. This project contribution
is a formal whole-face and route-transfer interface, not historical discovery.

## Executed finite checks

The standalone exact-rational script constructs convex hulls independently for
P,Q and all pointwise sums, checks unique vertex pairs, and tests every cyclic
sum edge against all listed component points. Both orientations of every
endpoint pair are contracted. The 56 models give 10,270 walks and 47,122 original
sum-edge occurrences, contracting to 24,894 and 23,454 factor edges. Stationary
and simultaneous cases are both retained. Twelve larger product examples reach
dimension64 without vertex enumeration. Eighteen serialized edge records pass
with all discovery routines disabled; five corruptions are rejected.

These are finite tests, not a universal proof by samples, not a formal Python
implementation, and not substitutes for full pinned Lean compilation. The
complete report and fixture are supplied with the bundle and reproduce
byte-for-byte from the committed script.
