# Removing supplied objectives from the zonotope route theorem

Let Z be the original coefficient sum of segments [0,w_i] for arbitrary real
generators. The proposed theorem connects any two ACTUAL extreme points with at
most m original exposed edges. Unlike accepted #315, it does not take regular
exposing objectives as inputs. The complete Lean packet still has two reported
elaboration errors; this note is a written argument, not a platform verdict.

## A finite hull without assuming a vertex catalogue

Define C as the images of all Boolean coefficient vectors. Some corner images
can be duplicated or fail to be vertices. Nevertheless, the parallelepiped hull
identity proves Z=convexHull(C). If u is extreme in Z, then Z minus {u} is convex.
Thus convexHull(C minus {u}) is contained in Z minus {u}, excluding u. A finite
convex hull is closed, so strict separation gives a linear f with f(x)<f(u) for
every corner image x different from u. This constructs the objective instead of
assuming it or assuming a list of all actual vertices. Both the hull equality
and this separator helper produced standard-only axiom reports in the first gate.

## Why the objective is regular on all nonzero generators

The canonical saturated corner V(f)=sum_(f(w_i)>0)w_i reaches the full support
value sum_i max(0,f(w_i)). The feasible point u cannot have a larger value, while
strict separation excludes a different corner with value at least f(u). Hence
V(f)=u. If a nonzero generator w_i had f(w_i)=0, its saturated coefficient would
be zero. Toggling that coefficient to one gives another corner V(f)+w_i with
exactly the same objective value. Strict separation would force w_i=0, a
contradiction. Thus f is regular, and the accepted saturation result proves its
WHOLE maximizing face is {u}.

Repeat independently for v. The accepted regular-objective route then has the
requested singleton endpoint faces and at most m genuine original exposed/extreme
segments. Identifying its singleton endpoints with u and v completes the written
all-pairs argument. No arbitrary projection or Boolean-cube edge is substituted
for an original edge.

## Formal status and remaining quantitative boundary

The first hosted gate checked the hull and separator helpers, but failed in the
binary update-self case and the introduction of the public theorem's let-bound
body. A separate uncompiled repair replaces the first branch with simp and reduces
the public let before introducing the two extremality proofs. The complete
regularity/route chain still has failed-elaboration sorryAx; no new ACCEPTED or
live Proved result is claimed. The tested publication source remains unchanged.

The proposed theorem includes zero, repeated, parallel, opposite and rank-deficient
generators, d=0,m=0 and equal endpoints. Its m is generator count, not the original
polyhedron's H-facet count. The finite Boolean hull is used only for mathematical
existence and does not supply efficient enumeration or extraction. A completion
with exponentially many generators still does not yield a polynomial original-input
bound. This is a classical zonotope bound, not a historical-first, shortest-path
or unrestricted Polynomial Hirsch claim.

The exact rational tests separately discover all small planar vertices, derive
objectives, and check full faces and routes. Their reports and fixture replay are
supporting computations, not Lean verification; see the handoff for precise counts,
raw failure evidence, and the next two-site compilation repair.
