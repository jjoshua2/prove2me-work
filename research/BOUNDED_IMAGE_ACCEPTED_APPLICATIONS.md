# Using accepted #241 without confusing representation and routing

The bounded-image representative theorem is now accepted. This note derives
some immediate mathematical consequences and identifies where they may be used.
These are written deductions from the accepted theorem, NOT separately
Lean-compiled or published declarations and not an alternative core-walk PR.

## A single strictly slack cap works on every original equality face

Let X={x>=0:Bx<=t}, with norm(Gx)<=M on X, and let C be the constant supplied
by #241. Choose

    R=C*(norm(t)+M)+1.

For any subsets I of coordinates and J of resource rows, define

    F_IJ={x in X: x_i=0 (i in I), (Bx)_j=t_j (j in J)}.

For every x in F_IJ the theorem produces y in the SAME F_IJ, with Gy=Gx and
sum(y)<=R-1. Thus, simultaneously for ALL choices I,J,

    G(F_IJ)=G(F_IJ intersect {sum(y)<=R-1})
            =G(F_IJ intersect {sum(y)<=R}).

The reverse inclusions are immediate. The same R works for every face; this
does not require a separate constant or enumeration of those faces. Empty
faces are included. The one-unit strict slack is a chosen margin in coefficient
space, not an invariant of the original geometry or a condition-number bound.

Consequently any attained image-objective maximum has a feasible maximizing
coefficient representative with the artificial cap STRICTLY slack. If an exact
nonnegative primal-dual certificate for the capped model is available, rowwise
complementarity forces its cap multiplier to be zero. The cap can then disappear
from that certificate. This observation does not itself prove existence of
those multipliers; the owner of #238 controls that support-witness obligation.
It must not be used as a new circular strong-duality premise.

## The helper also gives closedness of finitely generated positive cones

For a continuous linear A from a finite coordinate space to a normed space,
the accepted helper supplies C and nonnegative representatives y for Ax with
sum(y)<=C*norm(Ax). Suppose a sequence z_n in A(nonnegative orthant) converges
to z. Select corresponding nonnegative preimages and replace them by these
bounded representatives. Their masses are uniformly bounded because the z_n
converge. The representatives therefore lie in one compact nonnegative box.
A convergent subsequence has nonnegative limit y, and continuity gives Ay=z.
Hence A(nonnegative orthant) is closed.

This is a classical result and a written corollary here, not a new priority
claim or another published theorem. If useful, it can remove a closed-cone
assumption from a future separation argument. Do not overwrite concurrent
support-witness work or claim a general Farkas theorem was already added.

## Where this stops relative to Polynomial Hirsch

The representation step adds one inequality and does not alter the represented
image, but it can neither preserve arbitrary coefficient edges nor control
the length of image routes. The numerical value of R also has no implication
for graph diameter: changing coordinate scale can make it arbitrarily large
without changing the graph.

The current geometric chain for a SUPPLIED decomposition Q=P+sum_i Q_i aims
at L+(L+1)*K, where L is a supplied core-route length and K=sum_i(|V_i|-1).
The core-walk concatenation is already owned elsewhere; don't duplicate it.
The genuine applicability task is to bound L and K by a uniform polynomial in
the original carrier's facet count/dimension, or to find a different original-
edge construction. A vertex list for an arbitrary summand may be exponential;
a finite decomposition or complete circuit catalogue alone does not control K.

A useful non-tautological witness of progress would be a geometrically defined
class of actual selected carriers for which such a decomposition and polynomial
budgets are proved automatically, or a quantitative invariant that controls
repeated original-row charges across the remaining high-dimensional repairs.
Supplying a desired route or a desired polynomial budget as an input and then
summing it is not the missing geometry.

Current tasks must be selected from live STATUS and PR comments. #241 is no
longer pending. #246's image-step certificate, #247's face discovery and the
separate core-walk assembly remain distinct; this note changes no ownership.
