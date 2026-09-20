# A concrete original-H exponential zonotope-completion obstruction

## Current formal status

PR #320 is OPEN/DRAFT. Its first complete compiler attempt35518652354 failed at
two finite-index elaboration sites. The full-hull and direction-separation helpers
reported standard-only axioms, but four dependent reports contain failed-elaboration
sorryAx. The complete public theorem is NOT verified, submitted to the platform,
ACCEPTED or Proved. The saved repair is separate, unapplied and uncompiled.
Read TRIANGULAR_COMPLETION_HANDOFF.md and the scoped compiler diagnostics.

## Explicit small original presentation

Let0<e<1/2 and let P in R^(n+1) be defined by

    0 <= x_n <= 1,
    e*x_(i+1) <= x_i <= 1-e*x_(i+1)  for0<=i<n.

There are2(n+1) displayed scalar inequalities. Backward induction derives every
redundant coordinate bound0<=x_i<=1. The candidate proves equality with the accepted
triangular feasibility predicate; it does not take an enlarged list as its original
size parameter. It does not claim a separate Mathlib facet-lattice count.

For a feasible tail y, the two possible head endpoints are affine functions
L(y)=e*y_0 and U(y)=1-e*y_0. Their difference is positive. Every feasible head is
a convex combination of these endpoints over the same tail. Inductively write
the tail as a convex combination of constructed Boolean corners, and distribute
that combination through the two affine boundary lifts. Conversely all corners
are feasible and the original body is convex. This proves the ENTIRE body is
that finite convex hull, rather than merely placing a selected point list in it.
This hull_eq_body helper has an actual standard-only compiler report.

## Construct an exponential family of whole original edges

Choose bits b_0,...,b_(n-1). Put x_n=t and recursively set

    x_i=e*x_(i+1)          when b_i=0,
    x_i=1-e*x_(i+1)        when b_i=1.

For0<=t<=1 this gives a feasible affine segment, with distinct endpoints because
the last coordinate changes from0 to1. Sum the n chosen ORIGINAL row functionals:
-x_i+e*x_(i+1) for a lower choice, x_i+e*x_(i+1) for an upper choice. Each is bounded
above by its original right-hand side. Equality in their sum forces every chosen
row tight, hence gives exactly the displayed affine segment and no other feasible
points. Thus the sum exposes the WHOLE edge, not just its endpoints or a chord.
The written argument is complete; its supporting_line Lean base case still needs
the explicit Fin(0+1) equality repair preserved separately.

Let delta_b=line_b(1)-line_b(0). Then

    delta_b(n)=1,
    delta_b(i)=(if b_i then -e else e)*delta_b(i+1).

Every component is nonzero. If delta_a=c*delta_b, the last coordinate forces c=1.
Cancel each nonzero following component to recover every bit, so a=b. This yields
2^n pairwise distinct UNORIENTED original edge directions. The directions_separate
helper has an actual standard-only compiler report. We do not need or claim the
stronger exact count2^(n+1)-1 of all edge directions from the earlier written note.

## Complete intended application to arbitrary completions

For any nonempty compact Q satisfying ACTUAL whole-set equality
P+Q=Z=sum_i[0,w_i], apply accepted #319 to the derived finite hull and these2^n
original edges. That theorem derives an injection into distinct nonzero generator
directions and constructs opposite actual completion vertices such that every
walk through nondegenerate whole exposed Z segments requires at least2^n steps.
The complete target thus asserts2^n<=m as well as the intrinsic path lower bound.
Q convexity is unnecessary. The original H family, scalar range, compactness,
nonemptiness and actual sum equality are the only pertinent structural premises;
no corner/edge/matching/count oracle is inserted.

In dimension d=n+1 the sufficient lower bound is2^(d-1), with2d displayed input
inequalities. At d8 this is128; at d16 it is32768. These are evaluations of the
intended all-dimensional theorem, not enumerations of the large completion graphs.
A completed proof would close the explicit-family part of the global completion
obstruction. An asymptotic domination theorem, translation transport, exact original
shortest diameter and facet-lattice count are not included in this packet.

This is a lower bound for the COMPLETION, not for P. It therefore does not refute
Polynomial Hirsch. Charging only steps that survive contraction, using other
geometric classes, or finding a different original-edge argument remain possible.
Classical triangular/Klee-Minty background is credited to Gaertner, Helbling, Ota
and Takahashi, Large Shadows from Sparse Inequalities, arXiv:1308.2495; no
historical-priority or new best classical diameter bound is claimed.

## Evidence separation and next repair

The new source includes exact accepted #319 and #280 namespace bodies with old
public roots omitted, not resubmitted. Its full public statement and proof assembly
remain unchanged after the failed gate. Only two reported finite-index sites need
the saved proposal: explicit Fin.ext value equalities in supporting_line and
minimal_eq_body. Further errors may appear after that uncompiled repair.

Exact rational tests cover18 complete small H models,189 selected edges,54 whole-body
convex reconstruction certificates, selected larger edge certificates and independent
active-system/support checks. Serialized audits run without construction routines,
and malformed controls are rejected. Clean replay reproduces the complete outputs.
They are supporting tests, not a replacement for a complete Lean build and audit.
