# A concrete original-H exponential zonotope-completion obstruction

## Current formal status

PR #320 is OPEN/DRAFT: complete Lean proof and transitive axiom audit PASS;
Prove2Me publication is blocked before registration by the trusted-main protocol
version guard. Frozen proof 2efb69e4e25165bfd2a5abc2fe2673d950114ab9 passed run
35624792380 after the exact saved two-site Fin.ext repair. Driver, solution and
separate target statement all exited 0; every one of six proof axiom reports lists
only propext, Classical.choice and Quot.sound. No platform ACCEPTED or Proved
result exists from this run. Read TRIANGULAR_COMPLETION_HANDOFF.md for exact
request, artifact, source-hash and blocker evidence. The prior failed mathematical
note and handoff are preserved under verification/triangular-completion/repaired-attempt/.

## Explicit small original presentation

Let 0<e<1/2 and let P in R^(n+1) be defined by

    0 <= x_n <= 1,
    e*x_(i+1) <= x_i <= 1-e*x_(i+1)  for 0<=i<n.

There are 2(n+1) displayed scalar inequalities. Backward induction derives every
redundant coordinate bound 0<=x_i<=1. The proof establishes equality with the
accepted triangular feasibility predicate; it does not take an enlarged list as
its original size parameter. It does not claim a separate Mathlib facet-lattice count.

For a feasible tail y, the two possible head endpoints are affine functions
L(y)=e*y_0 and U(y)=1-e*y_0. Their difference is positive. Every feasible head is
a convex combination of these endpoints over the same tail. Inductively write
the tail as a convex combination of constructed Boolean corners, and distribute
that combination through the two affine boundary lifts. Conversely all corners
are feasible and the original body is convex. This proves the ENTIRE body is
that finite convex hull, rather than merely placing a selected point list in it.
The complete hull_eq_body proof compiles with standard-only axioms.

## Construct an exponential family of whole original edges

Choose bits b_0,...,b_(n-1). Put x_n=t and recursively set

    x_i=e*x_(i+1)          when b_i=0,
    x_i=1-e*x_(i+1)        when b_i=1.

For 0<=t<=1 this gives a feasible affine segment, with distinct endpoints because
the last coordinate changes from 0 to 1. Sum the n chosen ORIGINAL row functionals:
-x_i+e*x_(i+1) for a lower choice, x_i+e*x_(i+1) for an upper choice. Each is bounded
above by its original right-hand side. Equality in their sum forces every chosen
row tight, hence gives exactly the displayed affine segment and no other feasible
points. Thus the sum exposes the WHOLE edge, not just its endpoints or a chord.
The supporting_line base case now explicitly proves the Fin(0+1) index equality;
the entire exposed_line proof compiles with standard-only axioms.

Let delta_b=line_b(1)-line_b(0). Then

    delta_b(n)=1,
    delta_b(i)=(if b_i then -e else e)*delta_b(i+1).

Every component is nonzero. If delta_a=c*delta_b, the last coordinate forces c=1.
Cancel each nonzero following component to recover every bit, so a=b. This yields
2^n pairwise distinct UNORIENTED original edge directions. The directions_separate
proof compiles with standard-only axioms. We do not need or claim the stronger
exact count 2^(n+1)-1 of all edge directions from the earlier written note.

## Verified application to arbitrary actual completions

For any nonempty compact Q satisfying ACTUAL whole-set equality
P+Q=Z=sum_i[0,w_i], apply accepted #319 to the derived finite hull and these 2^n
original edges. That theorem derives an injection into distinct nonzero generator
directions and constructs opposite actual completion vertices such that every
walk through nondegenerate whole exposed Z segments requires at least 2^n steps.
The complete theorem proves 2^n<=m as well as this intrinsic path lower bound.
Q convexity is unnecessary. The original H family, scalar range, compactness,
nonemptiness and actual sum equality remain structural premises; no corner,
edge, matching or count oracle is inserted. The full public solution compiles.

In dimension d=n+1 the sufficient lower bound is 2^(d-1), with 2d displayed input
inequalities. At d=8 this is 128; at d=16 it is 32768. These are evaluations of the
all-dimensional formula, not enumerations of the large completion graphs.
A separately formalized asymptotic domination theorem, translation transport,
exact original shortest diameter and facet-lattice count are not included.

This is a lower bound for the COMPLETION, not for P. It therefore does not refute
Polynomial Hirsch. Charging only steps that survive contraction, using other
geometric classes, or finding a different original-edge argument remain possible.
Classical triangular/Klee-Minty background is credited in the unchanged packet to
Gaertner, Helbling, Ota and Takahashi, Large Shadows from Sparse Inequalities,
arXiv:1308.2495; no historical-priority or new best classical diameter bound is claimed.

## Evidence separation and next obligation

The source reuses exact accepted #319 and #280 namespace bodies with old public
roots omitted, not resubmitted. The full public statement and proof assembly,
metadata and hypotheses are unchanged. Only two finite-index equalities changed;
all formerly failed dependent proofs now compile without sorryAx.

The separate statement.lean target placeholder is not a proof and its expected
sorry warning is not the source of verification: driver.lean and solution.lean
both compile completely and their full-root transitive axiom audits pass.
The earlier exact-rational regression remains supporting evidence; it was not
rerun in this continuation and is not substituted for the hosted Lean evidence.

The next blocker is a separately reviewed official protocol compatibility update
on trusted main, not another proof repair, enlarged inventory bound or duplicate
obstruction theorem. Preserve exact verified bytes and all security safeguards.
