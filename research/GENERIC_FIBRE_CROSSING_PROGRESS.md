# From generic objectives to genuine exposed-edge transitions

## 1. What is established

PR #242 closes two concrete interfaces in the simultaneous Minkowski fibre construction. The generic-objective theorem is ACCEPTED and live Proved in the publisher receipt. The new per-crossing module passes Lean compilation; its successful module-only gate does not retain an independent axiom audit. Read the separate receipts rather than conflating these statuses.

The previously accepted #239 theorem counts a supplied sequence of unique affine maximizers and turns GLOBAL supporting-segment certificates into ordinary edges. Accepted #240 constructs bridges over exposed core edges. The missing fibre argument requires both generic objectives and a proof that their transitions really expose segments, not diagonals of higher-dimensional faces.

## 2. Generic objectives are constructed, not assumed

Let C0,C1 be finite lists of strict endpoint comparison vectors. Given objectives strictly negative on these lists and a finite list D of nonzero within-factor differences, first perturb the first objective to avoid D while preserving C0. For nonparallel d,e, the vector f(d)e-f(e)d is nonzero. Perturb the second objective inside C1 so it avoids D and every such vector. The two-by-two determinant f(d)g(e)-f(e)g(d) is then nonzero.

If F_t=(1-t)f+t*g annihilated both d and e, elementary elimination would force that determinant to zero. Therefore all nonzero simultaneous tie directions are parallel. The theorem covers every real t and arbitrary real vector spaces, without a normal-fan genericity oracle or finite ambient-dimension premise. Shared strict core comparisons remain negative for 0<=t<=1.

## 3. The whole supporting segment is derived

Consider finite component sets S_i. Let p_i be a left-objective maximizer and q_i a right-objective maximizer, both maximizing a wall objective. Choose a changed component c and set e=q_c-p_c. Strict left/right comparisons give left(e)<0<right(e). The no-independent-ties condition puts every wall-maximal difference x-p_i in span(e).

Normalize a linear coordinate tau by tau(e)=1. Write q_i=p_i+eta_i*e and any wall-maximal point x=p_i+z*e. The left comparison forces z>=0 and eta_i>=0; the right comparison forces z<=eta_i. Thus ALL listed wall maximizers lie in the segment [p_i,q_i], and both endpoints are listed maximizers. The already-proved finite-hull support lemma upgrades this to equality of the ENTIRE supporting slice of conv(S_i).

The changed component satisfies eta_c=1, so sum eta_i>=1. There can be no cancellation into a stationary total transition. The existing sum-of-support-slices and parallel-interval lemmas yield

    supportFace(sum_i conv(S_i), wall) = [sum_i p_i, sum_i q_i],

with distinct endpoints. The existing supporting-face extreme-subset theorem then gives `Hirsch.Adj`. Whole-slice equality and nondegeneracy are conclusions, not input certificate assumptions.

Stationary factors, parallel simultaneous changes, lower-dimensional hulls and redundant listed points are retained. A rank-two simultaneous face fails the tie hypothesis and cannot be certified as its diagonal.

## 4. Exact next formal assembly

For finite S_i and two endpoint tuples sharing the same strictly exposed core vertex, instantiate #242 on the actual nonzero within-factor differences and all requested endpoint comparisons. Its common-comparison lemma keeps the core fixed.

Every nonidentical pair gives an affine difference with at most one zero. Form the finite set of interior crossing parameters, sort it, add endpoints 0 and 1, and choose a sample in each consecutive interval. There are no ties inside such intervals, so the unique maximizing point in every factor remains constant throughout the interval. At a boundary, the adjacent winners both maximize the wall objective by the affine inequalities. Apply `affine_crossing_exposed_edge` whenever any factor changes. Delete stationary consecutive tuples without creating new geometric transitions. Index the retained samples strictly increasingly and use #239's slope-rank count to bound the actual number of edges by sum_i(card S_i-1).

The finite ordering, endpoint transport, stationary compression and final route concatenation still need their Lean implementation. The new module does NOT silently assume they are already formalized. The numerical constructor implements them with exact rational arithmetic, but this does not certify arbitrary JSON in the Lean kernel.

## 5. Deterministic executable construction and scope

The constructor avoids finitely many hyperplanes using the moment curve (1,z,...,z^(d-1)). Each nonzero form vanishes at at most d-1 integer parameters, so H(d-1)+1 candidates suffice. Explicit small rational perturbations preserve the strict endpoint cones. Factor-by-factor affine-envelope processing avoids the Cartesian product of all component choices. Independent checking validates all listed component points and the ENTIRE exposed face at every retained event.

The committed scripts and exact raw regression reproduce 85 paths/103 edges and 17 rejected controls; the clean replay and serialized 32D verification are preserved separately. These are supplied finite factor presentations, not automatic decompositions from arbitrary H-inequalities. No universal correctness theorem for Python/JSON or historical novelty is claimed.

Classical source: Deza and Pournin, *Diameter, decomposability, and Minkowski sums of polytopes*, arXiv:1806.07643v1, Lemmas 3.7-3.8. The simultaneous written lifting bound L+(L+1)sum_i(f0(Q_i)-1) and larger carrier applicability boundary remain as recorded in `SIMULTANEOUS_MINKOWSKI_LIFT.md`. Controlled decompositions for arbitrary high-dimensional carriers, or a different routing method for those carriers, remain necessary for a uniform Polynomial Hirsch result.
