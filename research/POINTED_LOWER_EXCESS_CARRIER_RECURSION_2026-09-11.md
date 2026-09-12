# Pointed strict-carrier recursion: what is now connected

Research date: 2026-09-11 (America/New_York)
Implementation: `Solutions/PolynomialPointedLowerExcessCarrierRecursion.lean`
Pull request: #161

## The gap

The previous lower-excess carrier adapter required the entire parent to be bounded. That hypothesis could not be passed to the pointed but potentially unbounded one-row deletion outer. Injective carrier rank accounting alone did not fix this: a resource inequality is not a graph route.

The new adapter uses the already-established injectivity of every equivalent nonempty common-carrier presentation. It applies an explicitly pointed lower-excess hypothesis, transports the resulting intrinsic graph budget back through the affine carrier chart, and then uses the pointed parent-vertex portals to assemble actual parent edges.

## Exact conditional result

Let the parent be a nonempty finite H-polyhedron with injective row map. Let w(0),...,w(L) be feasible checkpoints whose first and last points are original vertices. For every consecutive carrier, require

`minimum presentation row count - intrinsic dimension < R`.

If all nonempty injective finite H-polyhedra below row excess R have diameter at most B, then the endpoints have an ordinary parent-edge/stay route of length B*L. With separate certified budgets C_i, the bound is sum C_i. The proof does not assume that intermediate checkpoints are vertices, that the parent is compact, or that a circuit segment itself is an edge.

The hypothesis is expressed as `LowerExcessInjectiveHpolyDiameterBound R B`; it is not asserted as an axiom or as an unconditional theorem. This uniform budget quantifies over all dimensions and row counts below the excess threshold. A size-dependent polynomial induction would require a compatible size-aware version or an independent justification of that uniform budget.

The final same-phase theorem now yields an edge-cost dichotomy, rather than only the previous resource inequality:

- the carrier has genuine intrinsic diameter at most B; or
- the full essential trapped-blocker certificate remains, including a minimum irredundant strictly feasible presentation and a single-tight witness.

## Application to the cubic deletion route

For a certified length-17*m^3 feasible sequence in the pointed deletion outer, the strict-carrier theorem gives B*(17*m^3) edges/stays. This application requires strictness for every indexed carrier and vertex endpoints. The existing cubic circuit theorem does not itself establish that strictness.

The weighted result charges indexed carriers. It does not claim that multiple occurrences of the same geometric carrier are distinct or that repeated carriers have already been globally deduplicated.

## Two traps to avoid in the next step

1. Padding is not a geometric resource decrease. A stay at a nonvertex can still have a large minimal face: in the square [0,1]^2, an interior point has no tight describing rows, so its common face with itself is the whole square. Thus strictness of only the nonstationary steps must not be substituted silently for the all-carriers hypothesis. A coherent pointwise parent-vertex rounding map or explicit removal of stays would remove this bookkeeping restriction; the current theorem leaves it visible.
2. A polynomial factor at each recursive level is not a uniform polynomial bound. Repeatedly using a cost multiplier N^3 over R levels produces N^(3R), whose degree grows with R. A cost-controlled hard-case bypass or a global amortization/recurrence argument is still required. This is an arithmetic limitation of that proposed analysis, not a counterexample to Polynomial Hirsch.

The square active-row example and the recursive product identity were checked with exact rational/integer Python arithmetic. These checks are bookkeeping controls, not Lean verification.

## Next focused target

Handle the essential trapped-blocker branch with a measured edge cost, preserving pointedness and real parent-vertex portals through row deletion/reinsertion. Pair it with a recurrence whose total cost has a fixed polynomial exponent. Do not create another Open child that merely renames the existing d>=4 refinement theorem.

## Verification and publication

The implementation contains no intentional proof holes. Its exact verification receipt is recorded separately after the frozen-source gate completes. No Prove2Me ACCEPTED verdict is claimed by this note.
