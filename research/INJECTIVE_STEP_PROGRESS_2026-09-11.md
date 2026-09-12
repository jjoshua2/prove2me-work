# Injective checkpoint localization and maximal-step progress

Date: 2026-09-11 (America/New_York)

Status while written: candidate formalization in PR #156; focused hosted Lean verification pending. This note does not claim kernel verification or Prove2Me publication.

## Observation

The existing sharp nonvertex checkpoint-localization theorem used an arbitrary reference vertex only to prove that the all-neutral defect of a row circuit is zero. PR #153 now proves exact neutral rank from row-map injectivity directly. Therefore the reference vertex, boundedness, and even nonemptiness of the H-polyhedron are not part of the localization argument itself.

## Candidate results

For any finite row presentation with injective `HirschCircuit.rowMap a` and any row circuit `y-x`:

`2 * commonFaceDim(x,y) + d <= n + commonFaceDim(x,x) + commonFaceDim(y,y) + 1`.

For a maximal feasible row-circuit step `x -> y`, the already-verified strict destination-self-face drop removes the target term and gives

`commonFaceDim(x,y) + d <= n + commonFaceDim(x,x)`

and

`commonFaceDim(y,y) + d + 1 <= n + commonFaceDim(x,x)`.

`Solutions/PolynomialOneRowDeletionStepProgress.lean` instantiates both inequalities in the canonical one-row deletion presentation, whose row map is injective by the bounded-parent pointedness theorem.

## Frontier role

Merged #151 gives the unbounded deletion outer an explicit cubic circuit walk. Merged #153 keeps exact neutral-rank/excess accounting there. This PR would also keep the maximal-step carrier/source-self-face progress inequality there.

Parallel PR #155 develops noncompact common-face parent-vertex portals. The two lines are complementary: #155 supplies portal vertices while #156 supplies sharp carrier/progress bounds for the circuit steps being routed.

Neither line by itself turns a row-circuit step into an ordinary graph edge path. The remaining D-side problem is still dynamic circuit-to-edge routing with polynomial total cost.
