# Crossing repair intervals: the actual geometric condition

## Scope and verification

This continuation is in PR #39, stacked on the exact/surviving-step and mixed-region work in PR #38. No Prove2Me registration, submission, or other API action is performed by this branch. The branch workflow checks the source proofs, an independently flattened public-facing proof packet, and the exact integer polygon regression. A workflow failure must not be described as a completed verification merely because some dependencies compiled.

The mathematical statements below are conditional routing results and an obstruction to an invalid repair hypothesis. They do not prove or disprove Polynomial Hirsch, and no novelty claim relative to the literature is made.

## 1. What the ordered repair theorem actually buys

The useful version from #38 only assumes surviving steps outside the marked intervals. Original steps inside those intervals need not be edges in the repaired polytope. For ordered disjoint intervals it constructs a route of exact padded budget

`L - sum_i(t_i-s_i) + sum_i B_i`.

Thus aggregate savings can offset a costly repair: it is enough that `sum B_i <= sum(t_i-s_i)` to avoid increasing length. The older loose theorem assuming every original step already survives is only a baseline, not the substantive damaged-path result.

## 2. Why arbitrary crossing endpoint intervals are insufficient

Consider the cycle on vertices `0,...,15`, with edges between consecutive indices and between `15` and `0`. Take the old sequence

`w = [0,8,1,9]`.

Mark intervals `[0,2]` and `[1,3]`. Their endpoints lie respectively in edge regions `{0,1}` and `{8,9}`. Each region has intrinsic diameter one. The half-open step intervals `[0,2)` and `[1,3)` cover every old step, so there is no uncovered step whose survival could be required.

However, the endpoints `0` and `9` have distance seven. The route `0,15,14,13,12,11,10,9` attains seven, and the potential `min(i,16-i)` changes by at most one per edge and has final value seven. Even the deliberately loose bound `L + sum B_i = 3+1+1 = 5` is false.

The chronological intervals overlap; the geometric edge regions are disjoint. These are different notions of intersection.

Lean verifies the finite-graph claim in `Solutions/PolynomialCrossingIntervalObstruction.lean`, including the lower bound for every padded route, an explicit seven-step route, interval coverage, endpoint membership, local one-step routing, and disjointness.

## 3. This obstruction occurs in actual convex polygons

For any integer `m >= 4`, take the convex hull of

`v_i = (i,i^2), 0 <= i < 4m`.

For `i < j`, the oriented determinant with a third vertex `k` is

`det(v_j-v_i, v_k-v_i) = (j-i)(k-i)(k-j)`.

Consequently the supporting edges are exactly consecutive pairs and the closing pair `{0,4m-1}`: consecutive pairs have all other vertices on one strict side; the closing pair has all remaining vertices on the other strict side; every other pair has vertices on both sides. No three vertices are collinear. The graph is therefore the `4m`-cycle.

Use the sequence `[0,2m,1,2m+1]` and the same intervals `[0,2]`, `[1,3]`. Their edge-region costs remain one and one, while endpoint distance is `2m-1`. Hence no bound depending only on the three old steps and these two unit repair charges can hold without another compatibility condition.

`scripts/test_crossing_interval_obstruction.py` checks all supporting-pair candidates by exact integer determinants and reconstructs the graph exhaustively for `m=4,...,20`. The 17 instances require 1,342,320 determinant checks. The first distance is 7 and the last is 39, against the same proposed bound 5.

The convex-hull realization is an independent exact Python certificate plus the argument above, not a Lean hull formalization. This family is not claimed to arise from a particular projective-removal operation, does not impose the balanced separated-endpoint hypotheses of the main research target, and is not a Polynomial Hirsch counterexample: its diameter grows only linearly in its facet count.

## 4. A sufficient geometric condition for crossing intervals

`HirschRegionRoute.route_of_interval_cover` allows unordered and crossing intervals provided:

- Every old step lies in at least one marked interval.
- Each interval's two endpoint values lie in its certified routing region.
- Region `i` can route any two of its points with budget `C_i`.
- Whenever two closed time intervals overlap, their actual routing regions share a point.

It produces a route of budget `sum_i C_i`, charging each available region once, not once per occurrence. Unused labels can be omitted from the finite family before applying the theorem.

The proof builds connectivity in the actual region-intersection graph from temporal coverage and the supplied portals. A simple path in that graph visits each region label at most once. Concatenate the local routes through the shared points, then pad to the sum budget.

The face specialization `route_of_face_interval_cover` uses regions `extremePoints(P) intersect F_i`. Its portals are shared parent extreme vertices. Only marked interval endpoints must remain parent extreme vertices. Unmarked interior entries of the old sequence need not remain feasible and no original graph connectivity or numerical parent diameter is assumed.

The overlap-portal condition is sufficient, not asserted to be necessary or automatic. The more general connected-region theorem in #38 can use a smaller suitable connected subfamily even when some unused temporal overlaps lack portals. Surviving edges can be included as two-point regions of cost one.

## 5. Next mathematical target

For a concrete projective-removal construction, prove that the repair regions and surviving-edge connectors contain an endpoint-connecting network whose total distinct-region cost is polynomially bounded. A counterexample to time-overlap connectivity cannot be repaired by merely sorting the same endpoint-only intervals. Actual geometric portals or additional surviving connectors must be certified.

The new theorem discharges routing once such a certificate exists; it does not establish that the desired projective-removal certificate always exists or has polynomial cost. Those quantitative geometric facts remain the research task.

## 6. Offline publication packet

`Solutions/Sol_Hirsch_face_interval_cover_route_bound.lean` has a public-facing theorem type containing only Mathlib and existing `Hirsch_model` vocabulary. The conclusion expands the local `Route` abbreviation.

`python3 scripts/bundle_public_interval_repair.py` generates `public_interval_repair_packet/solution.lean` and a source-hash manifest. All local `Solutions.*` dependencies are flattened, unexpected imports and unchecked proof declarations are rejected, and only `Mathlib` and `Definitions.Def_Hirsch_model` remain as imports. The workflow compiles the packet and audits `#print axioms solution` independently.

The proposed public theorem name is `Hirsch.face_interval_cover_route_bound`. Name-collision checking, registration, and Prove2Me server verification are deliberately deferred. A kernel-green packet is not yet a platform `ACCEPTED` verdict.
