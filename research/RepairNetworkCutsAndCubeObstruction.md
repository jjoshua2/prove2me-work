# Repair-network cuts and the crossing-cube obstruction

## Scope and provenance

This continuation is stacked on PR #38, from commit `0ae077b5a183af8b4c9a9df935a2bf90c03c240a` of `chatgpt/projective-damage-blocks`. That snapshot already contains the exact ordered-block repair and unordered mixed-region routing work, including the `Std.Irrefl` repair. This continuation does not claim authorship of those inherited changes and does not overwrite the actively changing base branch.

New work is on `chatgpt/repair-network-cut-certificates`. Publication to Prove2Me is deliberately deferred. No API credentials are read by the new workflow. The pin remains Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## 1. The precise missing hypothesis

A damage block `[s,t]` only certifies a route between its two endpoints. If two time intervals overlap, this does **not** establish a shared vertex between their repair faces. The old chronology and the actual repair-network connectivity are different objects.

For regions `S_i`, define their intersection graph by

```
i ~ j iff i != j and there exists z in S_i intersect S_j.
```

The new `RegionCutCondition S i j` says that every set `A` of region labels containing `i` but not `j` has a genuine shared-point bridge between a label in `A` and a label outside `A`.

The new theorem `region_walk_iff_cut_condition` proves this is equivalent to existence of a walk between `i` and `j` in the intersection graph. The proof is direct: if no walk exists, take `A` to be the labels reachable from `i`. Any alleged crossing shared point extends a walk to a label outside `A`, a contradiction. Conversely a walk must cross any separating partition.

This is an exact certificate criterion, **not** an independently established geometric property of every projective-removal instance. Compilation and axiom-audit status are recorded in the PR and Actions evidence; the mathematical description here does not replace that evidence.

## 2. Positive quantitative consequence

Suppose any two points in `S_i` can be connected in the target relation `R` within padded budget `C_i`. If the cut condition holds between endpoint regions, then

```
route length <= sum_i C_i.
```

This uses PR #38's loop-erased region walk: repeated appearances of the same label are removed, and each retained region is traversed once. A finite selected subfamily `K` is sufficient, with budget `sum_{i in K} C_i`; unused regions incur no charge. The ambient collection may be infinite.

`route_or_separating_region_cut` also exposes the diagnostic alternative: a route within the full family budget, or a concrete partition of region labels with no shared point crossing it. Such a partition obstructs the **chosen certificate network**, not necessarily the full parent graph.

For actual polyhedral faces, `route_of_extreme_face_cut_condition` applies this construction to `S_i = extremePoints(P) intersect F_i`. All cut bridges must then be actual parent vertices in both faces. Surviving edges can be included as two-vertex cost-one regions, as in PR #38.

New declarations are in `Solutions/PolynomialRepairNetworkCuts.lean`.

## 3. A counterexample even on balanced cubes

In the d-dimensional unit cube, with d >= 6, write

```
u = (0,0,...,0)
a = (1,0,...,0)
b = (0,1,...,1)
v = (1,1,...,1).
```

Take the four-point sequence `w = [u,b,a,v]`, of three transitions. The interval `[0,2]` has endpoints `u,a` in the first-coordinate edge with all other coordinates zero. The interval `[1,3]` has endpoints `b,v` in the parallel first-coordinate edge with all other coordinates one. Both repair faces have intrinsic graph diameter one.

The half-open step intervals `[0,2)` and `[1,3)` cover all three original step indices. Thus an assumption requiring valid original steps only outside those intervals is vacuous. The two intervals cross, however, and their supporting edges are disjoint.

The naive unordered extension would assert a route of length at most `L + sum B_i = 3 + 1 + 1 = 5`. But every cube edge changes just one binary coordinate. A route from `u` to `v` therefore needs at least `d` steps, and flipping the coordinates in turn gives exactly `d`. The proposed bound fails for every `d >= 6`, not just for one exceptional configuration.

The cube has exactly `2d` irredundant facet inequalities, is bounded and simple, and `u,v` share no facet. Consequently balance, simplicity, and separated endpoints do not repair this *endpoint-only interval-cover* inference.

### What this does not disprove

The sequence is not asserted to be a walk in the final cube. That is allowed by the proposed weakened repair interface, which permits destroyed interior steps. We have not shown it arises from an actual Case VII deformation, and we have not invalidated any theorem carrying additional constraints from such a deformation. We have not disproved Polynomial Hirsch.

### Exact formalization boundary

`Solutions/PolynomialCrossingCubeObstruction.lean` represents cube vertices as `Finset (Fin d)`, with adjacency defined by inserting/deleting exactly one coordinate. The general lower-bound theorem uses the potential `phi(x) = x.card`. It proves the crossing obstruction for every `d >= 6`, not by finite enumeration.

The interpretation as the Euclidean cube `Hpoly` follows from the elementary geometry above: fractional coordinates prevent extremality, binary vertices have d independent active coordinate rows, and the smallest common face of two vertices has one free coordinate per differing bit. Its graph edges therefore differ in exactly one coordinate. This identification is explained here and checked by the finite Python regression; it is **not** a Lean transport theorem to `Hirsch.Adj` in this continuation.

The formal `cube_crossing_has_separating_cut` diagnoses the failure as the partition `{low edge}` / `{high edge}`, rather than as a failure of the full cube's connectivity.

## 4. Regressions

`python3 scripts/test_repair_network_cuts.py` uses only exact integer and finite-set operations. It exhausts all 64 simple graphs on four labelled vertices and all families of one, two, or three distinct nonempty regions whose induced subgraphs are connected. It checks:

- 12,531 region families;
- 93,307 endpoint-label pairs;
- 113,884 separating cuts;
- 393,852 parent-route budget inequalities.

It separately checks the cube examples in dimensions 6 through 9, including the coordinate active-row description, every unordered vertex pair, every edge's potential change, the block endpoints, coverage of old step indices, the disconnected repair network, and the true source-target distance.

A positive mixed-region regression has 12 old transitions, including repeated and reversed region visits, yet a once-per-region cost of 5 and an actual endpoint distance of 5.

The regressions are supplemental evidence, not replacements for the universal Lean proofs. The new workflow compiles the imported proof chain, requires all selected axiom reports, and rejects `sorryAx` and nonstandard axioms. It does not publish anything to Prove2Me.

## 5. Consequence for the next research step

Do not attempt to prove that overlap of endpoint-only repair intervals implies repair-network connectivity. The cube family refutes that statement.

A useful next geometric target must instead establish genuine cross-cut bridges for a low-cost selected family of surviving faces/edges, or use extra deformation information that excludes the disconnected certificate. Both the number/cost of selected regions and their connectivity must be proved. Assuming either of those universally would only move the unresolved quantitative graph-routing issue into a hypothesis.
