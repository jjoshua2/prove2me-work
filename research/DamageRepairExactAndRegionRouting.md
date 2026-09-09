# Exact damaged-sequence repair and distinct-support routing

## Scope and publication status

This continuation develops two routing implications and an exact obstruction to a tempting weakening. No result in this packet proves the global Polynomial Hirsch conjecture. No Prove2Me API call is made by the packet workflow or bundler. Publication is deferred to the user's next request.

The source environment is Lean 4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`. The `Verify damage-repair proof packets` workflow records source compilation, mandatory axiom reports, independent standalone compilation, regression output, source hashes, and the exact repository commit. A proof is ready only when all of those checks pass.

## 1. Exact repair, with genuinely invalid original steps allowed

Let `w[0],...,w[L]` be a sequence, not necessarily a walk in the final parent polytope P. Select ordered intervals `[s_i,t_i]` with `t_i <= s_j` whenever `i<j`. Both endpoints of interval i must be extreme vertices of P and lie in an extreme face F_i with intrinsic graph diameter at most B_i. Only the original steps outside the half-open intervals `[s_i,t_i)` must be valid parent edges or equalities. Interior points and steps are unrestricted.

The repaired sequence is a padded parent walk of exact budget

```
L - sum_i(t_i-s_i) + sum_i B_i.
```

Here a padded walk permits equality steps, so this is a diameter upper bound, not a claim that its underlying shortest path has exactly that length.

Proof: concatenate the surviving gap before each interval, a route inside its supporting face, and the final suffix. Each face edge is a parent edge. Ordering makes the total original length removed at most L, and the arithmetic identity is proved separately rather than relying on unsafe cancellation of natural-number subtraction.

The checked implementation also supplies:

- the loose bound `L + sum B_i`;
- `L + M*C` when there are at most M blocks of cost at most C, still allowing destroyed interior steps;
- an aggregate no-growth criterion: `sum B_i <= sum(t_i-s_i)` implies repair within L. Individual blocks may grow, provided savings elsewhere compensate.

Core: `Solutions/PolynomialProjectiveDamageSurviving.lean`.
Public indexed wrapper: `Solutions/Sol_Hirsch_ordered_damage_repair.lean`.
Proposed publication name: `Hirsch.ordered_damage_repair_exact`.

The older theorem assuming every original step is already valid is retained for compatibility. Its bare existence conclusion at the looser length also follows by padding that existing walk; it is not the substantive damaged-sequence result.

## 2. Remove chronological ordering by certifying actual connections

Let S_i be finitely many routing regions, each permitting a route between any two of its points for cost C_i. Connect region labels when their sets share an actual point. A walk in this intersection graph can be simplified to a path without repeated labels. Route through one shared point between consecutive regions. Each used label is charged once, giving total cost at most

```
sum_i C_i.
```

The argument does not assert that the resulting parent walk never revisits a face or is shortest. It removes repeated labels from the auxiliary routing certificate, which is enough to avoid repeated charges.

For the polytope application, the region for face F_i is `extremePoints P ∩ F_i`. Thus intersections are witnessed by common parent vertices, not just overlap of intervals in a historical sequence. Each separately listed surviving edge is another region of cost one, consisting of its two endpoints. If every consecutive pair of a supplied parent-vertex sequence either shares a selected face or lies on a listed surviving edge, there is a genuine parent walk of budget

```
(sum_i B_i) + number_of_listed_surviving_edges.
```

The input sequence can use a face or listed edge arbitrarily many times and in any chronological order. To obtain a distinct-support bound, index each chosen face and edge only once; duplicate indices are permitted but make the bound weaker.

Core: `Solutions/PolynomialRegionRouting.lean`.
Mixed specialization: `Solutions/PolynomialMixedRegionRouting.lean`.
Proposed publication name: `Hirsch.route_of_faces_and_surviving_edges`.

## 3. Why interval overlap alone is insufficient

For m>=7, take the integer-coordinate polygon

```
P_m = convexHull {p_j=(j,j^2) : 0<=j<2m}.
```

Its graph is the cycle on the ordered vertices p_0,...,p_(2m-1). Consecutive lower edges have supporting lines `y=(2i+1)x-i(i+1)`: at p_j the difference is `(j-i)(j-i-1)`, positive except at their two endpoints. The closing edge has line `y=(2m-1)x`. Each vertex p_i is uniquely exposed by minimizing `y-2i*x`, whose difference from the value at p_i is `(j-i)^2`.

Use the four-distinct-vertex sequence

```
w = [p_0, p_m, p_1, p_(m+1)],  L=3.
```

Record interval `[0,2]` supported by edge `[p_0,p_1]`, and interval `[1,3]` supported by edge `[p_m,p_(m+1)]`. Both supporting faces have intrinsic diameter one. Every original step is inside at least one recorded interval, so the outside-survival condition is vacuous. All block endpoints are genuine parent vertices in their stated faces.

Nevertheless the parent distance from p_0 to p_(m+1) is m-1. For m=7 it is 6, larger than the putative unordered loose bound `3+1+1=5`; it becomes arbitrarily large while L=3, the block count=2, both face costs=1, and dimension=2 stay fixed. The two faces are disjoint. Chronological overlap of their intervals creates no geometric connection between them.

This refutes dropping the ordered-block hypothesis while retaining only endpoint face membership and interval coverage. It does not refute Polynomial Hirsch, and does not show that such a configuration occurs in a particular projective-removal process.

## 4. Independent exact regressions

`scripts/test_damage_region_routing.py` uses only Python's standard library and integer arithmetic. It checks:

- 55 crossing examples in the polygon family, including a simpler singleton-face variant;
- all 64 simple graphs on four vertices, 12,531 families of at most three nonempty induced connected regions, and 88,798 certified endpoint pairs;
- 50,749 ordered interval/cost cases with L<=6, at most three blocks, and costs in {0,1,2}, including zero-length and touching intervals.

The polygon hull/graph checks are exact computational certificates, not Lean formalizations of those hulls. The general repair implications are separately checked by Lean, not inferred from finite tests.

## 5. Remaining geometric obligation

A global application must produce a low-cost connected network of certified supports in the final polytope, or ordered blocks with a sufficiently small exact repair cost. Historical facet names and chronological overlap do not suffice. In particular, one must establish surviving endpoints and edges, actual common-vertex connections, and quantitative bounds on the total intrinsic support costs. Those bounds are not supplied by these routing lemmas.

## Reproduction and publication handoff

Run the verification workflow, or in the pinned repository environment:

```sh
python3 scripts/test_damage_region_routing.py
lake build Solutions.Sol_Hirsch_ordered_damage_repair Solutions.PolynomialMixedRegionRouting
python3 scripts/bundle_damage_progress.py
lake env lean damage_progress_packet/ordered_exact.lean
lake env lean damage_progress_packet/mixed_regions.lean
```

The workflow additionally performs strict axiom audits allowing only `propext`, `Classical.choice`, and `Quot.sound`, and uploads the proof packets, exact source hashes, build logs, and regression results. Each standalone file declares `solution` and imports only Mathlib and the already-public `Definitions.Def_Hirsch_model`.

The `*_statement.lean.txt` files are proposed problem statements with an intentional `by sorry` placeholder for problem registration; they are not proofs. The corresponding `.lean` proof files contain no admissions and must pass the standalone gate. Before a later publication, verify collision-free names and the pinned server environment, then submit the corresponding checked proof. Nothing in this continuation performs those writes.
