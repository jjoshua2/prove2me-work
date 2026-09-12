# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-12 through merged, kernel-verified PR #185.
Repository: `jjoshua2/prove2me-work`.
Current integrated main after #185: `f2d3fd3ce3b6fa1d171f2ff77e1ae169610e7087`.
Lean: `v4.30.0`; Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first

The remaining research task is still **cost-controlled ordinary-edge refinement**, not circuit-walk existence, pointedness, vertex existence, face-portal existence, or support counting.

The target-anchored line has advanced substantially beyond the old #165 handoff. For a fixed original target vertex `v`, keeping the target-tight rows gives an outer with only `v` as an old vertex. All target-slack cuts can then be restored simultaneously. The repair now exposes the **actual final cut faces and actual parent-vertex portal pairs used**, and charges only those pair-specific calls.

For target-rooted repair, the centre-star edge itself needs no cut-face charge; the nontrivial cut cost is localized to the endpoint-lift spoke. The newest verified radial result (#185) shows fixed-row active cells on such radial geometry are convex, so along a segment one row cannot leave the radial upper envelope and later re-enter.

No result below proves the global fixed-degree polynomial recurrence. A polynomial number of circuit steps, a bound on the number of used cut labels, or a sum of recursive budgets is not enough unless the recursive subproblems are shown to decrease under a globally amortized resource.

## Recorded formal Open frontier

The latest authenticated Prove2Me frontier audit was performed during PR #172 and left

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

Open, theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`.
Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the Polynomial Hirsch root remained Open.

No later PR through #185 mutated the Prove2Me frontier. Kernel verification is not platform acceptance.

Do not create cyclic children through `balanced_polynomial_bound` or broad target-face-access assumptions. Do not call a `RowCircuitStep` an `Adj` edge. Do not redo already-complete circuit Child A or Santos/spindle work without finding a defect.

## New public Prove2Me results from the target-anchored line

### PR #167 — target-tight outer has one vertex

Public theorem:
`Hirsch.target_tight_outer_unique_vertex_zero_diameter`

- theorem ID `aa3abbb2-203b-41ab-86b6-f45ab734c57a`
- proof submission `9903527d-a915-4c03-9109-5142f582d801`
- status **Proved**

Keeping exactly the rows tight at a chosen vertex gives a relaxed H-polyhedron whose extreme-point set is exactly that vertex, hence old-vertex graph diameter zero. The outer may be unbounded.

### PR #172 — sharp slack-row count

Public theorem:
`Hirsch.vertex_strictly_slack_rows_card_le_row_excess`

- theorem ID `804b7a8e-0572-4407-a014-2d9f4aaa6f87`
- proof submission `8dc241ef-cb1e-4eec-9423-a424b559d380`
- status **Proved**

At any vertex of an `n`-row H-presentation in dimension `d`, at most `n-d` describing rows are strictly slack. No boundedness, irredundancy, simplicity, or full-dimensionality assumption is used.

## Verified target-anchored / clipping chain through #185

### #165–#166: preserve the fixed target under deletion

- #165: any batch of rows strictly slack at a fixed original target vertex can be deleted simultaneously while preserving row-map injectivity, the target vertex, and exact recovery on reinsertion. Keeping exactly the target-tight rows gives the singleton-vertex outer.
- #166: for the canonical same-phase destination blocker, one-row deletion preserves the same target and gives strict row-count / row-excess drop together with a fresh cubic circuit walk in the relaxed pointed model.

The relaxed walk is still a circuit walk, not automatically an ordinary-edge route.

### #168, #170: simultaneous target-cone reinsertion

`HirschTargetDeletion.target_slack_batch_reinsertion_with_parent_routes`
restores all target-slack cuts in one clipping construction. If each final cut face has an ambient parent-edge budget, pairwise and target-rooted repair costs are additive in those budgets.

#170 combines this with the sharp target-slack cardinality bound. A uniform local budget `B` gives pairwise cost `2 + (n-d)*B` and rooted cost `1 + (n-d)*B`. This is not a polynomial recurrence because it does not supply `B`.

### #171, #173–#175, #177: pay only support actually used

- #171 exposes the simple-path region support after cycle erasure. The returned labels are `Nodup`; cost is the sum of local budgets on those labels, not on every available face.
- #173/#174/#177 propagate that support through simultaneous radial clipping. Mixed repair labels distinguish final cut faces, surviving old-edge regions, and endpoint singletons. Projecting to cut labels stays `Nodup`; distinct old-edge labels contribute at most the original outer budget `D`.
- #175 gives the target-cone statement: each repaired route uses a `Nodup` list of actual target-slack cuts of length at most `n-d`. Pairwise cost is `2 + sum used B_i`; target-rooted cost is `1 + sum used B_i`.

Support counting alone still does not bound the weighted sum of the used face costs.

### #178–#179: retain the actual parent-vertex portal pairs

- #178 retains the actual simple intersection-graph path. Consecutive closed extreme-face regions come with a shared **parent extreme vertex** portal.
- #179 introduces `RegionLeg`: every local call records `(label, entry, exit)`. Local costs may depend on that actual pair, and the global route cost is exactly the sum of pair-specific leg costs. The leg-label list is duplicate-free.

This removes the interface-level reason to pay a whole-face diameter when only one concrete portal pair is needed.

### #181 and #183: pair-specific target-cone accounting

#181 propagates pair-specific portal costs through simultaneous clipping. For one outer route of padded length `D`, the final route costs

`D + sum(pair-specific costs of actual used cut legs)`.

Every used cut leg retains its concrete parent-extreme entry and exit vertices, both tight on its labelled cut row.

#183 specializes this to the target-tight star. For the target-slack set `J`:

- pairwise repair returns at most `n-d` duplicate-free actual cut legs and costs
  `2 + Σ B(row, entry, exit)`;
- target-rooted repair returns the analogous actual legs and costs
  `1 + Σ B(row, entry, exit)`.

This is the current clean statement of the remaining numerical obstruction: **control the sum of costs of the concrete portal pairs actually selected by the repair.**

### #182 and #185: target-rooted radial structure

#182 proves that radial retraction about its centre preserves every centre-to-point segment. In the target-tight star, the centre-to-outer-vertex edge can therefore be covered entirely by the old-edge repair region and needs no cut-face label. The nontrivial target-rooted cut cost is on the endpoint-lift spoke.

#185 (`Solutions/PolynomialRadialActiveRowInterval.lean`) proves the next one-dimensional structural fact:

- each normalized radial row score is affine;
- if one row attains the radial scale at two points, it attains it on every convex combination;
- every fixed-row active cell is convex;
- under strict centre slack, a segment whose endpoints are active for one row retracts entirely into that final cut face.

Frozen source `fd7511f10153113446dcad73971f091ac6d5f9cf` passed run `34692904962`, job `103551222857`, artifact `10297421344`, digest `sha256:038b33fe502c512a91e97f9b5072360acc22e68ee674ef770929083d68999ffc`. Receipt: `research/RADIAL_ACTIVE_ROW_INTERVAL_VERIFICATION_2026-09-12.md`.

This gives chronological interval structure but still does not bound the parent-edge cost between the two portal vertices selected inside an active cut face.

## Completed interfaces to reuse

### Pointed carrier recursion: #151, #153–#161

- #151: `rowCircuitWalk_explicit_cubic_of_injective` gives a `17*n^3` circuit walk from a feasible source to a vertex target under row-map injectivity, without boundedness.
- #153: exact neutral-rank / selected-defect / savings identities work under injectivity.
- #154–#157: nonempty injective H-polyhedra have vertices; intersecting carriers have genuine parent-vertex portals; feasible checkpoint sequences assemble from supplied local parent-edge budgets.
- #158: retaining one nonneutral row kills the circuit-line kernel; with two nonneutral rows either can be deleted while preserving pointedness. Vertex-starting steps have opposite-sign blockers.
- #159: equivalent nonempty common-face presentations inherit row-map injectivity and satisfy the expected dimension-vs-row count.
- #160: minimum-carrier same-phase strict-resource / essential-trapped-blocker dichotomy works in pointed unbounded parents.
- #161: strict minimum-carrier excess drop becomes a real conditional ordinary-edge budget through `LowerExcessInjectiveHpolyDiameterBound`.

**Important:** `LowerExcessInjectiveHpolyDiameterBound` is still an induction hypothesis, not a proved uniform global theorem. A future result must establish when the actual portal-pair carriers fall under a smaller resource.

### One-row cap / facet descent: #140–#152, #164

The exterior-cap line supplies explicit bounded caps, preservation of old vertices/edges for sufficiently far caps, classification of new cap vertices, and radial horizon repair. #149 gives same-excess/lower-dimension facet routing from an explicit lower-dimensional budget. #164 gives the one-cut wrapper `D + 1 + B`.

These remain useful local tools but naive independent recursion on `D` and `B` is Pascal-type, not a fixed-degree polynomial proof.

### Existing small-excess and product tools

Reuse common-face affine transport, minimum-presentation invariance, small-excess routing through row excess three, and independent row-block product budgets. In particular `commonFace_diamLE_of_subpresentation_excess_le_three` keeps the actual local excess `r ≤ 3` as the route budget rather than rounding everything to three.

## Highest-value next theorem: used-path support must buy carrier row savings

The next step should turn the support object into a **decreasing recursive resource**, not expose another variant of the same support.

A promising concrete target is the following ordinary theorem and Lean formalization.

Let `C = commonFace a b p q`, let

- `h = commonFaceDim a b p q`,
- `M = commonFaceMinSubpresentationCount a b p q`,
- `J` be original row indices that are **strictly slack at every point of `C`**.

Prove

`(M - h) + J.card ≤ n - d`.

Suggested declaration:
`HirschCircuitLocalization.commonFace_minExcess_add_strictRows_le`.

Why this is the right resource statement: rows in `J` can be deleted simultaneously from the common-face coordinate presentation without changing that represented carrier. If `T` is the set of original nonzero rows tight throughout the carrier, then `d-h ≤ |T|`, and an equivalent presentation remains after removing both the rows vanishing on the carrier and the rows strictly slack everywhere on it. This yields `M + |T| + |J| ≤ n`, hence the displayed inequality.

### Apply it to a chordless used-region path

Before assigning pair-specific local costs, choose a shortest/chordless path in the **full mixed repair-region graph**. Do not shortcut a path after costs are attached, because changing a portal pair can change its pair-specific cost.

For a used cut face `F_i`, every other used cut `F_j` that is not an immediate path neighbor must be disjoint from `F_i`; otherwise compact closed extreme-face intersection supplies a shared parent vertex and hence a chord. Therefore row `j` is strictly slack on every point of `F_i`, and hence on every common carrier of a portal pair routed inside `F_i`.

If

- `e = n-d` is ambient row excess,
- `r` is the number of used cut labels,
- `c_i ∈ {0,1,2}` counts immediate path neighbors of cut `i` that are themselves cut labels,
- `e_i = M_i-h_i` is the minimum-presentation excess of the actual entry/exit carrier on cut `i`,

then the desired consequence is

`e_i + (r - 1 - c_i) ≤ e`,

hence

`e_i ≤ e - r + 1 + c_i ≤ e - r + 3`.

This is a genuine support-versus-subproblem-size tradeoff. It is materially stronger than `r ≤ e`.

### Concrete payoff to target in the same proof line

When a chordless repair uses the maximum possible number of cut labels, `r=e`, every actual cut-leg carrier has `e_i ≤ 3`. The already-verified small-excess carrier theorem can then discharge each local ordinary-edge cost directly. Summing `c_i` over the used cuts gives at most `2(r-1)`, so the total cut-leg cost is at most `3e-2`. Adding the old-edge contribution gives the concrete route certificate

`D + 3e - 2`

for that maximum-support repair case (with the obvious zero-support exception handled separately).

This does **not** yet solve the cases with few used cuts, where one or more portal-pair carriers may retain large excess. But it would be the first theorem in this line that converts exact used support into a quantitatively smaller recursive problem and solves a nontrivial support regime outright.

## Important falsifiers / proof hygiene for the next step

- Simple path is not enough; use a chordless/shortest path when deriving nonintersection of nonneighbors.
- A row slack only at the two selected portal vertices need not be removable. The hypothesis for the deletion lemma must be strict slack **throughout the carrier**.
- Do not infer that pair-specific costs decrease under a graph shortcut; choose the shortcut path before assigning local pair costs.
- A `RowCircuitStep` is not an `Adj` edge.
- A route budget may contain padded stays; do not call it a shortest-path length without an additional argument.
- Do not declare a same-excess/lower-dimension or lower-excess induction budget polynomial merely because its index is smaller.
- Preserve frozen verification receipts, remove one-shot workflows before integration, and distinguish ordinary deductions, kernel verification, and authenticated Prove2Me acceptance.

## Open PR queue at this handoff

No open PRs remain after merging #185. New work should therefore start from current `main`, not from the historical #171–#185 branches.
