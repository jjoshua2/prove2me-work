# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-12 through merged, kernel-verified PR #186 and authenticated Prove2Me sync PR #187.
Repository: `jjoshua2/prove2me-work`.
Current integrated main: `65cf63c4786210f9bf4ac83bb79873642d26894d`.
Lean: `v4.30.0`; Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first

The remaining research task is **cost-controlled ordinary-edge refinement**. Circuit-walk existence, target-preserving deletion, compact target-star construction, support counting, parent-vertex portal extraction, and pair-specific repair accounting are already available.

The target-anchored repair line now returns the **actual target-slack cut legs used**, including the parent-extreme entry/exit pair on each cut, and charges only those concrete pair-specific local calls. Target-rooted repair localizes its nontrivial cut cost to the endpoint-lift spoke. Radial active-row cells are convex along segments.

PR #186 adds the first genuine decreasing-resource theorem in this line: ambient rows which are strictly slack throughout an actual portal-pair common carrier subtract directly from that carrier's minimum-presentation excess.

No result below proves the global fixed-degree polynomial recurrence. A polynomial number of circuit steps, a bound on the number of used cuts, or independent smaller-looking recursive calls is insufficient unless their total ordinary-edge cost is globally amortized.

## Live Prove2Me state

Authenticated sync run `34697880616`, job `103564398150`, against platform `0.10.3` verified:

- `Hirsch.target_tight_outer_unique_vertex_zero_diameter`
  - theorem `aa3abbb2-203b-41ab-86b6-f45ab734c57a`
  - status **Proved**
- `Hirsch.vertex_strictly_slack_rows_card_le_row_excess`
  - theorem `804b7a8e-0572-4407-a014-2d9f4aaa6f87`
  - status **Proved**
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  - theorem `73beca40-31bc-42d5-8350-5ec9ac28bd3e`
  - status **Open** before and after the sync

Polynomial Hirsch mission discussion comment `f9b857cd-c188-45ca-b8f5-c721538ce5ae` records the current strategy through PR #186. Receipt: `research/PROVE2ME_FRONTIER_SYNC_2026-09-12.md`. No theorem status or frontier edge was changed by the sync.

Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) also remains part of the unresolved edge-refinement line.

Do not create cyclic children through `balanced_polynomial_bound` or broad target-face-access assumptions. Do not call a `RowCircuitStep` an `Adj` edge. Do not redo the already-complete cubic circuit Child A or Santos/spindle work without finding a defect.

## Verified target-anchored chain

### #165–#166 — preserve a fixed target through deletion

Rows strictly slack at a fixed original target vertex can be deleted simultaneously while preserving row-map injectivity, that same target vertex, and exact recovery on reinsertion. Keeping exactly the target-tight rows yields a relaxed outer whose only old vertex is the target. The canonical same-phase blocker deletion gives strict row-excess drop and a fresh cubic circuit walk, but that relaxed walk is still a circuit walk rather than an ordinary-edge route.

### #168, #170 — simultaneous reinsertion

All target-slack cuts can be restored in one clipping construction. With supplied parent-edge budgets on final cut faces, repair cost is additive. The sharp public slack-row count gives at most `n-d` target-slack rows, but a uniform recursive face budget still produces the known multiplicative obstruction.

### #171, #173–#175, #177 — pay only support actually used

Cycle-erased region routing exposes a `Nodup` used support. Simultaneous clipping preserves this support information, separates final cut labels from old-edge labels, and bounds distinct old-edge labels by the original outer budget `D`. Target-cone repair therefore pays only the final cut labels used by the repaired path, never every available cut.

### #178–#179 — retain actual portal geometry

The repair can retain the actual simple region path. In closed extreme-face routing every consecutive region transition has a shared **parent extreme vertex** portal. `RegionLeg` records `(label, entry, exit)`, so local costs may depend on the concrete parent-vertex pair rather than a whole-face diameter.

### #181, #183 — pair-specific target-cone cost

For one simultaneous clipping repair, the final route costs

`D + sum(pair-specific costs of actual used cut legs)`.

#183 specializes this to the target-tight star. Each returned target-slack cut leg:

- has a duplicate-free label among at most `n-d` cuts;
- carries actual parent-extreme `entry` and `exit` vertices;
- both endpoints are tight on that labelled row.

Pairwise repair pays `2 + Σ B(row,entry,exit)` and target-rooted repair pays `1 + Σ B(row,entry,exit)`.

### #182, #185 — one-dimensional radial structure

Target-rooted center-to-outer-vertex motion can use only the old-edge region, so its cut cost is localized to the endpoint-lift spoke.

PR #185 proves:

- each normalized radial row score is affine;
- every fixed-row active cell is convex;
- a row active at both segment endpoints remains active throughout;
- under strict centre slack, the whole retracted segment lies in that final cut face.

Frozen source `fd7511f10153113446dcad73971f091ac6d5f9cf`; run `34692904962`, job `103551222857`, artifact `10297421344`, digest `sha256:038b33fe502c512a91e97f9b5072360acc22e68ee674ef770929083d68999ffc`. Receipt: `research/RADIAL_ACTIVE_ROW_INTERVAL_VERIFICATION_2026-09-12.md`.

### #186 — strict unused rows buy carrier excess savings

Module: `Solutions/PolynomialCommonFaceStrictRowSavings.lean`.

Kernel-checked declarations:

- `HirschCircuitLocalization.irredundant_commonFace_rows_disjoint_strict_rows`
- `HirschCircuitLocalization.commonFace_minExcess_add_strictRows_le`
- `HirschCircuitLocalization.commonFace_minExcess_le_of_strictRows_card`

For a bounded `n`-row parent in dimension `d`, parent vertices `u,v`, and a set `J` of original rows which are strictly slack at **every point** of `commonFace a b u v`, let

- `M = commonFaceMinSubpresentationCount a b u v`,
- `h = commonFaceDim a b u v`.

Then

`(M - h) + J.card ≤ n - d`.

Equivalently, if `n-d ≤ J.card + r`, the actual portal-pair carrier has minimum-presentation excess at most `r`.

The proof uses the globally-minimal strictly-feasible irredundant carrier model. Every selected indispensable row has a feasible coordinate point where exactly that row is tight; mapping that witness into the ambient common face excludes every row strict throughout the carrier. Those excluded rows are disjoint from the selected rows and from the common-source rows which vanish on the carrier. Rank-nullity supplies the remaining `d-h` charge.

Frozen head `7896d786797b67ff3f60957fe6dea37a1ef7ebff`; run `34697559250`, job `103563545980`, artifact `10299296580`, digest `sha256:97b0a239a0c3e7eff33109cd1813fa92e9a0b0ab105519f993238ac7c386c0fb`. All three axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Receipt: `research/COMMON_FACE_STRICT_ROW_SAVINGS_VERIFICATION_2026-09-12.md`.

This is a resource theorem, not itself a diameter theorem.

## Completed interfaces to reuse

### Pointed carrier recursion: #151, #153–#161

- `rowCircuitWalk_explicit_cubic_of_injective` gives a `17*n^3` circuit walk under row-map injectivity, without boundedness.
- Exact neutral-rank / selected-defect / savings identities work under injectivity.
- Nonempty injective H-polyhedra have vertices; intersecting carriers have genuine parent-vertex portals; feasible checkpoint sequences assemble from supplied local parent-edge budgets.
- The same-phase minimum-carrier strict-resource / essential-trapped-blocker split works in pointed unbounded parents.
- `LowerExcessInjectiveHpolyDiameterBound` turns strict excess decrease into a conditional ordinary-edge budget.

**Important:** that lower-excess bound is an induction hypothesis, not a proved global polynomial theorem.

### Cap / facet descent: #140–#152, #164

The exterior-cap line supplies explicit bounded caps, preservation of old vertices/edges at far levels, new cap-vertex classification, and radial horizon repair. #149 gives same-excess/lower-dimension facet routing from an explicit lower-dimensional budget. #164 gives the one-cut `D + 1 + B` wrapper. Naive independent recursion on those budgets is still Pascal-type.

### Small-excess carrier routing

`commonFace_diamLE_of_subpresentation_excess_le_three` converts an actual common carrier of minimum-presentation excess `r ≤ 3` into an intrinsic graph route of cost `r`, using the already-public small-excess H-polyhedron result. This is the intended endpoint of the next support-to-resource argument.

## Highest-value next theorem: shortest used paths force strict rows

The next task is now narrower than the previous handoff: PR #186 already proves the row-savings inequality. What remains is to prove that the **actual used repair geometry supplies the required strict rows**.

### Step 1 — choose a shortest region path before assigning pair costs

Strengthen the generic region-routing interface so a reachable intersection graph chooses a walk `p` with

`p.length = (intersectionGraph S).dist i j`.

Mathlib already provides `Reachable.exists_walk_length_eq_dist` and `Walk.isPath_of_length_eq_dist`.

Prove a reusable chordlessness statement: if `r + 1 < s ≤ p.length`, then

`¬ G.Adj (p.getVert r) (p.getVert s)`.

Otherwise prefix + chord + suffix would produce a shorter `i→j` walk, contradicting `p.length = G.dist i j`.

**Choose this shortest/chordless path before local pair costs are assigned.** A shortcut can change the portal pair and therefore its pair-specific cost.

### Step 2 — convert nonadjacent used cut faces into strict rows

For an actual used cut leg labelled `i`, its `entry` and `exit` lie on row face `F_i`. Their common carrier is contained in `F_i` because row `i` is tight at both endpoints.

If another used cut label `j` occurs nonconsecutively on the shortest full mixed-region path, chordlessness says the two region labels are not adjacent. For compact closed extreme cut faces, nonempty intersection would give a shared parent extreme vertex and hence an intersection-graph edge. Therefore `F_i ∩ F_j = ∅`.

Every point `z` in the portal-pair common carrier is feasible and lies in `F_i`. Since `F_i ∩ F_j = ∅`, row `j` cannot be tight at `z`; feasibility then gives

`⟪a j, z⟫ < b j`.

So each nonneighboring used cut contributes one row eligible for PR #186.

### Desired quantitative consequence

Let

- `e = n-d` be parent row excess,
- `r` be the number of used cut labels on a shortest mixed repair path,
- `c_i ∈ {0,1,2}` count immediate path neighbors of used cut `i` which are themselves cut labels,
- `e_i = M_i-h_i` be the minimum-presentation excess of the actual portal-pair carrier routed inside cut `i`.

Formalize

`e_i + (r - 1 - c_i) ≤ e`,

hence

`e_i ≤ e - r + 1 + c_i ≤ e - r + 3`.

This is the support-versus-subproblem-size tradeoff needed by the current proof line.

### Maximum-support payoff

If a shortest repair uses the maximum `r=e` cut labels, then every actual cut-leg carrier has `e_i ≤ 3`. The existing small-excess carrier theorem can therefore discharge every local ordinary-edge call directly.

Since `Σ c_i ≤ 2(r-1)`, total cut-leg cost is at most `3e-2`; adding distinct old-edge labels gives a route budget

`D + 3e - 2`

for that maximum-support regime, with the zero-support case handled separately.

This would solve a nontrivial support regime outright. It would **not** yet solve few-used-cut cases where a local carrier may retain large excess.

## Proof hygiene / falsifiers

- A merely simple path is insufficient for nonintersection of nonneighbors; use a shortest/chordless path.
- Slackness only at the two portal endpoints is insufficient. PR #186 requires strict slack throughout the common carrier.
- Choose the shortest path before attaching pair-specific costs; do not assume shortcutting decreases those costs.
- A `RowCircuitStep` is not an `Adj` edge.
- `Route R B` may include stays; do not call `B` a shortest-path length without a separate argument.
- Smaller recursion indices do not automatically imply a uniform fixed-degree polynomial.
- Preserve frozen verification receipts, remove one-shot workflows before integration, and distinguish ordinary deductions, kernel verification, and authenticated Prove2Me acceptance.

## Open PR queue at this handoff

No open PRs remain after merging #187. New work should start from current `main`.
