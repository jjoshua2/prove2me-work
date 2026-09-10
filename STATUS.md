# Current Prove2Me Polynomial Hirsch frontier

Date: 2026-09-10. Repo: `jjoshua2/prove2me-work`.
Platform observed by authenticated publication: Prove2Me **0.9.9**.
Lean environment: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative handoff. Follow the logical dependency graph and explicit verification/publication receipts, not branch timestamps.

## Executive status

Polynomial Hirsch is **not solved**.

The sole formal Open bottleneck remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks`

- theorem ID `099c6686-560c-48fc-b2c2-18b6a620a06e`
- live status **Open** after all 2026-09-10 circuit rank/defect publications
- asks for constants `C,k` so every length-`L` row-circuit walk between vertices of a bounded, irredundant, strictly feasible `n`-row `d`-polytope can be replaced by an ordinary edge/stay walk of padded length `C*(n+d)^k*L`.

The replacement need not visit nonvertex circuit intermediates. Constant or dimension-only overhead per circuit step is already false in exact polygon examples; polynomial row-dependent overhead is not ruled out.

Do not create a cyclic child depending back on `balanced_polynomial_bound`, and do not register a one-step or exactly-balanced one-step reformulation as a supposedly smaller child. The current structural results show why those restrictions can retain, or fail to isolate, the real graph-routing difficulty.

## Closed work not to redo

The complete Santos / linear-Hirsch counterexample chain is Prove2Me **Proved**, including `five_spindle_length_six`, `spindle_one_step_axis`, `strong_dstep_spindle`, and `santos_counterexample`.

PR #9 split the old prescribed-face leaf into:

```text
polynomial_access_to_given_supporting_face
  -> cubic_circuit_walk_bound                         Proved
  +  polynomial_edge_refinement_of_circuit_walks     Open
```

`Hirsch.cubic_circuit_walk_bound` (`9b9a6f06-d05d-41ba-980f-04b905e67562`) is Proved. Its completed Lean development supplies a concrete `17*n^3` circuit bound. The relaxed circuit-walk half is finished; the remaining difficulty is ordinary graph routing.

## Major public / Proved toolkit

Reusable public results include:

- supporting-face access: `target_face_access_of_local_neutral_rank`, `given_supporting_face_access_of_boundary_residual_rank`, `vertex_exposing_redundant_row_extension`, `given_supporting_face_access_of_boundary_product_factors`;
- cuts: `cut_face_access_of_outer_diameter`, `clipped_diameter_le_outer_add_cut_face`, `cut_face_access_of_unbounded_outer_diameter`, `bounded_clip_diameter_le_outer_add_cut_face_add_one`, `box_slice_diameter_le_dimension`;
- geodesic/common-face: `reentry_splice_through_extreme_face`, `geodesic_face_disjoint_tail_bound`, `geodesic_face_cover_diameter_bound`, `common_face_dimension_tradeoff`, `common_face_effective_count_le_rows_minus_common`, `common_face_diameter_of_effective_rows`, `separated_common_face_split`;
- repair networks: `face_interval_cover_route_bound`, `ordered_damage_repair_exact`, `route_of_faces_and_surviving_edges`, `extreme_face_cut_route_bound`, `mixed_repair_route_or_cut`, `crossing_cube_endpoint_certificate_insufficient`;
- checkpoint/portal family: start/active-containment routing, simultaneous face-preserving vertex selection, compact extreme-face parent-vertex extraction, feasible face-covered sequence routing, and shared-point-to-parent-vertex transfer;
- circuit structure: sharp common-face localization, the balanced shared-tight-row obstruction, exact common-face neutral rank, selected-row defect charging, and the equivalent-subpresentation excess/defect theorem documented below.

`research/PUBLICATION_INDEX_2026-09-09.md` is a historical 9/9 snapshot. Use the dated 9/10 publication updates, the explicit receipts, and this file for current truth.

## Proved: sharp vertex-to-vertex circuit localization

### `Hirsch.row_circuit_common_face_dimension_bound`

- theorem ID `f0e79793-711b-4ada-b276-b4eab1fd0fe8`
- submission ID `b5028624-3b66-4e72-8f8d-5b269a429128`
- verdict **ACCEPTED** / live status **Proved**

For extreme vertices `u,v` of an `n`-row H-polytope in ambient dimension `d`, if `v-u` is a support-minimal row circuit, then

`2 * dim F(u,v) + d <= n + 1`.

No simplicity, irredundancy, strict-feasibility, or maximal-step assumption is used.

### `Hirsch.balanced_row_circuit_vertices_share_tight_row`

- theorem ID `73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454`
- submission ID `cf5a5faa-d4d2-419e-8802-62aded7c1e51`
- verdict **ACCEPTED** / live status **Proved**

If `n=2d`, `d>=2`, and two extreme vertices have row-circuit displacement, then they share a **nonzero describing row tight at both endpoints**. Therefore an exactly balanced estranged vertex pair cannot be a single row-circuit step.

Verification provenance for these two results:

- frozen source commit `9f964b8617fbbcae3cf652c130cbdbacd32b0dea`
- source verification Actions run `34495410594`, artifact `10159657523`
- standalone SHA-256s `6d3b6b7aecd9c483d30acdff94ff304afad8a8c45f6948b6c12aba1efc1ec009` and `e9b2a0be5fde78404b9b3456a8936d1ff3fea93be27c4cff0d318d02e27fe4ce`
- publication Actions run `34496281896`, receipt artifact `10160146095`
- Polynomial Hirsch mission comment `ed23703f-6e2a-4199-ab42-bc43bd60e8cd`.

These results do **not** prove edge refinement.

## Newly Proved: circuit neutral rank and common-face defect accounting

The ordinary defect/excess program has now been formalized through the row-presentation level. Keep the word **row-presentation** explicit: the repo still does not have a formal geometric facet-count API for these common faces.

### `Hirsch.row_circuit_common_face_neutral_rank`

- theorem ID `2caa4fd8-0241-4671-b675-531d935970b9`
- submission ID `b1057f03-aaf3-4edb-94f8-03ab51fdb0a3`
- verdict **ACCEPTED** / live status **Proved**
- standalone SHA-256 `b8ed5634d1767f65038eae0949fc522aff3f3ef8565fa84d7b3dbaabf1fb23b7`

For a vertex endpoint `u` and row-circuit displacement `g=v-u`, the ambient neutral rows restricted to the common-direction space have rank exactly

```text
h - 1
```

where `h` is the common-face coordinate dimension. Internally this comes from the stronger kernel statement that the restricted common kernel is exactly the line spanned by `g`.

### `Hirsch.row_circuit_common_face_selected_row_defect_budget`

- theorem ID `3a03179f-7d55-45e7-89bb-a8a13020f396`
- submission ID `7e0e59f5-8e04-4b0d-a473-17269f3b68ff`
- verdict **ACCEPTED** / live status **Proved**
- standalone SHA-256 `f7fe91e5e20341b382fdf809a6b3aa755f60da997b125b5ab03568b0fc15cd35`

For any chosen subset `F` of ambient rows that remain nontrivial on the common-direction space,

```text
|F| + defect(F) + d <= n + h.
```

Equivalently, once `h <= |F|` and `d <= n` are available,

```text
(|F| - h) + defect(F) <= n - d.
```

This formalizes the linear-algebra charging mechanism: deleting `k` effective restricted rows can cost at most `k` units of neutral rank.

The first two rank/defect publications used frozen source commit `a3b23e33d4ce9689c13fc11de4faebf83c102625`, source run `34510652994`, source artifact `10165740340`, publication run `34511247204`, receipt artifact `10166104373`, and mission comment `b5bf4c05-066f-4b71-b093-8f5e11608080`.

### `Hirsch.row_circuit_common_face_subpresentation_excess_defect`

- theorem ID `6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11`
- submission ID `c2c4f32e-f1d5-46c7-8588-1d4ebdfda50f`
- verdict **ACCEPTED** / live status **Proved**
- frozen source commit `47df3997447a3e0494fa7d7480c69e319c2a3564`
- source run `34516191146`, artifact `10167887559`
- standalone SHA-256 `ca39305fe72a000f4e6aa2137b89e6592c34750e2585c339255019ebbaeb2502`
- publication run `34516855383`, receipt artifact `10168146839`
- mission comment `a1f31157-93cc-412a-a041-97f0002ce75a`

If the canonical common-face coordinate H-presentation has an **actual equivalent subpresentation** using at most `M` of the original restricted rows, then one can choose such a subpresentation, delete the selected rows whose restricted normal is zero, and obtain an effective selected set `F` satisfying

```text
h <= |F| <= M
(|F| - h) + defect(F) <= n - d.
```

This is the formally proved row-subpresentation version of the ordinary defect/excess charge. It is stronger than a mere arbitrary-row estimate because `F` comes from an equivalent presentation of the actual common face.

### Repo-internal strengthening: least equivalent row-presentation count

`Solutions/PolynomialCommonFaceMinimalSubpresentation.lean` is now kernel- and axiom-checked. Define `M_min` to be the least number of original common-face coordinate inequalities that give an equivalent H-presentation. The development proves:

- the admissible set of presentation sizes is nonempty;
- zero-normal selected inequalities are tautologies and can be filtered/reindexed without changing the H-polyhedron;
- a minimum witness can therefore be chosen with every selected row effective;
- `h <= M_min`;
- for a row-circuit displacement,

```text
(M_min - h) + defect_min <= n - d.
```

The final internal theorem is

`HirschCircuitLocalization.rowCircuit_commonFace_minSubpresentation_excess_defect`.

It passed the full core axiom gate on source commit `dbb7ccd0164f60506d745dab1e7b7fd0864315c7`, Actions run `34518322328`, artifact `10168716133` (digest `sha256:6deb0dc5ac01cd12b76f784030450f7bd727aec0d8459b9d2000a66ccd6669aa`). Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited declarations.

This minimum-count theorem is intentionally **not** being called a geometric facet theorem. The remaining semantic bridge is to prove that this least equivalent restricted-row count equals the number of genuine facets of the bounded full-dimensional common-face coordinate polytope. Standard polyhedral theory motivates that equivalence, but it is not yet formalized in this repo.

None of the neutral-rank/defect theorems supplies an ordinary edge path, so the edge-refinement frontier remains Open.

## Proved: compact simultaneous clipping

`Hirsch.simultaneous_clipping_diameter_of_compact_outer`

- theorem ID `75d26f37-e0bd-4d73-9128-688fe7d5a80c`
- submission ID `2c038ea7-ebc9-4f22-80c6-328fab2ea613`
- verdict **ACCEPTED** / live status **Proved**
- verified source commit `446304d56513437aad9c0a02fc1d202e41783259`
- verification Actions run `34485975796`
- publication Actions run `34487272212`
- standalone SHA-256 `fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f`

Formal content: for compact convex outer `Q`, a finite simultaneous family of halfspace cuts, outer padded graph diameter `D`, and intrinsic padded budgets `B_i` on the **final** exposed cut faces, the final intersection has padded graph diameter `D + sum_i B_i`.

This is not Polynomial Hirsch because the final-face budgets remain hypotheses, and arbitrary circuit/projective evolution is not yet shown to admit the needed clipping representation with polynomial total face cost.

## Exterior-cap / pointed-unbounded line

`Hirsch.simultaneous_clip_diameter_of_exterior_cap`
(`2e20b0a7-503c-4be4-bd9c-446b88f77c8e`) is Prove2Me **Proved**. It assumes an explicit compact exterior-cap witness, strict common centre, old-vertex route bound, and classification of new cap vertices; it proves `D + 1 + sum_i B_i`.

The universal ordinary-mathematical pointed-H-polyhedron cap-existence assembly is not thereby formalized. Keep that distinction explicit.

## Research-only advances — NOT Lean / NOT Proved unless listed above

The following later ordinary claims remain research-only:

1. **Full genuine-facet defect/excess transfer.** The circuit/common-face row-presentation specialization is now Proved as described above, including a kernel-checked least equivalent row-presentation count. What is not yet formalized is the general face-to-face theorem stated using genuine facets, including the semantic identification of `M_min` with geometric facet count.
2. **Balanced isometric installation.** Ordinary constructions preserve an arbitrary polytope as an isometric face of an exactly balanced ambient polytope while making a selected pair one maximal circuit step. This is a hardness/equivalence diagnostic, not a smaller child.
3. **Optimal defect completion.** With `delta=d-1-r` and excess `e=n-d`, the ordinary proof claims exact minimum excess `e+delta` for proper face-containing circuit completion, plus an exact balanced minimum dimension. Exact finite tests support this but there is no Lean or Prove2Me verdict yet.
4. **Rank-controlled box / cone-carrier cost work.** These give useful ordinary cost bounds in structured representations but do not yet cover arbitrary circuit refinement.

See `research/BalancedIsometricCircuitLocalization.md`, `research/OptimalCircuitDefectCompletion.md`, `research/CONTINUATION_CATCHUP_2026-09-10.md`, and the exact receipts. Do not promote the remaining claims without a kernel/server gate.

## Key structural lesson after defect formalization

A vertex-to-vertex circuit step is formally known to live in a small common face, but **restricting to that face is not automatically a circuit-preserving reduction**. Rows that become intrinsically redundant can carry neutral rank; deleting them can destroy circuit status.

The correct local bookkeeping quantity is now formally established at the row-presentation level:

- presentation excess of the restricted common face, plus
- neutral-rank defect of the chosen displacement.

The proved minimum-presentation inequality shows this combined resource cannot exceed the ambient row excess for an ambient circuit. The ordinary research still indicates that this resource can be tight, so bookkeeping alone does not guarantee strict progress or a graph route.

## Highest-value next formal work

1. Formalize the **genuine-facet bridge** for bounded full-dimensional common-face coordinate polytopes: connect the least equivalent original-row subpresentation count `M_min` to an intrinsic geometric facet count, or introduce a clean public irredundant-presentation notion that can play this role without ambiguity.
2. Generalize the now-Proved circuit/common-face specialization to the full face-to-face defect/excess transfer theorem only after the facet/presentation semantics are explicit.
3. Investigate what extra structure beyond `excess + defect` can actually pay for ordinary edge routing—selected portals, route order, special restricted rows, or a low-cost clipping/carrier representation.
4. Keep `polynomial_edge_refinement_of_circuit_walks` as the sole Open child. Only create a new decomposition if its children are demonstrably smaller and the parent implication compiles without an ancestor cycle.
5. Continue separating representation/connectivity from polynomial charging. Small support count, low face dimension, or small defect budget is not itself a graph-distance bound.

## Mandatory regressions / dead ends

Before large formal work, test proposed geometry against:

- exact 4D/5D Dantzig 2-face-bridge counterexamples;
- crossing polygon/cycle and Boolean-cube repair obstructions;
- the moving-facet intersection-loss sweep;
- the 5D incidence-vs-order cost example;
- the maximal-circuit carrier hexagon;
- balanced cyclic-polar cost barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions, where the current class has linear upper bounds.

Do not infer connectivity from chronological overlap, automatic balance from low face dimension, circuit inheritance from ambient circuit status, or small graph diameter from a small number of repair supports.

## Recent branch map

- PR #9 `chatgpt/circuit-leaf-split`: exact circuit split; Child B Open.
- PRs #13–#26: completed circuit Child A.
- PR #27–#33: geodesic/common-face/effective-row foundation and counterexamples.
- PR #38–#49: damage repair, route/cut certificates, start/active containment and publication gates.
- PR #50 `chatgpt/face-preserving-checkpoints`: face-preserving rounding / radial foundation.
- PR #52 `chatgpt/recession-cap-clipping`: verified/public exterior-cap theorem.
- PR #53 `chatgpt/verify-simultaneous-clipping`: canonical full bounded clipping source; public theorem Proved.
- PR #54: rank-controlled box research; its older clipping candidate is superseded by PR #53.
- PR #55 merged: shared Lean-cache / Actions cost-control policy.
- PR #56 merged: durable clipping and late-research catch-up.
- `formal/circuit-localization`: frozen source for the two sharp circuit-localization theorems.
- `formal/circuit-neutral-rank`: current verified source for neutral-rank, row-deletion, effective-row, subpresentation defect/excess, and minimum-subpresentation developments. Its temporary push-triggered verification workflow was deleted after run `34518322328` passed.
- `publish/circuit-neutral-rank-defect` and `publish/circuit-subpresentation-excess`: isolated publication branches; their one-shot publication workflows were deleted after success.

## Publication / tooling truth

Only an authenticated Prove2Me verdict establishes platform `Proved`. Exact Python certificates and ordinary proofs are research evidence; GitHub Actions compilation establishes kernel/source evidence; do not blur these levels.

Authenticated platform version currently observed: **0.9.9**. Keep the repo-local Prove2Me skill synchronized with upstream before future authenticated work; do not disable version checks.

Credentials remain outside Git. GitHub Actions uses repository secret `PROVE2ME_API_KEY` for publication/audit gates.
