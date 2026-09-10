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
- live status **Open** after the 2026-09-10 circuit-localization publication
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
- circuit structure: the two new localization/obstruction theorems below.

`research/PUBLICATION_INDEX_2026-09-09.md` is a historical 9/9 snapshot. Use the dated 9/10 publication updates and this file for current truth.

## Newly Proved: sharp vertex-to-vertex circuit localization

Two local structural results were kernel-checked, independently flattened/compiled, and then accepted by Prove2Me.

### `Hirsch.row_circuit_common_face_dimension_bound`

- theorem ID `f0e79793-711b-4ada-b276-b4eab1fd0fe8`
- submission ID `b5028624-3b66-4e72-8f8d-5b269a429128`
- verdict **ACCEPTED** / live status **Proved**

For extreme vertices `u,v` of an `n`-row H-polytope in ambient dimension `d`, if `v-u` is a support-minimal row circuit, then

`2 * dim F(u,v) + d <= n + 1`,

where `F(u,v)` is the common face cut out by all nonzero describing rows tight at both endpoints. Equivalently, `2*dim F(u,v) <= n-d+1`.

No simplicity, irredundancy, strict-feasibility, or maximal-step assumption is used.

### `Hirsch.balanced_row_circuit_vertices_share_tight_row`

- theorem ID `73ce6c5c-25d8-46ec-9d77-a9f2b5d7b454`
- submission ID `cf5a5faa-d4d2-419e-8802-62aded7c1e51`
- verdict **ACCEPTED** / live status **Proved**

If `n=2d`, `d>=2`, and two extreme vertices have row-circuit displacement, then they share a **nonzero describing row tight at both endpoints**. Therefore an exactly balanced estranged vertex pair cannot be a single row-circuit step.

This is useful negative information for reduction design: “balanced + estranged + one circuit step” is not a viable target class.

### Verification / publication provenance

- frozen source commit `9f964b8617fbbcae3cf652c130cbdbacd32b0dea`
- source verification Actions run `34495410594`, artifact `10159657523`
- standalone SHA-256s:
  - localization `6d3b6b7aecd9c483d30acdff94ff304afad8a8c45f6948b6c12aba1efc1ec009`
  - balanced obstruction `e9b2a0be5fde78404b9b3456a8936d1ff3fea93be27c4cff0d318d02e27fe4ce`
- publication Actions run `34496281896`, receipt artifact `10160146095`
- Polynomial Hirsch mission comment `ed23703f-6e2a-4199-ab42-bc43bd60e8cd`
- clean re-integration on top of current `main` independently rebuilt the source and the same hash-locked standalone proofs in Actions run `34497418271`.

Only `propext`, `Classical.choice`, and `Quot.sound` appear in the audited Lean declarations. The temporary push-triggered publication workflow was deleted after success.

These theorems do **not** prove edge refinement: circuit status can still be lost after restricting to an irredundant intrinsic presentation of the common face, and neither theorem supplies an edge route.

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

The endpoints may be final vertices created by the cuts. There is no separate strict-centre hypothesis in the public theorem: either one is constructed or a universally tight cut face already equals the final set.

This is not Polynomial Hirsch because the final-face budgets remain hypotheses, and arbitrary circuit/projective evolution is not yet shown to admit the needed clipping representation with polynomial total face cost.

## Exterior-cap / pointed-unbounded line

`Hirsch.simultaneous_clip_diameter_of_exterior_cap`
(`2e20b0a7-503c-4be4-bd9c-446b88f77c8e`) is Prove2Me **Proved**. It assumes an explicit compact exterior-cap witness, strict common centre, old-vertex route bound, and classification of new cap vertices; it proves `D + 1 + sum_i B_i`.

The universal ordinary-mathematical pointed-H-polyhedron cap-existence assembly is not thereby formalized. Keep that distinction explicit.

## Research-only advances — NOT Lean / NOT Proved unless listed above

The later ordinary circuit-localization packet contained more than the two now-Proved theorems. The following remain research-only:

1. **Intrinsic rank-defect accounting.** After restricting a circuit direction to the genuine facets of its common face, circuit status can be lost. With neutral-rank defect `delta`, the ordinary proof gives a resource inequality of the form `(f-h)+delta <= N-D`, and more generally a defect/excess transfer invariant.
2. **Balanced isometric installation.** Ordinary constructions preserve an arbitrary polytope as an isometric face of an exactly balanced ambient polytope while making a selected pair one maximal circuit step. This is a hardness/equivalence diagnostic, not a smaller child.
3. **Optimal defect completion.** With `delta=d-1-r` and excess `e=n-d`, the ordinary proof claims exact minimum excess `e+delta` for proper face-containing circuit completion, plus an exact balanced minimum dimension. Exact finite tests support this but there is no Lean or Prove2Me verdict yet.
4. **Rank-controlled box / cone-carrier cost work.** These give useful ordinary cost bounds in structured representations but do not yet cover arbitrary circuit refinement.

See `research/BalancedIsometricCircuitLocalization.md`, `research/OptimalCircuitDefectCompletion.md`, `research/CONTINUATION_CATCHUP_2026-09-10.md`, and the exact receipts. Do not promote these claims without a kernel/server gate.

## Key structural lesson after localization

A vertex-to-vertex circuit step is now formally known to live in a common face of dimension at most roughly half the facet excess, but **restricting to that face is not automatically a circuit-preserving reduction**. Rows that become intrinsically redundant can carry neutral rank; deleting them can destroy the circuit property. Exact examples already realize this failure.

Therefore the next useful invariant must track both:

- true facet excess of the restricted face, and
- neutral-rank defect of the chosen displacement.

The ordinary research suggests `B = excess + defect` is monotone under face restriction and can be tight, so this bookkeeping alone will not guarantee strict progress. It is nevertheless the right local quantity to formalize before attempting a more global cost argument.

## Highest-value next formal work

1. Formalize a **neutral-row rank characterization** of `IsRowCircuit` in the bounded/vertex setting: the annihilating-row family should have rank `d-1`, equivalently the common kernel should be the line spanned by the circuit direction under the needed hypotheses.
2. Formalize **face-restriction rank-defect transfer** using the published common-face coordinate vocabulary. Target the non-strict invariant first; do not assert automatic descent.
3. Use the now-Proved localization theorem to connect a vertex circuit step to that smaller-dimensional face model, while keeping the possible defect increase explicit.
4. Keep `polynomial_edge_refinement_of_circuit_walks` as the sole Open child. Only create a new decomposition if its children are demonstrably smaller and the parent implication compiles without an ancestor cycle.
5. Continue separating representation/connectivity from polynomial charging. Small support count or low dimension is not itself a graph-distance bound.

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
- `formal/circuit-localization`: frozen source for the two 2026-09-10 circuit-localization theorems.
- `integration/circuit-localization-2026-09-10`: clean byte-for-byte integration of those verified sources onto current `main`.

## Publication / tooling truth

Only an authenticated Prove2Me verdict establishes platform `Proved`. Exact Python certificates and ordinary proofs are research evidence; GitHub Actions compilation establishes kernel/source evidence; do not blur these levels.

Authenticated platform version currently observed: **0.9.9**. Keep the repo-local Prove2Me skill synchronized with upstream before future authenticated work; do not disable version checks.

Credentials remain outside Git. GitHub Actions uses repository secret `PROVE2ME_API_KEY` for publication/audit gates.
