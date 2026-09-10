# Current Prove2Me Polynomial Hirsch frontier

Date: 2026-09-10. Repo: `jjoshua2/prove2me-work`.
Platform observed by authenticated publication: Prove2Me **0.9.9**.
Lean environment remains `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative handoff. Follow the logical dependency graph and explicit verification receipts, not branch timestamps.

## Executive status

Polynomial Hirsch is **not solved**.

The sole formal Open bottleneck remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks`

- theorem ID `099c6686-560c-48fc-b2c2-18b6a620a06e`
- status **Open**
- asks for constants `C,k` so every length-`L` row-circuit walk between vertices of a bounded, irredundant, strictly feasible n-row d-polytope can be replaced by an ordinary edge/stay walk of padded length `C*(n+d)^k*L`.

The replacement need not visit nonvertex circuit intermediates. Constant or dimension-only overhead per circuit step is already false in exact polygon examples; polynomial row-dependent overhead is not ruled out.

Do not create a cyclic child depending back on `balanced_polynomial_bound`, and do not register a one-step or exactly-balanced one-step reformulation as a supposedly smaller child: ordinary reductions in the research notes show those restrictions can retain the full quantitative graph-diameter difficulty.

## Closed work not to redo

The complete Santos / linear-Hirsch counterexample chain is Prove2Me **Proved**, including `five_spindle_length_six`, `spindle_one_step_axis`, `strong_dstep_spindle`, and `santos_counterexample`.

PR #9 split the old prescribed-face leaf into:

```text
polynomial_access_to_given_supporting_face
  -> cubic_circuit_walk_bound                         Proved
  +  polynomial_edge_refinement_of_circuit_walks     Open
```

`Hirsch.cubic_circuit_walk_bound` (`9b9a6f06-d05d-41ba-980f-04b905e67562`) is Proved. Its completed Lean development supplies a concrete `17*n^3` circuit bound. The relaxed circuit-walk half is therefore finished; the remaining difficulty is ordinary graph routing.

## Major public / Proved toolkit

Reusable public results include:

- supporting-face access: `target_face_access_of_local_neutral_rank`, `given_supporting_face_access_of_boundary_residual_rank`, `vertex_exposing_redundant_row_extension`, `given_supporting_face_access_of_boundary_product_factors`;
- cuts: `cut_face_access_of_outer_diameter`, `clipped_diameter_le_outer_add_cut_face`, `cut_face_access_of_unbounded_outer_diameter`, `bounded_clip_diameter_le_outer_add_cut_face_add_one`, `box_slice_diameter_le_dimension`;
- geodesic/common-face: `reentry_splice_through_extreme_face`, `geodesic_face_disjoint_tail_bound`, `geodesic_face_cover_diameter_bound`, `common_face_dimension_tradeoff`, `common_face_effective_count_le_rows_minus_common`, `common_face_diameter_of_effective_rows`, `separated_common_face_split`;
- repair networks: `face_interval_cover_route_bound`, `ordered_damage_repair_exact`, `route_of_faces_and_surviving_edges`, `extreme_face_cut_route_bound`, `mixed_repair_route_or_cut`, `crossing_cube_endpoint_certificate_insufficient`;
- checkpoint/portal family: start/active-containment routing, simultaneous face-preserving vertex selection, compact extreme-face parent-vertex extraction, feasible face-covered sequence routing, and shared-point-to-parent-vertex transfer.

See `research/PUBLICATION_INDEX_2026-09-09.md` and `research/PUBLICATION_UPDATE_2026-09-10.md` for theorem IDs and publication receipts.

## Newly Proved: compact simultaneous clipping

The old `main` status was stale here. PR #53 completed the end-to-end Lean assembly.

Public theorem:

`Hirsch.simultaneous_clipping_diameter_of_compact_outer`

- theorem ID `75d26f37-e0bd-4d73-9128-688fe7d5a80c`
- submission ID `2c038ea7-ebc9-4f22-80c6-328fab2ea613`
- verdict **ACCEPTED**
- live status **Proved**
- verified source commit `446304d56513437aad9c0a02fc1d202e41783259`
- verification Actions run `34485975796`
- publication Actions run `34487272212`
- standalone SHA-256 `fe83809fcda2cc6b2714193964e8f8be6ad2a1705ac4e3383b8dc6621736564f`

Formal content: for compact convex outer `Q`, a finite simultaneous family of halfspace cuts, outer padded graph diameter `D`, and intrinsic padded budgets `B_i` on the **final** exposed cut faces, the final intersection has padded graph diameter

`D + sum_i B_i`.

The endpoints may be final vertices created by the cuts. The final theorem has no separate strict-centre hypothesis: the proof constructs one unless a cut is universally tight, in which case that final cut face already equals the clipped set and its assumed budget closes the case.

This is a genuine all-final-vertex diameter-transfer theorem. It is **not** Polynomial Hirsch because the final-face budgets remain hypotheses, and it does not assert that arbitrary circuit/projective evolution has this clipping representation.

### Verification provenance

The source declaration is `HirschRadial.simultaneous_clipping_diameter_bound` in `Solutions/PolynomialSimultaneousClipDiameter.lean`. Run `34485975796` compiled the complete source chain and public adapter, deterministically flattened the exact dependencies, independently compiled the standalone proof, and audited `solution`. Only `propext`, `Classical.choice`, and `Quot.sound` were reported. Artifact `10155724751` has digest `sha256:ff0ff54c263efd482cded2e7edba27324276094a143264adae49731ed6bbdcfe`.

The first publication attempt safely aborted before registration because authenticated refresh reported platform 0.9.9 while the local publisher expected 0.9.8. After checking the official upstream 0.9.9 skill, the idempotent publisher was retried and received the ACCEPTED verdict above.

## Exterior-cap / pointed-unbounded line

`Hirsch.simultaneous_clip_diameter_of_exterior_cap`
(`2e20b0a7-503c-4be4-bd9c-446b88f77c8e`) is already Prove2Me **Proved**. It assumes an explicit compact exterior-cap witness, strict common centre, old-vertex route bound, and classification of new cap vertices; it proves `D + 1 + sum_i B_i`.

The universal ordinary-mathematical pointed-H-polyhedron cap-existence assembly is not thereby formalized. Keep that distinction explicit.

PR #53 also contains ordinary low-rank cone-carrier cost work (`research/ConeCarrierDescent.md`) with exact regressions. That universal cost theorem is not Lean-formalized.

## Current research-only advances — NOT Lean / NOT Proved

Research-status posts already preserve the quasipolynomial rank-box cost, low-linking-rank direction catalogue, growing-rank weighted-wheel catalogue, single-step universality, simultaneous clipping precursors, unbounded clipping, balanced common-face cost barrier, rank-controlled box precursor, and cone-carrier descent. See `research/RESEARCH_SUBMISSION_STATUS_2026-09-10.md` and `research/RESEARCH_UPDATE_2026-09-10.md`.

Later ordinary results are summarized in `research/CONTINUATION_CATCHUP_2026-09-10.md`:

1. **Circuit localization / rank-defect accounting.** For a vertex-to-vertex row-circuit displacement in an `N`-row `D`-polytope, the minimal common-face dimension obeys `2*h <= N-D+1`. On the irredundant intrinsic face, circuit status can be lost; the proposed defect `delta` satisfies `(f-h)+delta <= N-D`. Exact examples show that removing redundant restricted rows can destroy circuit status even when the ambient direction is realized by an edge elsewhere.
2. **Balanced isometric installation.** Ordinary constructions preserve an arbitrary original polytope as an isometric face of an exactly balanced ambient polytope while making a selected pair one maximal circuit step. This shows balanced one-step refinement is not automatically a smaller problem.
3. **Optimal defect completion.** If `delta=d-1-r` is the missing neutral rank and `e=n-d`, the ordinary proof claims exact minimum excess `e+delta` for proper face-containing circuit completion, plus an exact balanced minimum dimension. These optimality claims have exact finite tests but no Lean proof and no novelty determination.

Do not call these Proved until formalized and accepted.

## Literature boundaries

Primary literature relevant to current claims:

- Borgwardt–Stephen–Yusun, *On the Circuit Diameter Conjecture*, arXiv:1611.08039: wedge methods do not transfer automatically to circuit diameter; realizations matter.
- Borgwardt–Brugger, *Circuits in Extended Formulations*, Discrete Optimization 52 (2024), arXiv:2208.05467: circuits are not generally inherited under projection; noninheritance can be exponentially large.
- Todd, *An improved Kalai–Kleitman bound for the diameter of a polyhedron*, arXiv:1402.3579: established quasipolynomial diameter input used by rank-box work.
- Blanchard–De Loera–Louveaux, *On the Length of Monotone Paths in Polyhedra*, arXiv:2001.09575: established edge-direction/monotone-path input used by direction-catalogue work.
- Natura, *Circuit Diameter of Polyhedra is Strongly Polynomial*, arXiv:2602.06958 (2026): circuit diameter has a strongly polynomial bound, reinforcing that our formal bottleneck is circuit-to-edge routing rather than short circuit walks.
- Dadush–Kober–Koh, *On Circuit Diameter and Straight Line Complexity*, arXiv:2602.05699 (2026): further structural circuit-diameter results.
- Borgwardt–Grewe–Lee, *On the Combinatorial Diameters of Parallel and Series Connections*, arXiv:2203.09587: relevant to structured cross-block repair models.

No exact published statement matching the later sharp defect-completion minima has been located in the initial search. That is not a novelty claim.

## Dead ends / mandatory regressions

Before large formal work, test proposed geometry against:

- exact 4D/5D Dantzig 2-face-bridge counterexamples;
- crossing polygon/cycle and Boolean-cube repair obstructions;
- the moving-facet intersection-loss sweep;
- the 5D incidence-vs-order cost example;
- the maximal-circuit carrier hexagon;
- balanced cyclic-polar cost barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber class, where current constructions have general linear upper bounds.

Do not infer connectivity from chronological overlap, automatic balance from low face dimension, or small graph diameter from a small number of repair supports.

## Highest-value next formal work

1. Keep `polynomial_edge_refinement_of_circuit_walks` as the formal frontier.
2. Use the newly Proved simultaneous-clipping theorem as infrastructure when a genuine outer/clipping model is available; the remaining obligation is to bound the actual final-face costs or supply cheaper inherited-edge shortcuts.
3. From the research-only line, the best focused Lean candidate is the **circuit-localization and rank-defect accounting layer**, because it is reusable and strictly local. Formalize the row-rank/common-face facts before the larger optimal-completion construction.
4. Do not register one-step universality or balanced one-step refinement as new Open children; they are hardness/equivalence diagnostics.
5. Keep representation/connectivity and polynomial charging as separate obligations. A good new Prove2Me decomposition should only be created after the child statements are demonstrably smaller and the parent implication compiles without importing an ancestor.

## Branch map

- PR #9 `chatgpt/circuit-leaf-split`: exact circuit split; Child B Open.
- PRs #13–#26: completed circuit Child A.
- PR #27–#33: geodesic/common-face/effective-row foundation and counterexamples.
- PR #38–#49: damage repair, route/cut certificates, start/active containment and publication gates.
- PR #50 `chatgpt/face-preserving-checkpoints`: face-preserving rounding / radial foundation.
- PR #51: earlier bounded clipping assembly history.
- PR #52 `chatgpt/recession-cap-clipping`: verified exterior-cap theorem, public/Proved.
- PR #53 `chatgpt/verify-simultaneous-clipping`: canonical repaired full bounded clipping source and cone-carrier research; full chain green.
- PR #54: rank-controlled box research; do not prefer its older clipping candidates over PR #53.
- PR #55 merged: shared Lean-cache / Actions cost-control policy.
- `integration/hirsch-catchup-2026-09-10`: durable integration of the verified clipping chain plus late research/status updates.

## Publication / tooling truth

Only an authenticated Prove2Me verdict establishes platform `Proved`. Exact Python certificates and ordinary proofs are research evidence; GitHub Actions compilation establishes kernel/source evidence; do not blur these levels.

Authenticated platform version currently observed: **0.9.9**. The repo-local Prove2Me skill must be synchronized with the 0.9.9 upstream instructions before future authenticated work; do not simply disable version checks.

Credentials remain outside Git. GitHub Actions uses repository secret `PROVE2ME_API_KEY` for publication/audit gates.
