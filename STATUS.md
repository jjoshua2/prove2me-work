# Current Prove2Me Polynomial Hirsch frontier

Date: 2026-09-09. Repo: `jjoshua2/prove2me-work`.

This file is the durable handoff for agents. `main` is a conservative baseline;
much of the newest proof development lives on the PR branches listed below.
Do not infer the live frontier merely from which theorem files happen to exist
on `main`.

## Executive status

Polynomial Hirsch is **not solved**.

The old September 6 frontier, `Hirsch.polynomial_access_to_given_supporting_face`,
has been split exactly into a proved circuit-routing child and an open
circuit-to-edge refinement child. The current formal research bottleneck is:

**`Hirsch.polynomial_edge_refinement_of_circuit_walks`**
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) — **Open** on Prove2Me.

Its exact statement asks for constants `C,k` such that every length-`L`
row-circuit walk between vertices of a bounded, irredundant, strictly feasible
`n`-row `d`-polytope can be replaced by an ordinary edge/stay walk of length
`C * (n+d)^k * L`. The replacement does **not** have to visit nonvertex
circuit intermediates.

An authenticated platform audit at 2026-09-09 14:41 UTC confirmed this theorem
Open in the pinned environment. Do not replace it with a cyclic sketch back to
`balanced_polynomial_bound`; that attempted dependency was deprecated.

## Closed work that must not be redone

### Linear Hirsch / Santos

The complete Santos counterexample chain is Proved on the public platform:

- `Hirsch.q28_*` certificate stack through `q28_polar_no_length_five_walk`
- `Hirsch.five_spindle_length_six`
- `Hirsch.spindle_normalize`, `spindle_one_step_axis`,
  `spindle_one_step_from_apex_facet`, `spindle_one_step`,
  `strong_dstep_spindle`
- `Hirsch.santos_counterexample`

`Solutions/Axis*.lean` is historical scratch from before that chain closed.
Do not treat it as a mission blocker.

### Original polynomial reduction scaffolding

Also Proved and reusable:

- `Hirsch.balanced_hpoly_transfer`
- `Hirsch.diameter_bound_of_target_face_access`
- `Hirsch.nonzero_supporting_row_of_distinct_extremes`
- `Hirsch.vertex_tight_rows_span`
- Kalai–Kleitman / Larman / Todd bounds (useful background only; their growth
  is not a fixed polynomial `(n+d)^k`)

The old reduction remains conceptually:

```text
polynomial_hirsch_conjecture
  -> balanced_polynomial_bound
  -> polynomial_target_face_access
  -> polynomial_access_to_given_supporting_face
```

but the final prescribed-face leaf now has the productive circuit split below.

## Current productive split

PR #9 (`chatgpt/circuit-leaf-split`) gives an exact compiled implication:

```text
polynomial_access_to_given_supporting_face
  -> cubic_circuit_walk_bound                         Proved
  +  polynomial_edge_refinement_of_circuit_walks     Open
```

The parent implication preserves the original prescribed-face quantifiers and
chooses the target vertex itself after obtaining an edge refinement.

### Child A is finished

`Hirsch.cubic_circuit_walk_bound`
(`9b9a6f06-d05d-41ba-980f-04b905e67562`) is **Proved** on Prove2Me.
The kernel-checked Natura development proves a concrete cubic circuit route
(including the `17*n^3` standard bound) with no `sorryAx` in the completed
proof chain.

Do not spend time re-formalizing the circuit-diameter side unless a bug is
found in the published statement/proof.

### Child B is the formal frontier

`Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) remains Open.

Known obstruction to overstrengthening it: an exact irredundant polygon family
has a single maximal circuit step whose endpoint graph distance is `n/2` even
in dimension two. Thus constant or dimension-only overhead per circuit step is
false; polynomial row-dependent overhead is not ruled out.

## Major proved supporting toolkit

The following are Prove2Me **Proved** in the same Lean 4.30 / pinned Mathlib
environment and should be reused rather than reproved.

### Supporting-face / cut access

- `Hirsch.target_face_access_of_local_neutral_rank`
- `Hirsch.given_supporting_face_access_of_boundary_residual_rank`
- `Hirsch.vertex_exposing_redundant_row_extension`
- `Hirsch.given_supporting_face_access_of_boundary_product_factors`
- `Hirsch.cut_face_access_of_outer_diameter`
- `Hirsch.clipped_diameter_le_outer_add_cut_face`
- `Hirsch.cut_face_access_of_unbounded_outer_diameter`
- `Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one`
- `Hirsch.box_slice_diameter_le_dimension`

### Geodesic / common-face structure

- `Hirsch.reentry_splice_through_extreme_face`
- `Hirsch.geodesic_face_disjoint_tail_bound`
- `Hirsch.geodesic_face_cover_diameter_bound`
- `Hirsch.common_face_dimension_tradeoff`
- `Hirsch.common_face_effective_count_le_rows_minus_common`
- `Hirsch.common_face_diameter_of_effective_rows`

Useful verified consequences on the GitHub branches include

`dim F(u,x) + dim F(v,x) <= d + (n - 2*d)`

for separated endpoints, and an effective-row model for common faces. The
condition `effectiveCount <= 2*faceDim` is **not automatic**; never silently
assume a lower-dimensional face is balanced.

### Damage / repair routing

Public Prove2Me results:

- `Hirsch.face_interval_cover_route_bound`
  (`11592f65-f434-4fad-9c84-f96cf223c3bf`)
- `Hirsch.ordered_damage_repair_exact`
  (`238cbea9-9f9a-454d-93e5-94344960261e`)
- `Hirsch.route_of_faces_and_surviving_edges`
  (`9eed40c7-03ed-4a02-80b4-1f7404ac05ac`)
- `Hirsch.extreme_face_cut_route_bound`
  (`d3a9d907-a9a7-4564-a718-51d1a1a78889`)
- `Hirsch.mixed_repair_route_or_cut`
  (`92dc970d-1e7c-4bbe-b30c-b781d045360b`)
- `Hirsch.crossing_cube_endpoint_certificate_insufficient`
  (`3672334a-7c8c-4a5d-b95d-8629418d3bba`)
- `Hirsch.face_interval_cover_route_bound_of_start_containment`
  (`ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe`) — published by PR #49,
  submission `6b2c08bc-b2bd-4688-9ab1-019ecf2a98ba`, **ACCEPTED / Proved**

The exact ordered-repair accounting is

`L - removedLength + replacementCost`.

For unordered/crossing repair, chronological overlap alone is not enough.
Actual shared parent vertices / connected repair regions are required.

## Latest geometric continuation: PR #48 / #49

PR #48 (`chatgpt/interval-start-portals`) proves a cleaner sufficient
condition for crossing-interval repair.

If interval `j` starts while interval `i` is active, it suffices that

`w (s j) ∈ F i`.

Because `w (s j)` is already in `F j`, the later start is automatically a
genuine shared parent-vertex portal. A stronger verified corollary assumes
that every checkpoint remains in its support face for the whole active
interval; this implies start containment automatically.

PR #49 successfully published the general start-containment theorem listed
above. The stronger active-containment corollary is kernel-verified in GitHub;
it is not currently recorded here as a separate Prove2Me publication.

The remaining geometric gap is **not** another generic routing lemma. It is to
show that the genuine projective/Pachner/circuit-removal evolution supplies a
fixed checkpoint sequence and a connected family of actual final-polytope
repair supports satisfying a condition such as start/active containment, with
polynomial total cost.

A useful next decomposition, only after checking that the geometry is true,
is roughly:

```text
edge refinement / prescribed-face routing
  -> geometric representation of the real evolution by repair supports
  -> repair-network connectivity (start/active containment or no closed cut)
  -> polynomial total support cost
  -> existing proved repair-routing machinery
```

Keep geometric existence and polynomial charging as separate obligations.
Do not publish a child that merely restates Polynomial Hirsch or creates an
ancestor dependency cycle.

## Dead ends / regression tests

Do not rediscover the following as if they were untested ideas.

- Arbitrary or "select a good" 2-face bridge lemmas are false. PR #31 has
  exact rational 4D and 5D Dantzig counterexamples; products extend one
  specified-facet failure to all higher dimensions.
- Chronological crossing of repair intervals does not imply geometric
  intersection. Cycle/polygon examples and the Proved Boolean-cube theorem
  give exact counterexamples.
- Incidence-only face charging can be much weaker than order-sensitive
  information; PR #27's exact 5D diagnostic has incidence bound 9 while the
  ordered-tail theorem gives the sharp value 5.
- The sparse d-step induction in PR #29 is a conditional diagnostic, not a
  global proof target.
- The Q28 scalar-coupling counterexample program found finite amplification
  but also proved linear upper bounds for the independent scalar-fiber class.
  A serious counterexample program must escape that class, e.g. through
  growing-rank spatial identifications or cross-block cuts.

Use these examples as falsification tests before investing heavily in a new
Lean decomposition.

## Branch / PR map

- PR #9 `chatgpt/circuit-leaf-split` — exact circuit split; Child B is Open
- PRs #13–#26 — completed Natura Child-A proof development
- PR #11 `chatgpt/counterexample-couplings` — Q28/coupling research
- PR #27 `chatgpt/face-reentry-splice` — geodesic/face-routing foundation
- PR #28 / #33 — effective-row common-face work
- PR #30 — common-face dimension tradeoff / splitter
- PR #31 — exact 2-face-bridge counterexamples
- PR #34 `chatgpt/publish-backlog-audit` — publication audit/index
- PR #38 `chatgpt/projective-damage-blocks` — exact damage-repair foundation
- PR #39 — portal-backed crossing repair + crossing obstruction
- PR #40 — exact ordered repair / distinct-support routing packets
- PR #41 — repair-network cuts + Boolean-cube obstruction
- PR #42 — generic route-or-cut framework
- PRs #43–#47 — publication gates for repair results
- PR #48 `chatgpt/interval-start-portals` — start/active-containment geometry
- PR #49 `chatgpt/publish-interval-start-portals` — successful publication

Recent no-op / marker-cleanup commits on a branch do not imply newer
mathematics. Follow the dependency graph and this status file, not commit time.

## Publication truth and environment

A local `lake build` or GitHub Actions compile is not a platform verdict.
Describe a result as Prove2Me Proved only after an authenticated `/verify`
`ACCEPTED` result or an authenticated read of live status.

Current mission environment:

- Lean `v4.30.0`
- Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- authenticated audit observed platform version `0.9.8`

Credentials remain outside Git. `credentials.json` is gitignored; GitHub
Actions uses repository secret `PROVE2ME_API_KEY` for authenticated audit and
publication workflows.
