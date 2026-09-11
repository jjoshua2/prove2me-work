# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Latest authenticated result recovery: **2026-09-11 16:17 UTC**.
Platform: Prove2Me **0.10.1**.
Lean: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed provenance belongs in dated
files under `research/`; do not infer status from old notes or branch names.

## Executive status

**Polynomial Hirsch is not solved.** The root
`Hirsch.polynomial_hirsch_conjecture`
(`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`) was authenticated **Open** at the
2026-09-11 mission sync.

The general circuit-refinement line remains Open:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`);
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`), authenticated **Open** before and
  after the latest low-excess publications;
- the separate common-face `h>=6` leaf
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`);
- ridge-visible access (`5f309362-bbda-4dea-806f-20b4e2712a2d`).

A cheap local carrier or a restricted-family result is not a uniform bound on
whole-walk edge-routing cost. Do not create an ancestor-equivalent or cyclic
Open child merely to restate that missing global argument.

## Six curated milestones — all Proved

The authenticated mission milestone endpoint lists Klee/Klee--Walkup for d<=3,
Larman, Naddef's 0/1 bound, Kalai--Kleitman, Todd's sharpening, and Santos's
bounded counterexample to linear Hirsch. All six are Proved. Their closure does
not close the Polynomial Hirsch root.

## Latest public results

### Unconditional small-excess diameter

`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`

- theorem `12426807-9602-4014-bd5e-c69fb43f4cb6`;
- accepted solution `59736803-0e9d-40bb-875d-7ca66b9ccd45`;
- **ACCEPTED / Proved**;
- public solution SHA-256
  `58ceb59004e1f9046ccaaf8b55ae39e7e8646135c5c521b8e74b495e7c238568`.

Every bounded `n`-row H-polyhedron in ambient dimension `d` with `n <= d+3`
has padded graph diameter at most `n-d`, including empty/lower-dimensional
sets, redundant rows, and zero normals. In particular `n <= d+2` gives
diameter <=2 without strict feasibility, irredundancy, or normalization weights.

The local induction driver and independent adapter were kernel/axiom checked.
The public composition imports only the exact already-Proved
`Hirsch.dimension_three_bound` and `Hirsch.facet_reduction` statements, whose
identity/type/status/pin were authenticated before submission. Final publication
run `34620239467`, artifact `10271654810`.

Receipt:
`research/LOW_EXCESS_SECTION_DESCENT_PUBLICATION_2026-09-11.md`.

### Positive normal-relation certificate

`Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations`

- theorem `96cb14a4-aa1b-4d14-93d9-b959e08aa662`;
- original submission `5e888ccf-0f16-48a1-8992-50d3debf1258`;
- **ACCEPTED / Proved**;
- standalone SHA-256
  `248851588b10bad874626a17463e9c11b542ac3898146abdbb03530fceb57c27`.

For `n=d+2`, a reference extreme vertex, positive `c`, nonconstant `t`, and

```text
sum c_i a_i = 0,
sum t_i c_i a_i = 0,
sum c_i b_i = 1,
```

the H-polyhedron AND every face cut out by making selected original rows tight
have intrinsic padded graph diameter <=2. The proof identifies the entire
affine slack image by rank-nullity and transports genuine vertices and edges.
This explicit certificate remains useful even though the unconditional
small-excess theorem now supplies the diameter-only conclusion without proving
certificate existence.

Receipts:
`research/SLACK_NORMAL_RELATIONS_VERIFICATION_2026-09-11.md` and
`research/SLACK_NORMAL_RELATIONS_PUBLICATION_RECEIPT_2026-09-11.md`.

### Common-face minimum-row adapter — kernel verified locally

`HirschCircuitLocalization.commonFace_diamLE_two_of_minCount_le_dim_add_two`

At source commit `6d6b194584e479f8593fdeb76a77ac0ae5df8c0d`, run `34621838819` compiled
and audited the theorem with only `propext`, `Classical.choice`, and `Quot.sound`.
It proves that, assuming the public small-excess H-polyhedron bound, a bounded
common face with

```text
commonFaceMinSubpresentationCount a b u v
  <= commonFaceDim a b u v + 2
```

has **intrinsic** padded graph diameter <=2. The proof uses the existing
irredundant/strict common-face model, presentation-independent minimum row
count, injective affine graph transport, and walk padding. This adapter has not
yet been separately published to Prove2Me at this status snapshot.

### Injective affine graph transport

`Hirsch.injective_affine_image_diameter_iff`
(`c4b0c852-981b-4bd7-8578-07e72315c3c9`) is Proved and transports `DiamLE`
through any injective real affine map, even between different ambient
dimensions. It also preserves/reflects extreme points and actual adjacency.

### Normalized two-moment diameter two

`Hirsch.normalized_two_moment_slice_diameter_two`
(`e93edd7b-4659-4df5-9eab-fbcce4352c78`) is Proved for arbitrary real moments,
including repetitions, degeneracies, empty slices, and coordinate support
faces.

### Irredundant row-count invariance

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`
(`8538150b-8afe-47ad-94b0-d72189b80264`) is Proved and makes strictly feasible
irredundant presentations cardinal-minimal among equivalent finite
presentations. This supports the presentation-independent common-face minimum
row count used above.

## Reusable circuit and routing foundations

Already public Proved results include:

- cubic circuit routing (`9b9a6f06-d05d-41ba-980f-04b905e67562`), with explicit
  `17*n^3` circuit-walk bound;
- maximal circuit-step carrier bound
  (`bfea4b5b-106a-4e52-8297-b8138ca0a294`);
- exact blocker criterion for swapping steps
  (`bd9710b8-067a-4ce6-8ab9-1f6f763133b7`);
- common-face subpresentation excess/defect budget
  (`6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11`);
- neutral-rank/selected-row defect, low-dimensional carrier-edge recognition,
  clipping/repair, rank-sensitive face-cover tools, and maximal-step checkpoint
  progress.

Common-face coordinate normalization is kernel-checked, including endpoint
extremality, boundedness, irredundancy and strict feasibility, as well as a
compatible recovered circuit walk. Circuit-walk existence is not the remaining
obstacle; total ordinary edge-routing cost is.

## What the low-excess result changes

Positive-annihilator existence is no longer required for the **diameter-only**
small-excess base case. Every bounded H-presentation with at most two excess
rows already has diameter <=2 by the direct dimension-descent theorem. The
explicit slack-normalization theorem remains valuable for portal coordinates
and intrinsic selected-row support faces.

The next mission-facing use is the now-kernel-checked common-face adapter:
`M_min <= h+2` implies intrinsic carrier diameter <=2. This is a local carrier
routing result, not a global whole-walk bound and not evidence that arbitrary
circuit carriers satisfy the low-excess condition.

## Other live work learned from the mission board

Sub-balanced section inheritance
`Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d`
(`0e4f233c-418a-4884-bbfb-dbfc7f76bc76`, accepted solution
`19dcd669-189e-4b8c-8a39-d194439f3048`) is Proved. Inspect its exact all-sections
premise before composing it; zero-row sections require care.

Ridge-visible experiments on duals of stacked simplicial polytopes refute a
uniform O(1) bound in that family. An O(n-d)-type hypothesis is still a research
possibility, not a proved bound. Paying an entire facet diameter to reach the
next ridge gives a dimension-multiplicative recurrence, not a fixed exponent.

## Whole-walk bottleneck

Possible resources are maximal-step self-face progress, row-excess/neutral-rank
charging, compatible blocker swaps, low-excess portals, shared equality
sections, and ridge-visible access. A successful global potential/accounting
argument must prevent repeatedly paying expensive high-dimensional carriers.
Its polynomial exponent must not depend on dimension.

## Verification and publication discipline

Keep distinct: finite exact regressions; Lean kernel/axiom evidence; and
Prove2Me ACCEPTED/live Proved. For a composition through already-Proved platform
theorems, report the driver's kernel audit and the platform's tracked dependency
verification separately; do not call locally imported theorem stubs an
axiom-clean standalone proof.

Credentials remain outside Git in `PROVE2ME_API_KEY`; clients authenticate only
to `https://prove2.me/api/v1` with redirects disabled. On a canceled monitor,
recover the exact pending submission receipt and poll it rather than resubmit.

## Mandatory counterexample regressions

Before large new routing claims, test maximal-circuit carrier hexagons/polygons;
coupled commuting-direction ordering obstructions; exact 4D/5D Dantzig
2-face-bridge examples; crossing polygon/cycle and Boolean-cube repair
obstructions; moving-facet intersection loss; 5D incidence-vs-order cost;
balanced cyclic-polar barriers; deformed cubes/single-step universality; and
Q28 scalar-fiber constructions.

Do not infer graph-distance control solely from small support count, small
common-face dimension, low defect, temporal overlap, ambient circuit status,
or presentation-minimality.
