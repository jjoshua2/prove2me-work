# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Latest authenticated synchronization: 2026-09-11 15:28 UTC.
Live platform: Prove2Me **0.10.1**.
Lean environment: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed verification/publication
provenance belongs in dated files under `research/`; do not infer status from
branch names or old notes.

## Executive status

**Polynomial Hirsch is not solved.** The live root

`Hirsch.polynomial_hirsch_conjecture`

- theorem ID `58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`
- authenticated status **Open** at the 2026-09-11 sync.

The circuit-refinement line is also still Open:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`) — **Open**;
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`) — **Open**.

A separate current high-dimensional diameter leaf is
`Hirsch.common_face_diameter_of_dim_ge_six`
(`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`) — **Open**.
The ridge-visible route is represented by
`Hirsch.polynomial_access_to_ridge_visible_vertex`
(`5f309362-bbda-4dea-806f-20b4e2712a2d`) — **Open**.

Do not mark any of these solved merely because a local carrier, low-dimensional
family, or one circuit step has a cheap edge route. A global proof still has to
bound total ordinary edge-routing cost over a whole circuit walk with constants
whose exponent is independent of dimension.

## Curated mission milestones

The live `/missions/.../milestones` endpoint returned **six milestones, all
Proved**:

1. Klee / Klee--Walkup: Hirsch for `d ≤ 3`;
2. Larman 1970: `n * 2^(d-3)` diameter bound;
3. Naddef 1989: the `0/1`-polytope bound;
4. Kalai--Kleitman 1992: quasi-polynomial bound;
5. Todd 2014: `(n-d)^(log₂ d)` sharpening;
6. Santos 2012: bounded counterexample to the original linear Hirsch bound.

These milestones are historical/formal foundations. Their closure does not
imply the Polynomial Hirsch root is closed.

## Latest public / Prove2Me-Proved repository results

### Injective affine graph-diameter transport

`Hirsch.injective_affine_image_diameter_iff`

- theorem ID `c4b0c852-981b-4bd7-8578-07e72315c3c9`;
- submission ID `d0300dfb-691d-4388-8d4d-878c28b9cddf`;
- verdict **ACCEPTED** / live status **Proved**;
- standalone SHA-256
  `3036e68ec71afc54cf927b4daf40062a26eb62fee9b8b1891b8ccd5b6f403032`.

For an injective affine map between real modules, any set `P`, and any natural
bound `B`,

```text
DiamLE (f '' P) B  ↔  DiamLE P B.
```

The source also preserves/refects extreme points and genuine segment-face
adjacency. Ambient dimensions may differ; surjectivity onto the target ambient
space is not required. This is exactly the graph-semantics transport needed for
higher-dimensional slack-coordinate embeddings.

Source verification run `34611873550`; publication run `34612388187`; mission
comment `77e5b93c-2e87-4444-aded-11d6e75f15ae`.
Receipts:
`research/AFFINE_DIAMETER_TRANSPORT_VERIFICATION_2026-09-11.md` and
`research/AFFINE_DIAMETER_TRANSPORT_PUBLICATION_RECEIPT_2026-09-11.md`.

### Normalized two-moment slices have diameter at most two

`Hirsch.normalized_two_moment_slice_diameter_two`

- theorem ID `e93edd7b-4659-4df5-9eab-fbcce4352c78`;
- submission ID `ea2f94b1-abcf-49bd-8c0e-82423da3839e`;
- verdict **ACCEPTED** / live status **Proved**;
- standalone SHA-256
  `45e96aecc53c63bfd394ebc11a2ee196b958534cd93fe1f648c281dad8072317`.

For arbitrary real moments and target value, the nonnegative simplex slice

```text
Σ s_i = 1,
Σ t_i s_i = μ
```

has padded vertex-edge graph diameter at most **2**, including repeated moments
and degenerate/empty cases. Internally, every vertex is classified as an
equal-moment singleton or a low/high pair point; the chosen two-step route can
preserve every coordinate that is zero at both endpoints, so every coordinate
support face also has intrinsic diameter at most two.

Source/standalone gate `34605987684`; publication run `34606984246`; mission
comment `fb10586a-11b4-40fa-944c-673c7a28f5ea`.
Receipt: `research/EXCESS_TWO_COMPLETION_PUBLICATION_RECEIPT_2026-09-11.md`.

### Irredundant row-count invariance

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`

- theorem ID `8538150b-8afe-47ad-94b0-d72189b80264`;
- submission ID `9194432c-54e2-4e6a-9aaf-d7c27fb9934e`;
- verdict **ACCEPTED** / live status **Proved**.

A strictly feasible irredundant finite H-presentation is cardinal-minimal among
all equivalent finite H-presentations, even when the comparison uses different
normals, duplicates, redundancies, or zero-normal tautologies. The common-face
adapters make the existing least-row count presentation-independent in the
strictly feasible irredundant coordinate setting; this is still not an abstract
facet-count API.

Mission comment `33f2c225-aae0-458b-8c98-8575c4e453c5`.
Receipt: `research/IRREDUNDANT_ROW_COUNT_PUBLICATION_RECEIPT_2026-09-10.md`.

### Circuit-step structure already public

The following remain Prove2Me **Proved** and reusable:

- `Hirsch.cubic_circuit_walk_bound`
  (`9b9a6f06-d05d-41ba-980f-04b905e67562`), with explicit `17*n^3`
  circuit-walk bound;
- `Hirsch.maximal_row_circuit_step_common_face_bound`
  (`bfea4b5b-106a-4e52-8297-b8138ca0a294`);
- `Hirsch.row_circuit_step_swap_iff_tight_blockers`
  (`bd9710b8-067a-4ce6-8ab9-1f6f763133b7`);
- `Hirsch.row_circuit_common_face_subpresentation_excess_defect`
  (`6f9c87a4-0a7c-4e6b-8f11-bda5ca40cc11`);
- the earlier neutral-rank, selected-row defect, low-dimensional carrier-edge,
  clipping/repair, and rank-sensitive face-cover infrastructure.

These provide real accounting resources but do **not** yet show that all
carrier-routing costs sum to a uniform polynomial multiple of circuit-walk
length.

## Progress pulled from Prove2Me during the 2026-09-11 sync

The board contains useful results that were newer than this repository's prior
`STATUS.md` snapshot.

### Sub-balanced section inheritance — Proved

`Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d`

- theorem ID `0e4f233c-418a-4884-bbfb-dbfc7f76bc76`;
- accepted solution `19dcd669-189e-4b8c-8a39-d194439f3048`;
- live status **Proved**.

When `n < 2d`, two vertices cannot have disjoint tight-row sets, so diameter can
be reduced to equality sections. This is complementary to the excess-two slack
slice route and should be reused rather than reproved.

### Ridge-visible access research

The latest board research log reports that ridge-visible distance is not
`O(1)` on duals of stacked simplicial polytopes. Sample experiments reached
values such as `8` for `d=3, n=24`, while remaining consistent with an
`O(n-d)`-type hypothesis. The key obstruction is that reaching a chosen ridge
by paying an entire `(d-1)`-facet diameter gives a dimension-multiplicative
recurrence (`d!` / `n^{O(d)}` style), not a fixed-exponent polynomial.

The associated theorem
`Hirsch.polynomial_access_to_ridge_visible_vertex`
(`5f309362-bbda-4dea-806f-20b4e2712a2d`) remains **Open**.

Other board contributions now public include product-diameter, axis-aligned
box diameter, vertex-listing diameter, common-face `0/1` diameter, and
synchronized scalar-height fiber-edge lemmas. Treat these as reusable toolkit,
not as closure of the high-dimensional leaf.

## Active repository direction: slack normalization

The graph transport and normalized two-moment target are now both public
**Proved**. The next concrete bridge is therefore geometric/algebraic:

> turn a bounded low-row-count H-presentation into an exact normalized
> two-moment slack slice.

Desired common-face interface:

```text
M_min ≤ h + 2  ⇒  intrinsic common-face diameter ≤ 2.
```

Current ordinary proof plan (not yet kernel-verified):

1. handle the empty/degenerate cases separately;
2. use boundedness to rule out a nonzero nonnegative vector in the row-map
   range;
3. obtain a strictly positive annihilating row weight via projection/separation
   of the simplex from that range;
4. normalize positive slacks so the first annihilator becomes `Σ s_i = 1`;
5. because row excess is at most two, choose a second annihilator giving the
   second moment equation;
6. prove the two equations characterize the **entire** affine slack image, not
   just contain it;
7. invoke `injective_affine_image_diameter_iff` and the public two-moment
   diameter-two theorem.

The mathematical handoff is in
`research/EXCESS_TWO_SLACK_NORMALIZATION_BRIDGE_2026-09-11.md`.
Do **not** report this normalization or the `M_min ≤ h+2` consequence as Proved
until Lean compilation/axiom audit and, if published, Prove2Me acceptance exist.
Do not assume arbitrary circuit carriers automatically have row excess ≤ 2.

## Whole-walk bottleneck

Even after a low-excess carrier base case is formalized, Polynomial Hirsch
needs a whole-walk argument. Possible resources now include:

- maximal-step self-face progress;
- row excess / neutral-rank defect charging;
- exact blocker criteria for commuting steps;
- support-preserving diameter-two portals in low-excess carriers;
- sub-balanced equality-section inheritance;
- ridge-visible access if a fixed-exponent bound can be found.

A successful potential/accounting theorem must prevent repeatedly paying an
expensive high-dimensional carrier. Local diameter bounds alone are not enough.

## Verification discipline

Evidence levels remain distinct:

1. exact Python/regression checks = finite computational evidence;
2. Lean build + axiom audit = kernel/source evidence;
3. independently audited `solution.lean` + Prove2Me **ACCEPTED / Proved** =
   public platform evidence.

Only level 3 establishes public `Proved`. Credentials stay outside Git in the
repository secret `PROVE2ME_API_KEY`; authenticated clients use only
`https://prove2.me/api/v1` with redirects disabled.

Latest bidirectional sync receipt:
`research/PROVE2ME_HIRSCH_SYNC_2026-09-11.md`.
Mission reconciliation comment:
`0d87f2f5-42c6-45cb-ad21-6ba88a670dfd`.

## Mandatory counterexample regressions

Before large new routing claims, test against at least:

- maximal-circuit carrier hexagon / polygon examples;
- coupled commuting-direction ordering obstruction;
- exact 4D/5D Dantzig 2-face-bridge examples;
- crossing polygon/cycle and Boolean-cube repair obstructions;
- moving-facet intersection-loss sweep;
- 5D incidence-vs-order cost example;
- balanced cyclic-polar cost barriers;
- deformed cubes / single-step universality;
- Q28 scalar-fiber constructions.

Do not infer graph-distance control merely from small support count, small
common-face dimension, low defect, temporal overlap, ambient circuit status, or
presentation-minimality by itself.
