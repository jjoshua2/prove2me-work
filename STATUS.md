# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Latest authenticated result recovery: **2026-09-11 16:08 UTC**.
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
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`), authenticated **Open** again before
  and after the latest slack-publication recovery;
- the separate common-face `h>=6` leaf
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`);
- ridge-visible access (`5f309362-bbda-4dea-806f-20b4e2712a2d`).

A cheap local carrier or a restricted-family result is not a uniform bound on
whole-walk edge-routing cost. Do not create an ancestor-equivalent or cyclic
Open child merely to restate that missing global argument.

## Six curated milestones — all Proved

The authenticated mission milestone endpoint lists Klee/Klee--Walkup for d<=3,
Larman, Naddef's 0/1 bound, Kalai--Kleitman, Todd's sharpening, and Santos's
bounded counterexample to linear Hirsch. All six are Proved. Their closure
does not close the Polynomial Hirsch root.

## Latest public result: positive normal-relation certificate

`Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations`

- theorem `96cb14a4-aa1b-4d14-93d9-b959e08aa662`;
- original submission `5e888ccf-0f16-48a1-8992-50d3debf1258`;
- **ACCEPTED / Proved**, authenticated 16:08 UTC;
- standalone SHA-256
  `248851588b10bad874626a17463e9c11b542ac3898146abdbb03530fceb57c27`;
- mission comment `02fb1808-74fc-468e-a0bd-5b7d6e216f86`.

For n=d+2, a reference extreme vertex, positive c, nonconstant t, and

```
sum c_i a_i = 0,
sum t_i c_i a_i = 0,
sum c_i b_i = 1,
```

the H-polyhedron AND every face cut out by making selected original rows tight
have intrinsic padded graph diameter <=2. The proof identifies the ENTIRE
affine slack image by rank-nullity and transports genuine vertices and edges.
No diameter hypothesis or Open research theorem is assumed.

**Certificate existence from boundedness alone is not part of this theorem.**

The two source modules are `PolynomialSlackMomentCertificate.lean` and
`PolynomialSlackNormalRelations.lean`. PR92's exact source blobs passed 14
required axiom audits in run `34615241828`. The independent standalone in run
`34618047572` compiled and produced 51 standard-axiom-only reports. Its monitor
was canceled while the server submission was pending; recovery run
`34620227081` read the SAME submission as ACCEPTED/Proved and posted its missing
board linkage. No duplicate proof was submitted.

Receipts:
`research/SLACK_NORMAL_RELATIONS_VERIFICATION_2026-09-11.md` and
`research/SLACK_NORMAL_RELATIONS_PUBLICATION_RECEIPT_2026-09-11.md`.

## Direct small-excess descent — new complementary route

PR95 (`formal/low-excess-section-descent`) contains
`Solutions/PolynomialLowExcessSectionDescent.lean`.

The driver and its independent adapter have passed Lean compilation and axiom
auditing in run `34619780682`. At this handoff its unconditional Prove2Me
composition is being checked; **no public acceptance is established here**.

Target:

```
bounded Hpoly a b and n <= d+3  ==>  DiamLE (Hpoly a b) (n-d).
```

Empty sets, lower-dimensional feasible sets, zero normals, and redundant rows
are included. The only external library inputs are the already-Proved
`Hirsch.dimension_three_bound` and `Hirsch.facet_reduction`, represented as
explicit propositions in the axiom-audited driver. The public solution supplies
those inputs using tracked imports of the exact two Proved platform theorems.

For d>3, n<=d+3 implies n<2d. Each vertex has >=d distinct NONZERO tight rows,
so any two vertices share one. Reduce to its equality section, lowering both
row count and ambient dimension by one. The excess n-d is preserved, both
endpoints already lie in the section, and no access step or multiplicative
cost is added. Stop at the Proved d<=3 base case.

Important API correction: the public sub-balanced theorem asks for intrinsic
diameter bounds on ALL row sections, including zero-row tautologies, whereas
`facet_reduction` promises an ambient walk. The implementation therefore proves
the short nonzero-row intersection lemma from the actual checked vertex-span
proof and applies the ambient facet-walk conclusion directly.

This route makes positive-annihilator existence unnecessary for the
**diameter-only** small-excess consequence. In particular, once the public
composition is confirmed, n<=d+2 gives diameter<=2 without normalization
weights. Combine an equivalent small common-face subpresentation with intrinsic
coordinate transport for the M_min<=h+2 corollary. The same route covers h+3
with diameter<=3. It does not give a uniform polynomial at arbitrary excess.

Ordinary argument: `research/LOW_EXCESS_BY_SECTION_DESCENT_2026-09-11.md`.

## Previously public graph and row-semantics tools

### Injective affine graph transport

`Hirsch.injective_affine_image_diameter_iff`
(`c4b0c852-981b-4bd7-8578-07e72315c3c9`), accepted solution
`d0300dfb-691d-4388-8d4d-878c28b9cddf`, proves

```
DiamLE (f '' P) B <-> DiamLE P B
```

for any injective affine map between real modules, any P, and any natural B.
Equal ambient dimensions and surjectivity onto the codomain are not required.
The source preserves/reflects extreme points and actual segment-face adjacency.
Source gate `34611873550`; publication `34612388187`; mission comment
`77e5b93c-2e87-4444-aded-11d6e75f15ae`. See the two affine-transport receipts.

### Normalized two-moment diameter two

`Hirsch.normalized_two_moment_slice_diameter_two`
(`e93edd7b-4659-4df5-9eab-fbcce4352c78`), accepted solution
`ea2f94b1-abcf-49bd-8c0e-82423da3839e`, covers all real moments, including
repetitions, degeneracies and empty slices. Internal classification gives
singletons and low/high pairs; short routes preserve common zero coordinates,
and every coordinate support face has intrinsic diameter <=2.

Standalone SHA-256 `45e96aecc53c63bfd394ebc11a2ee196b958534cd93fe1f648c281dad8072317`.
Source gate `34605987684`; publication `34606984246`; comment
`fb10586a-11b4-40fa-944c-673c7a28f5ea`. See the excess-two completion receipt.

### Irredundant row-count invariance

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`
(`8538150b-8afe-47ad-94b0-d72189b80264`), accepted solution
`9194432c-54e2-4e6a-9aaf-d7c27fb9934e`, makes strictly feasible irredundant
presentations cardinal-minimal even against descriptions with different
normals/redundancies/tautologies. The common-face minimum is therefore
presentation-independent in that coordinate setting. This is not an abstract
geometric facet-count API. See the row-count publication receipt.

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
  clipping/repair, and rank-sensitive face-cover tools.

Common-face coordinate normalization is kernel-checked, including endpoint
extremality, boundedness, irredundancy and strict feasibility, as well as a
compatible recovered circuit walk. Circuit-walk existence is not the remaining
obstacle; total ordinary edge-routing cost is.

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

Public board tools also include product/box diameter, vertex-listing diameter,
common-face 0/1 bounds, and synchronized scalar-height fiber edges. These are
restricted-family infrastructure, not a solution of general face diameter.

## Remaining explicit slack-normalization work

The certificate-to-geometry implication is now public Proved. The remaining
existence construction uses boundedness to separate the simplex from the
row-map range, obtains a strictly positive annihilating weight, treats zero
weighted slack mass separately, and chooses an independent second annihilator
when needed. The ordinary argument is in
`research/EXCESS_TWO_SLACK_NORMALIZATION_BRIDGE_2026-09-11.md`.

Do not report that existence construction as kernel-verified. Do not assume
arbitrary circuit carriers have excess <=2. The section-descent route above
means explicit normalization is no longer the only path to the low-excess
diameter corollary.

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

Previous mission synchronization receipt:
`research/PROVE2ME_HIRSCH_SYNC_2026-09-11.md`, board comment
`0d87f2f5-42c6-45cb-ad21-6ba88a670dfd`.

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
