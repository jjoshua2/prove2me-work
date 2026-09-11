# Current Prove2Me Polynomial Hirsch frontier

Updated 2026-09-11 (America/New_York). Repo: `jjoshua2/prove2me-work`.
Latest authenticated publication: **2026-09-11 16:17 UTC**.
Platform: Prove2Me **0.10.1**.
Lean: `v4.30.0` / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

This is the authoritative short handoff. Detailed source hashes, run IDs, and
publication provenance belong in dated files under `research/`. Read current
receipts instead of inferring status from old notes or branch names.

## Executive status

**Polynomial Hirsch is not solved.** The root
`Hirsch.polynomial_hirsch_conjecture`
(`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac`) was authenticated **Open** during the
2026-09-11 mission synchronization.

The general circuit-refinement line remains Open:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks`
  (`099c6686-560c-48fc-b2c2-18b6a620a06e`);
- `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`
  (`73beca40-31bc-42d5-8350-5ec9ac28bd3e`), authenticated **Open** again before
  and after the latest 16:17 UTC publication;
- the separate common-face `h>=6` leaf
  (`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e`);
- ridge-visible access (`5f309362-bbda-4dea-806f-20b4e2712a2d`).

A restricted-family result is not a uniform bound on whole-walk edge-routing
cost. Do not create an ancestor-equivalent or cyclic Open child merely to
restate the missing global argument.

## Six curated milestones — all Proved

The authenticated mission milestone endpoint lists Klee/Klee--Walkup for d<=3,
Larman, Naddef's 0/1 bound, Kalai--Kleitman, Todd's sharpening, and Santos's
bounded counterexample to linear Hirsch. All six are Proved. Their closure
does not close the Polynomial Hirsch root.

## Latest public result: Hirsch with at most three excess rows

`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`

- theorem ID `12426807-9602-4014-bd5e-c69fb43f4cb6`;
- accepted submission `59736803-0e9d-40bb-875d-7ca66b9ccd45`;
- **ACCEPTED / live Proved**, authenticated at 16:17:25 UTC;
- public solution SHA-256
  `58ceb59004e1f9046ccaaf8b55ae39e7e8646135c5c521b8e74b495e7c238568`;
- mission comment `24672cde-eaba-4630-8fa5-025950227067`;
- successful final transaction `34620239467`, artifact `10271654810`.

For EVERY bounded n-row H-polyhedron P in ambient dimension d,

```
n <= d+3  ==>  DiamLE P (n-d).
```

Empty sets, lower-dimensional feasible sets, zero normals, and redundant rows
are included. No strict feasibility or irredundancy is assumed. In particular,
**n<=d+2 gives diameter<=2 without constructing positive normalization weights**.

The source `Solutions/PolynomialLowExcessSectionDescent.lean` proves the
induction using two explicit logical premises matching the already-Proved
`Hirsch.dimension_three_bound` and `Hirsch.facet_reduction`. Its actual source
and independent flattened adapter passed Lean on their first check; all five
printed axiom reports use only standard logical axioms. The public solution
supplies the premises through Prove2Me's tracked imports of those exact Proved
theorems. Prove2Me accepted the resulting unconditional composition.

For d>3, n<=d+3 implies n<2d. Each vertex has >=d distinct NONZERO tight rows,
so any pair shares one. Facet reduction deletes that row and lowers dimension
by one. The row excess n-d is preserved; both endpoints are already in the
section, so there is no access step or multiplying-per-dimension cost. Stop at
the Proved d<=3 base case.

Important API distinction: the public sub-balanced theorem requests intrinsic
bounds for ALL row sections, including zero-row tautologies. Facet reduction
promises an ambient walk. The implementation avoids an invalid composition:
it proves the nonzero common-row fact from the actual checked vertex-span
proof and uses exactly the ambient-walk conclusion of facet reduction.

This is the classical small-excess consequence of low-dimensional Hirsch,
not a new general diameter bound. At arbitrary excess, the induction no longer
ends in a universally small base dimension.

**PR95 is merged** into main at `b03f7e3b43188dd5a1d7131fc21c262807dc2b3f`.
Receipts:
`research/LOW_EXCESS_SECTION_DESCENT_VERIFICATION_2026-09-11.md` and
`research/LOW_EXCESS_SECTION_DESCENT_PUBLICATION_RECEIPT_2026-09-11.md`.
The publication receipt supersedes the earlier verification receipt's pending
publication language.

## Next concrete work: connect the minimum common-face row count

The final common-face adapter is **not yet written or kernel-checked**.
Its mathematical route is now short and does NOT require positive-weight
existence or an abstract facet-count API:

1. Use `commonFaceMinSubpresentation_spec` to choose an equivalent common-face
   coordinate H-presentation with m<=M_min rows.
2. Transfer the known boundedness across its equality of feasible sets.
3. If M_min<=h+3, then m<=h+3. Apply the new public theorem to obtain
   coordinate diameter <=m-h. Pad to three, or to two when M_min<=h+2.
4. Use the already-Proved intrinsic common-face coordinate diameter transfer
   to obtain the same bound for the common face itself.

The target consequences are

```
M_min <= h+2  ==>  intrinsic common-face diameter <=2,
M_min <= h+3  ==>  intrinsic common-face diameter <=3.
```

Relevant interfaces:

- local `HirschCircuitLocalization.commonFaceMinSubpresentation_spec`, in
  `Solutions/PolynomialCommonFaceMinimalSubpresentation.lean`;
- `Hirsch.common_face_diamLE_of_coord_diamLE`, Proved theorem
  `d7b5f979-eb85-47c4-8c1d-a53aff0bccbe`;
- the public small-excess theorem above.

Do not report this adapter as already formalized merely because the component
theorems are Proved. Exact coordinate boundedness, equality rewriting, padding,
and the public/local common-face namespaces must still be assembled correctly.

## Also public: positive normal-relation diameter certificate

`Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations`

- theorem `96cb14a4-aa1b-4d14-93d9-b959e08aa662`;
- original accepted submission `5e888ccf-0f16-48a1-8992-50d3debf1258`;
- **ACCEPTED / live Proved**, authenticated 16:08 UTC;
- standalone SHA-256
  `248851588b10bad874626a17463e9c11b542ac3898146abdbb03530fceb57c27`;
- mission comment `02fb1808-74fc-468e-a0bd-5b7d6e216f86`.

For n=d+2, a reference extreme vertex, positive c, nonconstant t, and

```
sum c_i a_i = 0,
sum t_i c_i a_i = 0,
sum c_i b_i = 1,
```

the H-polyhedron AND every face obtained by making selected original rows tight
have intrinsic padded diameter <=2. The proof identifies the ENTIRE affine
slack image by rank-nullity and transports actual vertices and edges. No
diameter hypothesis or Open research theorem is assumed.

The two source modules are `PolynomialSlackMomentCertificate.lean` and
`PolynomialSlackNormalRelations.lean`. PR92's exact blobs passed all 14 required
source audits. The independent standalone produced 51 standard-axiom-only
reports. A canceled monitor was recovered by querying the SAME existing
submission; no duplicate proof was submitted.

**PR94 is merged**, and historical PR92 is closed as superseded. Source and
publication receipts are `research/SLACK_NORMAL_RELATIONS_*_2026-09-11.md`.

Certificate existence from boundedness alone remains unformalized. Its ordinary
projection/separation and annihilator argument is in
`research/EXCESS_TWO_SLACK_NORMALIZATION_BRIDGE_2026-09-11.md`. It remains useful
for explicit slack coordinates and portals, but is **no longer a prerequisite
for the diameter-only low-excess consequence**.

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
The source preserves/reflects extreme points and segment-face adjacency.
See the two `AFFINE_DIAMETER_TRANSPORT_*_2026-09-11.md` receipts.

### Normalized two-moment diameter two

`Hirsch.normalized_two_moment_slice_diameter_two`
(`e93edd7b-4659-4df5-9eab-fbcce4352c78`), accepted solution
`ea2f94b1-abcf-49bd-8c0e-82423da3839e`, covers all real moments, including
repetitions, degeneracies, and empty slices. Internal classification gives
singletons and low/high pairs; short routes preserve common zero coordinates,
and every coordinate support face has intrinsic diameter <=2.
See `research/EXCESS_TWO_COMPLETION_PUBLICATION_RECEIPT_2026-09-11.md`.

### Irredundant row-count invariance

`Hirsch.irredundant_rows_card_le_any_equivalent_presentation`
(`8538150b-8afe-47ad-94b0-d72189b80264`), accepted solution
`9194432c-54e2-4e6a-9aaf-d7c27fb9934e`, makes strictly feasible irredundant
presentations cardinal-minimal even against descriptions with different
normals/redundancies/tautologies. The common-face minimum is presentation-
independent in that coordinate setting. This is not an abstract facet-count
API. See the row-count publication receipt.

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
extremality, boundedness, irredundancy, strict feasibility, and a compatible
recovered circuit walk. Circuit-walk existence is not the remaining obstacle;
total ordinary edge-routing cost is.

## Other live work learned from the mission board

Sub-balanced section inheritance
`Hirsch.diamLE_le_section_diamLE_of_n_lt_two_d`
(`0e4f233c-418a-4884-bbfb-dbfc7f76bc76`, accepted solution
`19dcd669-189e-4b8c-8a39-d194439f3048`) is Proved. Inspect its exact all-sections
premise before composing it; zero-row sections require care.

Ridge-visible experiments on duals of stacked simplicial polytopes refute a
uniform O(1) bound in that family. An O(n-d)-type hypothesis remains a research
possibility, not a proved bound. Paying an entire facet diameter to reach the
next ridge gives a dimension-multiplicative recurrence, not a fixed exponent.

Public board tools also include product/box diameter, vertex-listing diameter,
common-face 0/1 bounds, and synchronized scalar-height fiber edges. These are
restricted-family infrastructure, not a solution of general face diameter.

## Whole-walk bottleneck

Possible resources are maximal-step self-face progress, row-excess/neutral-rank
charging, compatible blocker swaps, low-excess portals, shared equality
sections, and ridge-visible access. A successful global potential/accounting
argument must prevent repeatedly paying expensive high-dimensional carriers.
Its polynomial exponent must not depend on dimension. Do not assume arbitrary
circuit carriers have excess <=2 or <=3.

## Verification and publication discipline

Keep distinct: finite exact regressions; Lean kernel/axiom evidence; and
Prove2Me ACCEPTED/live Proved. For a composition through already-Proved platform
theorems, report the driver's kernel audit and the platform's tracked dependency
verification separately; do not call locally imported theorem stubs an
axiom-clean standalone proof.

Credentials remain outside Git in `PROVE2ME_API_KEY`; clients authenticate only
to `https://prove2.me/api/v1` with redirects disabled. On a canceled monitor,
recover its existing registration/submission receipt before any retry. No
additional submission is justified merely by an Actions cancellation.

Earlier mission synchronization receipt:
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
