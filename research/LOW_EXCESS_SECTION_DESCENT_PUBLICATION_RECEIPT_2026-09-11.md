# Small-excess Hirsch bound — Prove2Me publication receipt

Authenticated transaction completed **2026-09-11T16:17:25.290732+00:00**.

## Public result

- Theorem: `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`.
- Theorem ID: `12426807-9602-4014-bd5e-c69fb43f4cb6`.
- Accepted submission: `59736803-0e9d-40bb-875d-7ca66b9ccd45`.
- Registration action: **REUSED** (the existing theorem registration was reused after the earlier monitor was canceled).
- Proof verdict: **ACCEPTED**.
- Authenticated final theorem status: **Proved**.
- Platform **0.10.1**, Lean **4.30.0**.
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

For every bounded H-polyhedron P in ambient R^d described by n linear inequalities,

    n <= d + 3  ==>  DiamLE P (n - d).

The subtraction is natural subtraction. Empty sets, lower-dimensional feasible sets, redundant inequalities, and zero normals are included. No strict feasibility or irredundancy is assumed. Thus n<=d+2 gives padded diameter<=2, and n<=d+3 gives padded diameter<=3.

This is the classical small-excess consequence of low-dimensional Hirsch, not a new polynomial diameter theorem for arbitrary excess.

## Exact proof and verification provenance

- Frozen source commit: `2774702c54078cb8efae7bed185ed1b4b93bce5b`.
- `Solutions/PolynomialLowExcessSectionDescent.lean`, Git blob `794126103cc9d9f60a95eb262d96d282f3e9ad4f`.
- Actual finite-perturbation vertex-span source blob: `673e5a68f154b66556d01dd81977107329a3415e`.
- Independent driver SHA-256: `d58e8dcb92d9ee1d21f330a64432c6b0d7b880ba6c44c803dd39bf33bc0deb1a`.
- Public solution SHA-256: `58ceb59004e1f9046ccaaf8b55ae39e7e8646135c5c521b8e74b495e7c238568`.

The source and independent driver first compiled successfully in run `34619780682`, job `103330569162`, before that publication monitor was canceled. The successful final transaction was:

- Actions run `34620239467`, **success**;
- job `103332327256`, **success**;
- execution head `23b52d36d7479ef83dcf84663441c8651cdfa1ba`;
- artifact `10271654810`, `low-excess-descent-final-proof`;
- artifact SHA-256 `8ab4205200f170189f6da2189195b37274c5c3f5bec1b5b350b2f62e01dea71d`;
- artifact contains 19 packet, audit, dependency, and publication-receipt files.

The final run reproduced the same driver hashes, built the actual source, compiled its independent flattened driver, and audited four required declarations/five printed reports. Every report used only `propext`, `Classical.choice`, and `Quot.sound`.

## Important distinction: driver audit versus public composition

The auditable driver has two explicit logical premises, with types matching:

1. `Hirsch.dimension_three_bound`, Proved theorem `cf588038-4ee8-4c90-b034-348c28d0da21`;
2. `Hirsch.facet_reduction`, Proved theorem `11b3500a-b9f8-4b44-94aa-d71354441ddb`.

It imports actual local proof source and no theorem stubs. The public unconditional solution supplies these two established premises using Prove2Me's tracked theorem imports. The authenticated publisher checked both exact statements, theorem names, Proved statuses, and Mathlib pins before submission. Prove2Me then accepted the unconditional composition.

The source/driver kernel audit and the platform's tracked dependency verification are distinct evidence. Do not claim a local theorem-stub import was an independently axiom-clean unconditional proof. No Open theorem or new conjectural child is used as a dependency.

## Mathematical argument

At each vertex, the nonzero active row normals span the ambient direction space. Evaluating directions on them is injective, so each vertex has at least d distinct nonzero tight rows. If n<2d, any two such row sets intersect in a genuinely nonzero row.

Induct on d. For d<=3, use the established Hirsch theorem, treating an empty polyhedron vacuously. For d>3, n<=d+3 implies n<2d. Both endpoints lie in the equality section of a shared nonzero row, and both remain extreme in that section. Facet reduction deletes that inequality and reduces ambient dimension by one. The induction hypothesis applies with unchanged row excess:

    (n-1) - (d-1) = n-d.

Both endpoints were already in the section, so no access step or multiplicative cost is added. The ambient edge/stay walk returned by facet reduction has the same n-d budget.

The nonzero-row qualification is deliberate. The public sub-balanced theorem requires bounds for all intrinsic row sections, including zero-row tautologies; facet reduction only supplies an ambient walk. The implementation avoids an invalid composition of those interfaces by proving the nonzero intersection lemma and using the precise ambient-walk conclusion directly.

## Mission communication and unchanged frontier

- Mission: The Polynomial Hirsch Conjecture.
- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`.
- New mission-board comment: `24672cde-eaba-4630-8fa5-025950227067`.
- The theorem and accepted-solution references were resolved.
- `frontier_graph_modified: false`.
- `new_conjectural_children: 0`.

The transaction read the d>=4 circuit-to-edge frontier `73beca40-31bc-42d5-8350-5ec9ac28bd3e` as **Open** before and after publication.

## What changes in the next-work plan

Positive normalization-weight existence is no longer a prerequisite for the diameter-only low-excess base case. Explicit slack normalization remains useful for constructing portal coordinates, and its certificate-to-geometry implication has separately been accepted in PR94.

The next small adapter is: select an equivalent common-face coordinate subpresentation of size m<=M_min, apply this theorem when M_min<=h+3, pad to the desired bound, and transport the coordinate walk to the intrinsic common face. In particular M_min<=h+2 yields diameter<=2. This final common-face adapter is a mathematical consequence; it has NOT yet been written or checked in the current source and should not be reported as separately formalized.

The general high-dimensional common-face, ridge-visible, circuit-to-edge, and Polynomial Hirsch difficulties remain. This proof reduces dimension to a fixed small base only when excess is at most three; it does not bound the remaining balanced problem for arbitrary excess.

All compilation recorded here was hosted. The editing conversation did not have a confirmed functioning local Lean runtime.
