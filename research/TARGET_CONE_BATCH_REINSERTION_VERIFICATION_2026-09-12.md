# Target-cone batch reinsertion: verification receipt

Date: 2026-09-12. PR #168.
Status: pinned Lean kernel build and transitive-axiom audit PASSED.
No Prove2Me registration, proof submission, or authenticated platform claim is
made by this verification.

## Verified source

Successful run head: `cdc769336e9a0baa78264561b2002197a3ee1120`.
The proof correction was committed at
`e1eaab7d540e4af699a5d56ecffe82c4aa80f815`.

SHA-256:

- `Solutions/PolynomialSimultaneousClipParentRoutes.lean`:
  `e53cc06362ad9ec947c6973c81d9558a815f6432e98d367ba814a9bdc00bcb2a`
- `Solutions/PolynomialTargetConeBatchReinsertion.lean`:
  `6585ca981ffa175015be4ea43770c1f95006c3d96ca8591426cb6780e0d34ec1`
- `scripts/check_target_cone_batch_reinsertion.py`:
  `205a9ad1ea9ddfa030f944a01593dffd2cecedf4c8bb85765ace53cdc721a1c8`

Pins: Lean `v4.30.0`, Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Successful final gate

- Actions run: `34675381081`.
- Job: `103504200911`.
- Artifact: `10292341350`, `target-cone-batch-reinsertion-verification`.
- ZIP SHA-256: `50c4011b6b3502443459ccd4f4ebeef12386dd4102dd75c2c8da60ee486f1fd8`.
- Conclusion: success.

The gate validated all three source hashes and both committed pins before
restoring the shared Lean cache. It reran the exact regression, compiled
`Solutions.PolynomialTargetConeBatchReinsertion` and its dependencies, then
freshly elaborated both new modules and audited all seven declarations.

The ZIP was downloaded and independently hashed. Its source-commit file equals
the successful run head. Both complete axiom logs were parsed independently;
each declaration below has exactly the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom theorem axioms.

1. `HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes`
2. `HirschRadial.diamLE_clip_of_strict_centre_with_parent_routes`
3. `HirschRadial.route_clip_from_root_with_parent_routes`
4. `HirschTargetDeletion.compact_cap_star_of_unique_vertex`
5. `HirschTargetDeletion.diamLE_two_of_vertex_star`
6. `HirschTargetDeletion.exists_compact_star_cap_of_target_tight_selection`
7. `HirschTargetDeletion.target_slack_batch_reinsertion_with_parent_routes`

## Exact regression

Two local runs and both hosted runs produced the same exact report digest:
`3106dc044009131b5a0e4ee781e1cbf8288fdab4ff348fcd2d0a27cebcd89fa3`.

- 23 fixtures;
- 99 target vertices;
- 297 compact caps;
- 1,041 capped-vertex occurrences;
- 744 actual apex-edge checks;
- 285 final-face budget calculations;
- 412 lost-original-vertex occurrences;
- 2 negative controls for missing assumptions.

The committed summary is `research/TARGET_CONE_BATCH_EXACT_2026-09-12.json`.
These finite checks are supplementary evidence, not the universal proof.

## First attempt and deterministic correction

This was NOT a first-attempt compilation success.

The first gate, run `34675046464`, job `103503290601`, validated the initial
hashes and exact regression but failed at two implicit region indices in the
new generic adapter. Artifact `10292420752` has ZIP SHA-256
`7fc59b39d0d6889a2beb1e280d11a32056f2bc8ef3ad174cbc9108cfbf31e94c`.

The two occurrences of `hF _` were replaced with the exact already-constructed
indices `hF (.inr (.inl e))` and `hF (.inr (.inr t))`. No theorem statement,
mathematical assumption, target-cone module, or regression changed. The new
adapter hash was pinned and one explicit verification was invoked. That second
run passed. There was no automatic push/synchronize retry loop.

The runtime had no local Lean/Lake installation and direct GitHub access failed
DNS, so local static checks and exact Python tests were not represented as
local kernel compilation.

## Formal result and boundary

For a bounded H-polyhedron P, a target vertex v, and J exactly the inequalities
strictly slack at v, assume a parent-edge route budget B_i between any two
parent vertices on each final face i in J. Those routes may leave the face.
Then the parent has diameter at most `2 + sum_{i in J} B_i`, and v reaches each
parent vertex within `1 + sum_{i in J} B_i`.

The target-tight outer is capped into an actual vertex star. Original vertices
lost under relaxation are recovered by endpoint lifting. All omitted cuts are
restored simultaneously and each final cut-face label is charged once.

The B_i remain hypotheses. Their total and recursive expansion have not been
proved uniformly polynomial. This does not close the Polynomial Hirsch root or
its d>=4 ordinary-edge-refinement leaf. See the companion ordinary proof note
for the precise construction and scope.
