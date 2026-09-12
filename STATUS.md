# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-12 through verified PR #165.
Repository: `jjoshua2/prove2me-work`.
Lean: `v4.30.0`; Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first

The remaining research task is **cost-controlled ordinary-edge refinement**, not circuit-walk existence, pointedness, vertex existence, or rank bookkeeping.

A target-anchored batch-deletion alternative is now available: keeping every row tight at an original target vertex preserves both the target vertex and pointedness. Keeping exactly those rows yields a possibly unbounded outer with that target as its only vertex and hence old-vertex graph diameter zero. The hard cost then lies in restoring the omitted cuts. Do not confuse this zero old-vertex cost with a diameter theorem for the clipped parent.

No result below proves the global fixed-degree polynomial recurrence. Repeated multiplication by polynomial factors, or independent dimension/excess recursions with Pascal-type growth, is not a uniform polynomial proof.

## Recorded formal Open frontier

The latest recorded authenticated platform audit leaves the circuit-refinement leaf

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

Open, theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`.
Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the Polynomial Hirsch root are also recorded Open.

PR #165 did not re-audit or mutate live Prove2Me state. Kernel verification is not platform acceptance.

Do not create cyclic children through `balanced_polynomial_bound` or broad target-face-access assumptions. Do not call a `RowCircuitStep` an `Adj` edge. Do not redo already-complete circuit Child A or Santos/spindle work without finding a defect.

## Latest verified step: PR #165

Module: `Solutions/PolynomialTargetAnchoredDeletion.lean`.
Namespace: `HirschTargetDeletion`.

Seven kernel-checked declarations:

- `selected_rowMap_injective_of_covers_target_tight`
- `selected_vertex_of_covers_target_tight`
- `exists_target_preserving_batch_deletion`
- `selected_tight_outer_extremePoints_eq_singleton`
- `selected_tight_outer_diamLE_zero`
- `exists_zero_diameter_target_outer`
- `same_phase_step_has_target_preserving_blocker_deletion`

For a fixed original vertex v, any batch J of inequalities strictly slack at v can be deleted simultaneously. Exactly n-|J| rows remain; their row map is injective; v remains extreme; reinserting J recovers the original set. No boundedness, full dimensionality, irredundancy, circuit hypothesis, or source-vertex hypothesis is needed for this batch result.

In an actual same-phase maximal circuit step toward vertex target v, a destination blocker is strictly slack at v. Its deletion therefore preserves pointedness AND the target vertex. PR #163's all-vertices-tight exception is impossible in this application. The current checkpoint may still be nonvertex.

Keeping exactly the target-tight rows gives extreme-point set `{v}` and `DiamLE 0`. Other parent vertices may disappear. Arbitrary points of that outer are not automatically reachable by ordinary graph edges, and restoring all missing cuts still has an unproved cost.

Evidence:
- source commit `7533ea8f4a4517d5939bd36665c185d87bdd2ff0`;
- source SHA-256 `1b8e3c801aa4a549728880ce253381aab0317ded1a1ee95c0635c9dea4d62a7e`;
- first final-gate run `34673820743`, job `103499983050`, success;
- artifact `10291368656`, digest `sha256:729f298a800d491102ea05ed48acd4649f1ebecd067e2c568b1253fbafa70017`;
- all seven transitive axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`;
- 212 exact Fraction batch-deletion checks across 30 target vertices and 9 fixtures.

Read `research/TARGET_ANCHORED_DELETION_2026-09-12.md` and the companion `TARGET_ANCHORED_DELETION_VERIFICATION_2026-09-12.md`. The temporary verifier was removed before integration. No Prove2Me submission occurred.

## Completed interfaces to reuse

### Pointed geometry and carrier accounting: #151, #153–#161

- #151: `rowCircuitWalk_explicit_cubic_of_injective` gives a `17*n^3` circuit walk from a feasible source to a vertex target with explicit row-map injectivity, without boundedness. One-row deletion has a matching reindexed wrapper.
- #153: exact neutral rank, selected defect, full five-term excess/savings identity, and direct pointed-deletion specializations need only injectivity.
- #154–#157: nonempty injective H-polyhedra have vertices; row-tight faces and intersecting common carriers have genuine parent-vertex portals; feasible nonvertex checkpoint sequences assemble from local parent-edge budgets.
- #158: neutral rows plus a nonneutral row preserve full rank; two distinct nonneutral rows allow pointed deletion; vertex-starting steps have opposite-sign blockers.
- #159: equivalent nonempty common-face presentations inherit injectivity.
- #160: minimum-carrier same-phase strict-resource/essential-trapped-blocker dichotomy works in pointed unbounded parents.
- #161: `PolynomialPointedLowerExcessCarrierRecursion.lean` turns the strict branch into a quantitative conditional edge budget. Weighted and uniform sequences have costs sum C_i and B*L using genuine portals.

**Important:** `LowerExcessInjectiveHpolyDiameterBound` in #161 remains an explicit hypothesis, not a proved uniform polynomial theorem. Strictness must hold for the carriers to which that theorem is applied.

### One-row cap and repair: #140–#150, #152, #164

Deleting one row from a bounded nonempty parent preserves pointedness. The explicit negative-row-sum cap is coercive, finite cap levels are bounded, and a sufficiently far cap preserves ALL old outer vertices and edges. A cap merely beyond the parent is not sufficient for that preservation; #147 includes the counterexample and stronger far-level construction.

#147 classifies each new capped vertex as adjacent by a genuine capped edge to an old vertex. #146/#148 connect the explicit cap to radial horizon repair. #150 establishes the current exterior-cap assembly, and #152 weakens intrinsic face diameter to ambient parent-edge routing.

#164 provides the integrated one-row wrapper:
`HirschDeletionRouting.hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route`
and its strict-rows specialization. For a bounded parent it gives `D+1+B` from an old deletion-outer graph budget D and a parent-edge routing budget B on the deleted-row face.

#149 supplies a same-excess/lower-dimension facet-routing interface relevant to B. Its numerical bound is still an induction input. Do not declare either budget automatically polynomial.

The target-tight batch outer from #165 can have D=0, but #164 is a ONE-CUT theorem and cannot be applied to a whole batch without the required simultaneous repair argument.

### General nonvertex deletion: #163

`PolynomialNonvertexBlockerDeletion.lean` gives pointed blocker deletion OR a supporting row containing every parent vertex. A budget for that extreme face controls the parent in the exceptional case. #165 eliminates the exception specifically for same-phase steps toward an original vertex target; it does not invalidate the general alternative.

### Existing routing/base tools

Reuse common-face localization, affine graph transport, common-face minimum-presentation invariance, small-excess routing through excess three, independent row-block product budgets, weighted/closed-face covers, simultaneous clipping, and blocker commutation/progress lemmas.

Selected reusable accepted public theorem IDs, as recorded before this pass:
- independent small-row blocks: `27737675-3725-4a3d-92d7-92a87e91031e`;
- common-face subpresentation: `eeac02bd-aa68-48e6-a246-63f921b4606d`;
- injective affine diameter transport: `c4b0c852-981b-4bd7-8578-07e72315c3c9`;
- normalized two-moment diameter two: `e93edd7b-4659-4df5-9eab-fbcce4352c78`;
- irredundant minimum-row count: `8538150b-8afe-47ad-94b0-d72189b80264`;
- common-face excess-two diameter: `ca4c980f-86d7-4810-be9e-30e473b9dd70`;
- compact simultaneous clipping: `75d26f37-e0bd-4d73-9128-688fe7d5a80c`.

The earlier detailed source/receipt map remains in this file's history at commit `f22162470d8b562897972c50e010ea88619d26e8`.

## Next substantive target

Investigate a cost-controlled **batch reinsertion cover for actual same-phase target-positive blockers**, using the surviving target vertex and retained tight rows. The geometry must account for source vertices lost under relaxation and the final exposed-face route costs; the accounting must avoid an exponential recursion tree.

Alternatively sharpen the genuinely coupled saturated carrier bypass with a measurable resource decrease and a globally amortized edge budget. Another polynomial count of circuit steps or blocker labels alone is insufficient.

PR #165 is the target-anchored line; do not duplicate it. Before new work, inspect live open PRs for concurrent work rather than relying on a stale queue in this document. Preserve frozen receipts, merge only kernel-checked source, remove one-shot workflows, and distinguish ordinary deductions, kernel checks, and authenticated Prove2Me acceptance.
