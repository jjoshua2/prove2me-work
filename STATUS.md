# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-11 after PRs #147–#153.
Repository: `jjoshua2/prove2me-work`.
Lean: v4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first: the remaining obstruction is now ordinary-edge refinement on a pointed deletion outer

Do **not** repeat the old nonvertex minimum-subpresentation, low-excess,
high-excess product, blocker-deletion, exterior-cap classification, or intrinsic
blocker-face work. Those layers are complete or have been replaced by stronger
interfaces.

For a bounded parent and a same-phase maximal row-circuit step, the current
formal reduction already removes:

1. **strict row-excess resource:** if `M_min-h < n-d`, the common carrier is a
   bounded H-polyhedron of strictly lower row excess and is routed by the
   lower-excess induction interface;
2. **independent product structure:** explicit row-block decompositions route
   by additive proved factor budgets; factors of excess at most three give the
   accepted high-excess theorem;
3. **bounded one-row deletion:** direct lower-row recursion handles it;
4. **unboundedness as lineality:** deleting one row from a nonempty bounded
   parent preserves injectivity of the remaining row map, so the deletion outer
   is pointed;
5. **far-cap geometry:** there is an explicit coercive cap, every finite cap is
   bounded, a far level can be chosen outside the parent, all far-cap vertices
   are classified as old vertices or cap vertices adjacent to old ones, and old
   edges survive;
6. **cap repair / blocker-face cost:** radial repair plus ambient parent-edge
   routing pays the blocker face only once, and the same-excess/lower-dimension
   facet-reentry theorem supplies that ambient route. The blocker-face term is
   no longer an independent obstruction;
7. **circuit-walk existence in the unbounded deletion outer:** the deletion
   outer has an explicit `17*m^3` row-circuit walk despite being unbounded;
8. **rank/defect accounting in that outer:** exact neutral rank and the full
   excess/defect/savings identity survive under row-map injectivity and hence
   hold directly in the one-row deletion presentation.

The residual exterior-cap quantity is therefore the old deletion-outer
**ordinary-edge cost `D`**. Equivalently: dynamically refine a controlled
row-circuit walk in the pointed lower-row deletion presentation to a graph-edge
walk with polynomial total cost.

Do not call this solved merely because the deletion outer has a polynomial
*circuit* walk. `RowCircuitStep` is not `Adj`.

## Formal Open frontier

The sole Polynomial-Hirsch circuit-refinement leaf remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`;
- live status **Open** in the latest authenticated publication audit.

Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the Polynomial Hirsch root remain
Open.

The standard/slack construction already gives a padded circuit walk of length
`17*n^3`. Another polynomial count of hard carriers is not enough: the missing
result is a polynomial bound on **ordinary graph-edge cost** or a genuine
cost-controlled bypass for the remaining pointed-deletion circuit steps.

Do not create a child that is merely this theorem with one hypothesis renamed,
and do not route through the broad target-face-access conjecture in a cyclic
way.

## Current active pull request

At this update, PR #154 is the only active line:

`Force vertices in nonempty injective H-polyhedra`

It develops a pointed/noncompact replacement for compact extreme-point
existence. Its intended conclusion is that every nonempty finite H-polyhedron
with injective row map has an original vertex, using the verified compact cap
classification. This is useful for generalizing checkpoint rounding to pointed
unbounded deletion outers. Treat it as active until its focused gate resolves;
do not duplicate it on another branch.

## Exterior-cap line: now complete as a reduction to `D`

### PRs #140–#144 — pointed deletion and explicit far cap

The one-row deletion program proves:

- `HirschDeletion.rowMapWithout_injective_of_bounded` — deleting any one row
  from a nonempty bounded H-presentation leaves an injective row map;
- an explicit negative row-sum cap functional is strictly positive on every
  nonzero recession direction;
- `deletionCappedOuter_isBounded_of_injective` and the bounded-parent
  specialization — every finite cap level is bounded;
- an explicit far cap level can be chosen above the whole original parent;
- reinserting the deleted row at that level recovers the parent exactly and the
  cap hyperplane is exterior to it.

Thus unbounded deletion outers are pointed and admit a universal compactifying
cap without adding any geometric mystery.

### PR #147 — universal far-cap vertex/edge classification

`Solutions/PolynomialCompactCapVertexClassification.lean` and
`Solutions/PolynomialOneRowDeletionCapWitness.lean` close the historical cap
classification gap.

For a sufficiently far compact cap:

- every old deletion-outer vertex survives;
- every old deletion-outer edge survives;
- every new capped vertex lies on the cap and is adjacent to an old vertex.

Hosted verification was kernel-green and axiom-clean. Exact finite regressions
are recorded in `research/CAP_VERTEX_CLASSIFICATION_EXACT_SUMMARY_2026-09-11.json`
and the ordinary proof/verification handoff in
`research/COMPACT_CAP_VERTEX_CLASSIFICATION_2026-09-11.md`.

### PR #150 — current-main `D + 1 + B` exterior-cap assembly

`Solutions/PolynomialCurrentExteriorCapRouting.lean` proves the current API
version of the old exterior-cap idea:

- `HirschExteriorCurrent.augmented_route_bound_of_cap_classification`;
- `HirschExteriorCurrent.diamLE_single_clip_of_augmented_outer_routes`;
- `HirschExteriorCurrent.diamLE_single_clip_of_old_routes_and_cap_classification`.

The exact cost is

```text
old deletion-outer graph cost D
+ one cap correction
+ blocker-face budget B.
```

Cap-cap shortcuts are explicitly auxiliary non-edges; radial repair turns them
into one final exposed-face charge before producing a genuine parent edge walk.

Verification receipt:
`research/CURRENT_EXTERIOR_CAP_ROUTING_VERIFICATION_2026-09-11.md`.
Frozen proof source `b196d8927ef4c442435f3081ad42947ac23d8c46`,
run `34657118412`, job `103451829683`.

### PRs #149 and #152 — blocker-face `B` is not independent anymore

PR #149 formalizes same-excess/lower-dimension facet reentry: repeated visits to
one blocker facet can be compressed to one lower-dimensional recursion charge.

PR #152 then weakens the cap repair so the blocker-face budget may be supplied
by an **ambient parent-edge route** between vertices on the final cut face; the
replacement route need not remain intrinsically inside that facet.

Key declarations:

- `HirschRegionRoute.route_of_preconnected_face_cover_with_parent_routes`;
- `HirschExteriorCurrent.diamLE_single_clip_of_augmented_outer_routes_with_parent_face_route`;
- `HirschExteriorCurrent.diamLE_single_clip_of_old_routes_and_cap_classification_with_parent_face_route`.

PR #152 hosted verification: frozen head
`0c80cd57020c412c18ba5d5c9ab01c20a48b7a7c`, run `34666541899`, job
`103479443364`, artifact `10289432337`, digest
`sha256:423119d575a05853262870fafe92db5cf18b1f48c69c110967ed6cbbad6fd61a`.

Consequently `B` is supplied by the dimension-descent mechanism; the remaining
numerical obstruction in this exterior-cap branch is `D`.

## Pointed deletion outer: circuit existence and rank accounting are solved

### PR #151 — cubic row-circuit walks need injectivity, not boundedness

`Solutions/PolynomialInjectiveCubicCircuitWalk.lean` proves

`HirschCircuit.rowCircuitWalk_explicit_cubic_of_injective`.

If `rowMap a` is injective, any feasible source reaches any vertex target by a
padded row-circuit walk of length `17*n^3`, with no boundedness assumption on
`Hpoly a b`.

`Solutions/PolynomialOneRowDeletionCubicCircuitWalk.lean` gives the canonical
finite reindexing of all rows except `j`, proves that it describes exactly
`HirschCapVertices.deletionOuterSet`, inherits row-map injectivity from the
bounded parent, and obtains the cubic walk directly in the potentially
unbounded deletion outer.

Verification receipt:
`research/INJECTIVE_DELETION_CUBIC_VERIFICATION_2026-09-11.md`.
Frozen proof source `03c77f05a6f2876196c9c206ef33ff7e70131d83`, run
`34666307907`, job `103478771634`, artifact `10289322319`, digest
`sha256:6f52c63759e896de55a477537ffe03a79187feac450a44bc3466ce884681cec5`.

This removes **circuit-walk existence** from `D`; it does not provide graph
edges.

### PR #153 — exact neutral rank / defect savings also need only injectivity

New modules:

- `Solutions/PolynomialCircuitInjectiveNeutralRank.lean`;
- `Solutions/PolynomialCircuitInjectiveDeletionSavings.lean`;
- `Solutions/PolynomialOneRowDeletionCircuitDefect.lean`.

Under explicit `Function.Injective (rowMap a)` they prove:

- `d <= n`;
- the neutral kernel of a row circuit is exactly its circuit line;
- exact neutral rank `dimension - 1` in the ambient space and any containing
  subspace;
- exact `commonFaceDim - 1` neutral rank on the circuit common direction;
- selected neutral defect is paid by discarded neutral rows;
- the complete five-term identity
  `e_F + delta + kappa + s + t = n-d`;
- the strengthened omitted-nonneutral-row savings inequality;
- the old budget saturates iff all explicit savings vanish.

The direct one-row deletion specializations prove these statements on the
unbounded deletion presentation itself.

Verification receipt:
`research/INJECTIVE_CIRCUIT_DEFECT_VERIFICATION_2026-09-11.md`.
Frozen proof source `982fc860f539cf46d6a2fd8121d81b11a47f1943`, run
`34666807890`, job `103480243486`, artifact `10289323110`, digest
`sha256:220e678a923d6c94d85df318f1cb355c8c339d61a5ab095898a48af709cd7d4a`.

Therefore the deletion outer does **not** lose the sharp carrier rank/excess
bookkeeping when boundedness is lost. The hard step is dynamic edge routing.

## Earlier completed recursive interfaces to keep reusing

### Strict lower-row-excess recursion

`Solutions/PolynomialLowerExcessCarrierRecursion.lean` includes

- `LowerExcessHpolyDiameterBound`;
- `commonFace_diamLE_of_minPresentationExcess_lt`;
- `feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt`.

If `M_min-h < R`, the common carrier is transported to a bounded finite
H-polyhedron of strictly lower row excess. No circuit structure is needed in the
recursive child.

### High-excess independent row blocks

`HirschRowBlocks.hpoly_diamLE_sum_of_row_block_bounds` adds arbitrary proved
factor budgets across explicit row-block product decompositions.

Public theorem
`Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks`:

- theorem ID `27737675-3725-4a3d-92d7-92a87e91031e`;
- accepted submission `78085f91-e27d-4a2d-90ed-5c646a38f8ae`;
- **ACCEPTED / Proved** on Prove2Me 0.10.1.

It handles arbitrary total excess when every independent factor has excess at
most three.

### Small-excess and carrier-to-edge tools

Reuse rather than restating:

- `row_circuit_common_face_dimension_bound` / common-face localization;
- `row_circuit_step_adj_of_common_face_dim_le_one`;
- excess-two/excess-three intrinsic routing;
- rank-sensitive face covers and weighted cover interfaces;
- affine graph-diameter transport;
- common-face minimum-row-count invariance;
- simultaneous clipping;
- blocker characterization, blocker swaps, same-phase trapped-blocker
  persistence, and saturated blocker progress.

## What to attack next

Highest-value work should address **edge refinement inside a pointed unbounded
one-row deletion presentation** without simply restating the Open theorem.
Promising genuinely smaller interfaces include:

1. generalize compact checkpoint/face-preserving vertex selection to nonempty
   injective H-polyhedra (PR #154 is already pursuing vertex existence; do not
   duplicate it);
2. identify which bounded carrier-to-edge lemmas use compactness only for
   endpoint/checkpoint vertex selection and port those parts to injective
   pointed presentations;
3. exploit the deletion presentation's exact `h-1` neutral rank and savings
   identity to isolate a subclass of its cubic circuit steps that has strictly
   smaller row-excess, dimension, or carrier cost;
4. formulate a step-level pointed-deletion refinement theorem only if it has a
   measurable structural restriction beyond the original Open theorem (for
   example a blocker/horizon condition supplied by the cap construction).

Avoid broad arbitrary-unbounded-diameter claims: those merely move the global
problem. Avoid the old `n=2d` balanced shortcut; the repo's balanced polynomial
bound relies on target-face access and is cyclic here.

## Publication discipline

The Polynomial-Hirsch root and the d>=4 edge-refinement leaf remain Open.
Kernel-green internal lemmas are not automatically public Prove2Me results.
Only claim a theorem as Prove2Me-Proved when an authenticated submission has an
ACCEPTED verdict and durable receipt.

Relevant accepted reusable public results include:

- `Hirsch.common_face_has_subpresentation_faceDim_add_row_excess`, theorem
  `eeac02bd-aa68-48e6-a246-63f921b4606d`;
- `Hirsch.injective_affine_image_diameter_iff`, theorem
  `c4b0c852-981b-4bd7-8578-07e72315c3c9`;
- `Hirsch.normalized_two_moment_slice_diameter_two`, theorem
  `e93edd7b-4659-4df5-9eab-fbcce4352c78`;
- `Hirsch.irredundant_rows_card_le_any_equivalent_presentation`, theorem
  `8538150b-8afe-47ad-94b0-d72189b80264`;
- `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`, theorem
  `ca4c980f-86d7-4810-be9e-30e473b9dd70`;
- `Hirsch.simultaneous_clipping_diameter_of_compact_outer`, theorem
  `75d26f37-e0bd-4d73-9128-688fe7d5a80c`.
