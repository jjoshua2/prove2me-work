# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-11 after PRs #122–#138 and the
accepted high-excess row-block publication.
Repository: `jjoshua2/prove2me-work`.
Lean: v4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first: the hard case has narrowed substantially

Do not repeat the old nonvertex minimum-subpresentation, low-excess, or generic
high-excess-product work. Those layers are now complete.

For a bounded parent and a same-phase maximal row-circuit step, the current
formal reduction removes two broad classes of carriers:

1. **strict resource / lower row excess:** a carrier with
   `M_min-h < n-d` is a genuine lower-row-excess H-polyhedron subproblem and is
   routed by the recursive induction interface;
2. **independent product structure:** high total excess is harmless when a
   minimum carrier presentation decomposes into independent row blocks with
   already-controlled factor diameters; factor costs add.

The remaining structural case is therefore a **saturated, genuinely coupled
minimum carrier** with an **essential same-phase trapped blocker**. The blocker
belongs to an irredundant, strictly feasible, minimum-cardinality carrier model,
is target-only for the local circuit step, strictly slack at the final target,
was already trapped at the phase reference, becomes newly zero at the step
endpoint, and has a single-tight witness certifying indispensability.

Open active work at this update:

- PR #139: bounded one-row deletion / clipping recursion;
- PR #140: deleting one row from a bounded H-presentation leaves the remaining
  row-evaluation map injective (the deletion outer may be unbounded but has no
  lineality / is pointed).

Treat those two as in-progress until their hosted gates are green and merged.

## Formal Open frontier

The sole Polynomial-Hirsch circuit-refinement leaf remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`;
- live status **Open** in the latest authenticated publication transaction.

Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the Polynomial Hirsch root remain
Open. Do not mark any of them solved merely because another carrier class is
cost-controlled.

The existing constructive circuit walk already has length `17*n^3`. Therefore
another polynomial count of carriers is not enough: the remaining theorem needs
a polynomial bound on **total ordinary-edge cost** or a cost-controlled bypass
for the residual hard carriers.

## Public high-excess routing result — new

`Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks`

- theorem ID `27737675-3725-4a3d-92d7-92a87e91031e`;
- accepted submission `78085f91-e27d-4a2d-90ed-5c646a38f8ae`;
- verdict **ACCEPTED** / live **Proved** on Prove2Me 0.10.1;
- mission comment `d27715fd-94c0-42a3-8a25-3da83332e099`;
- publication run `34644738674`, job `103412860556`;
- accepted solution SHA-256
  `e963ae734869955cc55f5166b5d2092c77e80d617fc77ccf7fcdc26694e4a5ec`.

Statement: a nonempty bounded `n`-row H-polyhedron in dimension `d` satisfies
`DiamLE P (n-d)` whenever an explicit invertible linear change of coordinates
splits the complete row presentation into independent factors and every factor
has row excess at most three. Total excess and the number of factors are
unrestricted.

The proof explicitly reuses the already-Proved small-excess theorem
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
(`12426807-9602-4014-bd5e-c69fb43f4cb6`). See
`research/HIGH_EXCESS_ROW_BLOCK_PUBLICATION_RECEIPT_2026-09-11.md`.

Source implementation is `Solutions/PolynomialRowBlockRouting.lean`; hosted
source verification is recorded in
`research/HIGH_EXCESS_ROW_BLOCK_HOSTED_VERIFICATION_2026-09-11.md`.

## Product routing is now a recursive interface, not merely a base case

Merged PR #138 adds

`HirschRowBlocks.hpoly_diamLE_sum_of_row_block_bounds`.

For an explicit row-block product decomposition, **arbitrary proved factor
budgets add**:

```text
factor i has DiamLE B_i  for every i
-------------------------------------
parent has DiamLE (sum_i B_i).
```

No small-excess assumption is used by this transport theorem. Consequently a
nontrivial product decomposition can recursively route harder factors too;
the `<=3` theorem is only one source of factor budgets. This is important for
fixed-exponent induction because independent factor costs add rather than
multiply.

Merged PR #136 connects the product theorem to minimum common-carrier
presentations:

`commonFace_diamLE_minPresentationExcess_of_small_row_blocks`.

If a **minimum equivalent** common-carrier presentation splits into independent
blocks each of excess at most three, its intrinsic graph cost is exactly bounded
by `M_min-h`, even when that number is large.

## Strict branch: real lower-row-excess recursion

Merged PR #133 adds `Solutions/PolynomialLowerExcessCarrierRecursion.lean`:

```text
LowerExcessHpolyDiameterBound R B
commonFace_diamLE_of_minPresentationExcess_lt
feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt
```

The key point is semantic, not merely arithmetic: if
`M_min-h < R`, the common carrier is transported to an actual bounded finite
H-polyhedron of strictly lower row excess, so a genuine induction hypothesis
can be applied without assuming any circuit structure inside the recursive
subproblem.

## Saturated branch: indispensable ordered blocker

Merged PR #130 packages the minimum-presentation same-phase strict/equality
split. Merged PR #131 strengthens the equality branch to an irredundant,
strictly feasible, minimum-cardinality model and an **essential** trapped
blocker with a single-tight witness.

Merged PR #137 packages the current three-way reduction:

`rowCircuitStep_same_phase_recursive_or_factorized_or_essential_trapped_blocker`.

Under the lower-excess induction hypothesis and the small-excess base, every
same-phase maximal circuit step is either:

- recursively solved at lower row excess;
- directly solved by independent small-row-block factorization; or
- nonfactorable and accompanied by the essential trapped-blocker certificate.

The theorem does **not** yet solve the third branch.

## Exact excess/defect accounting and why scalar amortization is insufficient

`Solutions/PolynomialCircuitDeletionSavings.lean` (merged PR #122) proves, for
selected effective rows `F` with `h<=|F|`, the exact identity

```text
e + delta + kappa + s + tau = n-d,
```

and in particular `e + delta + s <= n-d`. Here `e=|F|-h`, `delta` is selected
neutral-rank defect, `kappa` is surplus row disappearance, `s` counts discarded
nonneutral effective rows, and `tau` is discarded-neutral redundancy beyond
rank loss.

This source has now also passed a normal hosted `lake build` and transitive
axiom audit in run `34637525943`, job `103388953563`; all four declarations use
only `propext`, `Classical.choice`, and `Quot.sound`. See
`research/CIRCUIT_DELETION_SAVINGS_HOSTED_VERIFICATION_2026-09-11.md`.

Two exact control families remain important:

1. high carrier excess may have **zero** savings even in balanced genuine-facet
   parents;
2. per-carrier savings do not automatically telescope across a walk, even when
   carriers are distinct.

Do not revive a scalar `e+delta` or savings-sum induction without additional
route-dependent structure.

## Blocker deletion / clipping direction

The next concrete geometric attack is to delete the indispensable blocker row
from the minimum carrier model and later reinsert it as one halfspace cut.

The already-Proved theorem

`Hirsch.simultaneous_clipping_diameter_of_compact_outer`

- theorem ID `75d26f37-e0bd-4d73-9128-688fe7d5a80c`;
- accepted submission `2c038ea7-ebc9-4f22-80c6-328fab2ea613`;

shows that for a compact convex outer region, clipping costs

```text
outer graph cost + sum(final exposed-face costs).
```

For one blocker this is `D + B`.

PR #139 formalizes the bounded deleted-row specialization: if the outer
H-polyhedron after removing the blocker is bounded and has strictly lower row
excess, the induction hypothesis pays its cost and only the final blocker-face
budget remains.

For an unbounded deleted-row outer, historical PR #52 contains a kernel-verified
**exterior-cap-witness** theorem (`HirschExterior.simultaneous_clip_diameter_from_exterior_cap`)
with a universal ordinary-mathematics pointed-polyhedral cap construction. The
explicit cap-witness theorem was verified, but the universal far-cap
existence/classification is not yet a general current-main Lean theorem. PR
#140 is intended to establish the first necessary structural fact on current
main: every one-row deletion outer of a bounded H-presentation is pointed.

Do not silently treat the research-only universal far-cap construction as
kernel-Proved.

## Existing low-excess and carrier composition interfaces

Reuse, do not repackage:

- low-excess H-polyhedra through excess 3 are solved;
- common carrier excess <=2 gives intrinsic diameter <=2;
- common carrier excess <=3 gives intrinsic cost <=3;
- `PolynomialCarrierSmallExcessBudgetRouting.lean` preserves exact additive
  per-carrier budgets;
- `route_of_feasible_commonFace_carrier_budgets` composes intrinsic carrier
  costs into an ordinary parent edge/stay route;
- face-preserving checkpoint/interval machinery already handles nonvertex
  circuit checkpoints.

## Other relevant public Prove2Me results

Among the accepted reusable inputs:

- `Hirsch.common_face_has_subpresentation_faceDim_add_row_excess`, theorem
  `eeac02bd-aa68-48e6-a246-63f921b4606d`, accepted submission
  `e5829063-8890-484e-a67f-9a70c920ee2c`;
- `Hirsch.injective_affine_image_diameter_iff`, theorem
  `c4b0c852-981b-4bd7-8578-07e72315c3c9`;
- `Hirsch.normalized_two_moment_slice_diameter_two`, theorem
  `e93edd7b-4659-4df5-9eab-fbcce4352c78`;
- `Hirsch.irredundant_rows_card_le_any_equivalent_presentation`, theorem
  `8538150b-8afe-47ad-94b0-d72189b80264`;
- `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`, theorem
  `ca4c980f-86d7-4810-be9e-30e473b9dd70`.

Authenticated publication of the high-excess row-block theorem re-read the d>=4
edge-refinement frontier as Open before and after; `frontier_graph_modified` was
false and no conjectural child was created.

## Operational handoff

- `STATUS.md` is authoritative over older plans/handoffs.
- Open PRs are an active work queue; at this update only #139/#140 should be
  active formal lines. Re-fetch before relying on that statement.
- The broad credential-free verifier
  `.github/workflows/verify-circuit-deletion-savings-hosted.yml` is temporary.
  Once the active formal branches are integrated and their evidence is durable,
  remove it rather than leave experiment CI as archival state.
- Publication-only workflows/branches must be removed/closed after receipts are
  durable. The high-excess row-block publication workflow and PR #135 have
  already been cleaned up.
- Credentials remain outside Git in repository secret `PROVE2ME_API_KEY`.
- Never describe source verification as Prove2Me acceptance; never describe the
  ordinary universal pointed-cap construction as Lean-verified until its
  construction/classification layer is actually formalized.
