# Current Prove2Me Polynomial Hirsch frontier

Authoritative continuation updated 2026-09-11 after PRs #122–#144 and the
accepted high-excess row-block publication.
Repository: `jjoshua2/prove2me-work`.
Lean: v4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

## Read first: the hard carrier class is now sharply isolated

Do not repeat the old nonvertex minimum-subpresentation, low-excess,
high-excess product, or basic blocker-deletion work. Those layers are complete.

For a bounded parent and a same-phase maximal row-circuit step, the formal
reduction now removes the following classes:

1. **strict row-excess resource:** if `M_min-h < n-d`, the common carrier is an
   actual bounded finite H-polyhedron of strictly lower row excess and is routed
   by the lower-excess induction interface;
2. **independent product structure:** any explicit row-block product
   decomposition can route by the sum of already-proved factor budgets; in
   particular arbitrarily high total excess is harmless when every factor has
   excess at most three;
3. **bounded deletion outer:** if an indispensable blocker row is deleted and
   the resulting lower-row-count outer H-polyhedron remains bounded, the lower-
   excess induction pays the outer cost and reinserting the row costs only the
   diameter of its exposed face.

The unresolved structural class is therefore a **saturated, genuinely coupled
minimum carrier** with an **essential same-phase trapped blocker**, where the
one-row deletion outer is potentially unbounded and/or the exposed blocker face
still has uncontrolled graph cost.

The blocker belongs to an irredundant, strictly feasible, minimum-cardinality
carrier model, is target-only for the local circuit step, strictly slack at the
fixed final target, was already trapped at the phase reference, becomes newly
zero at the step endpoint, and has a single-tight witness certifying that the
row is indispensable.

There are currently **no open pull requests** in the repository. The temporary
hosted verification workflow used for PRs #139–#144 has been removed.

## Formal Open frontier

The sole Polynomial-Hirsch circuit-refinement leaf remains

`Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`

- theorem ID `73beca40-31bc-42d5-8350-5ec9ac28bd3e`;
- live status **Open** in the latest authenticated publication transaction.

Its parent `Hirsch.polynomial_edge_refinement_of_circuit_walks`
(`099c6686-560c-48fc-b2c2-18b6a620a06e`) and the Polynomial Hirsch root remain
Open. Do not mark any of them solved merely because additional carrier classes
are cost-controlled.

The constructive circuit walk already has length `17*n^3`. Another polynomial
count of hard carriers is not enough; the remaining theorem needs a polynomial
bound on **total ordinary-edge cost** or a cost-controlled bypass for the
residual carriers.

## Public high-excess routing theorem

`Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks`

- theorem ID `27737675-3725-4a3d-92d7-92a87e91031e`;
- accepted submission `78085f91-e27d-4a2d-90ed-5c646a38f8ae`;
- verdict **ACCEPTED** / live **Proved** on Prove2Me 0.10.1;
- mission comment `d27715fd-94c0-42a3-8a25-3da83332e099`;
- publication run `34644738674`, job `103412860556`;
- accepted solution SHA-256
  `e963ae734869955cc55f5166b5d2092c77e80d617fc77ccf7fcdc26694e4a5ec`.

Statement: a nonempty bounded `n`-row H-polyhedron in dimension `d` satisfies
`DiamLE P (n-d)` whenever an explicit invertible linear coordinate change
splits the complete row presentation into independent factors and every factor
has row excess at most three. Total excess and the number of factors are
unrestricted.

The proof explicitly reuses the already-Proved theorem
`Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three`
(`12426807-9602-4014-bd5e-c69fb43f4cb6`). See
`research/HIGH_EXCESS_ROW_BLOCK_PUBLICATION_RECEIPT_2026-09-11.md` and
`research/HIGH_EXCESS_ROW_BLOCK_HOSTED_VERIFICATION_2026-09-11.md`.

## Product routing is a recursive interface

Merged PR #138 adds

`HirschRowBlocks.hpoly_diamLE_sum_of_row_block_bounds`.

For any explicit row-block product decomposition, arbitrary proved factor
budgets add:

```text
factor i has DiamLE B_i  for every i
-------------------------------------
parent has DiamLE (sum_i B_i).
```

No small-excess assumption is used by this transport theorem. Thus a nontrivial
product decomposition can recursively route harder factors; the excess-at-most-
three theorem is only one source of factor budgets. Independent factor costs
add rather than multiply.

Merged PR #136 connects the product theorem to minimum common-carrier
presentations:

`commonFace_diamLE_minPresentationExcess_of_small_row_blocks`.

If a minimum equivalent carrier presentation splits into independent blocks of
excess at most three, its intrinsic graph cost is bounded by `M_min-h`, even
when that total excess is large.

## Strict branch: genuine lower-row-excess recursion

Merged PR #133 adds `Solutions/PolynomialLowerExcessCarrierRecursion.lean`:

```text
LowerExcessHpolyDiameterBound R B
commonFace_diamLE_of_minPresentationExcess_lt
feasible_sequence_edge_route_mul_of_carrier_minPresentationExcess_lt
```

If `M_min-h < R`, the common carrier is transported to an actual bounded finite
H-polyhedron of strictly lower row excess. The recursive call does not need any
circuit structure inside the child.

## Saturated branch: essential ordered blocker

Merged PR #130 packages the minimum-presentation same-phase strict/equality
split. Merged PR #131 strengthens equality to an irredundant, strictly feasible,
minimum-cardinality model and an indispensable trapped blocker with a single-
tight witness.

Merged PR #137 packages the current three-way reduction:

`rowCircuitStep_same_phase_recursive_or_factorized_or_essential_trapped_blocker`.

Under the lower-excess induction hypothesis and small-excess base, every
same-phase maximal circuit step is either:

- recursively solved at lower row excess;
- directly solved by independent small-row-block factorization; or
- nonfactorable and accompanied by the essential trapped-blocker certificate.

The third branch is the present target.

## Blocker deletion and clipping: current formal state

The already-Proved theorem

`Hirsch.simultaneous_clipping_diameter_of_compact_outer`

- theorem ID `75d26f37-e0bd-4d73-9128-688fe7d5a80c`;
- accepted submission `2c038ea7-ebc9-4f22-80c6-328fab2ea613`;

shows that clipping a compact convex outer region costs

```text
outer graph cost + sum(final exposed-face costs).
```

For one blocker this is `D+B`.

The one-row deletion program is now formalized much further:

### PR #139 — one-cut lower-excess routing

`Solutions/PolynomialSingleCutLowerExcessRouting.lean` proves:

- `diamLE_inter_halfspace_of_compact_outer`;
- `hpoly_inter_halfspace_diamLE_of_lower_excess_outer`.

If a deleted-row outer H-polyhedron is bounded and has strictly lower row
excess, the induction hypothesis pays the outer cost; reinserting the blocker
costs only the exposed blocker-face diameter.

### PR #141 — automatic finite-row deletion model

`Solutions/PolynomialDirectRowDeletionRouting.lean` proves:

- `hpoly_eq_deleteRow_inter_row` using `Fin.succAbove`;
- `hpoly_diamLE_of_bounded_deleteRow_outer`.

For a `Fin (m+1)` presentation, deleting row `j` gives an explicit `m`-row
outer. Under `d<=m`, its row excess is strictly lower. Thus **bounded blocker
deletion is now an automatic recursive branch**, not an abstract certificate.

### PR #140 — every one-row deletion outer is pointed

`Solutions/PolynomialOneRowDeletionPointedness.lean` proves

`HirschDeletion.rowMapWithout_injective_of_bounded`.

Deleting any single inequality from a nonempty bounded H-presentation leaves
the remaining-row evaluation map injective. The outer may become unbounded, but
it cannot acquire lineality.

### PR #142 — explicit positive cap functional

`Solutions/PolynomialOneRowDeletionCapFunctional.lean` defines

```text
deleteCap(r) = - sum_{i != j} <a_i,r>
```

and proves it is strictly positive on every nonzero recession direction of the
one-row deletion outer. No separation theorem or generic cap direction is
needed.

### PR #143 — every finite explicit cap level is bounded

`Solutions/PolynomialOneRowDeletionCapBounded.lean` proves

- `deletionCappedOuter_isBounded_of_injective`;
- `deletionCappedOuter_isBounded_of_bounded_parent`.

Original inequalities bound remaining row values from above; the negative-row-
sum cap bounds them from below. The remaining-row map therefore lands in a
bounded coordinate box. Mathlib's finite-dimensional
`LinearMap.injective_iff_antilipschitz` and
`AntilipschitzWith.isBounded_preimage` pull boundedness back to the capped
outer.

Thus **every finite cap level is bounded**. A cap only has to be chosen far for
geometric preservation/classification, not for compactness.

### PR #144 — explicit far level beyond the entire parent

`Solutions/PolynomialOneRowDeletionFarCapLevel.lean` proves:

- `exists_far_deletion_cap_level`;
- `deletionCappedOuter_inter_deletedRow_eq_parent`;
- `deletion_cap_face_disjoint_parent`.

Using a closed-ball radius and Cauchy-Schwarz, it chooses an explicit cap level
such that the entire original bounded parent lies **strictly below** the cap,
the capped deletion outer is bounded, and reinserting the deleted blocker row
recovers the parent exactly. Consequently the cap hyperplane is exterior to the
final parent.

### Remaining exterior-cap gap

Historical PR #52 contains a kernel-verified theorem

`HirschExterior.simultaneous_clip_diameter_from_exterior_cap`

which proves the desired clipping diameter bound **given** an exterior-cap
vertex classification: old vertices route in the outer graph and every new cap
vertex lies on the cap and is adjacent to an old vertex. The general far-cap
classification itself was not formalized there.

After PRs #140–#144, the universal construction has formal pointedness, an
explicit coercive cap direction, boundedness for every cap level, an explicit
far level preserving the whole final parent, and exterior separation. The
remaining universal cap theorem is therefore specifically the **new cap
vertex/edge classification** (and then plugging that classification into the
historical cap-witness routing theorem).

Do not claim the universal exterior-cap routing theorem as kernel-Proved until
that classification is completed.

## Exact excess/defect accounting and why scalar amortization is insufficient

`Solutions/PolynomialCircuitDeletionSavings.lean` (merged PR #122) proves

```text
e + delta + kappa + s + tau = n-d,
```

and in particular `e + delta + s <= n-d` for selected effective rows.

Hosted full verification: run `34637525943`, job `103388953563`; all four
transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

Two exact control families remain important:

1. high carrier excess may have zero savings even in balanced genuine-facet
   parents;
2. per-carrier savings do not automatically telescope across a walk, even when
   carriers are distinct.

Do not revive a scalar savings induction without additional route-dependent
structure.

## Reuse these completed interfaces

Do not repackage:

- low-excess H-polyhedra through excess three;
- intrinsic common-carrier excess-two/excess-three routing;
- exact additive carrier budget composition;
- injective affine graph-diameter transport;
- minimum row-count representation invariance;
- normalized two-moment/excess-two routing;
- simultaneous compact-outer clipping;
- the high-excess independent-row-block theorem and generic additive factor
  budgets;
- strict lower-row-excess common-carrier recursion;
- one-row deletion pointedness/cap boundedness/far-level construction.

## Other relevant public Prove2Me results

Among the accepted reusable inputs:

- `Hirsch.common_face_has_subpresentation_faceDim_add_row_excess`, theorem
  `eeac02bd-aa68-48e6-a246-63f921b4606d`;
- `Hirsch.injective_affine_image_diameter_iff`, theorem
  `c4b0c852-981b-4bd7-8578-07e72315c3c9`;
- `Hirsch.normalized_two_moment_slice_diameter_two`, theorem
  `e93edd7b-4659-4df5-9eab-fbcce4352c78`;
- `Hirsch.irredundant_rows_card_le_any_equivalent_presentation`, theorem
  `8538150b-8afe-47ad-94b0-d72189b80264`;
- `Hirsch.common_face_diameter_two_of_rows_le_dim_add_two`, theorem
  `ca4c980f-86d7-4810-be9e-30e473b9dd70`.

Authenticated publication of the high-excess row-block theorem re-read the d>=4
edge-refinement frontier as Open before and after; no theorem graph was modified
and no conjectural child was created.

## Operational handoff

- `STATUS.md` is authoritative over older plans and handoffs.
- The open PR queue is currently empty.
- The temporary deletion verifier has been removed from `main` after all active
  branches passed their hosted gates and were merged.
- Publication-only workflows/branches must be removed/closed after receipts are
  durable; the high-excess row-block publication transaction is already clean.
- Credentials remain outside Git in repository secret `PROVE2ME_API_KEY`.
- Source/kernel verification is not Prove2Me acceptance.
- The next highest-value formal work is **cap vertex/edge classification for the
  explicit one-row deletion far cap**, followed by applying the already-verified
  exterior-cap witness routing theorem. If that route stalls, study the blocker
  exposed face for recursive product structure rather than returning to scalar
  savings accounting.
