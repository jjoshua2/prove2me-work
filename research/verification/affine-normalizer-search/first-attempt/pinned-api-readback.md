# Exact pinned API, not a compiler result

Read through the native GitHub connector:
leanprover-community/mathlib4 at c5ea00351c28e24afc9f0f84379aa41082b1188f,
Mathlib/Data/Fintype/Card.lean, lines210..265, blob
92b0c19123219c529f84acd7a7db084b2bb3b886.

Inside namespace Fintype with [Fintype alpha] [Fintype beta], the pinned file states:

    theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
      card_le_of_injective _ (Function.injective_surjInv h)

The failed candidate instead referenced Finset.card_le_card_of_surjective,
which was found in newer API documentation but is absent from this pinned
compiler environment. Do not upgrade Mathlib to repair this.

The existing surjection F : S -> T is already constructed. The proposed repair
uses the pinned Fintype theorem and rewrites subtype cardinalities by
Fintype.card_coe. This changes only the final two lines of image_card_of_ties,
not its statement or any other proof. It remains UNCOMPILED and UNAPPLIED to
the publication source. File inspection and a patch round trip are not verification.
