# Injective minimum-carrier dichotomy verification

Date: 2026-09-11.

Frozen theorem source commit: `ce223d7eb21e0f74a5696fbb6b56acca333cf6b4`.

Hosted verification:
- run `34668577620`
- job `103485419223`
- artifact `10290656138`
- digest `sha256:480e5201995af2681da6637417b49fc61d76610e086d97cf30604dbd046fe0cb`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled and axiom-audited the injective/pointed minimum-carrier strict-or-blocker declarations. Only the repository-allowed logical axioms `propext`, `Classical.choice`, and `Quot.sound` occur.

Formal role: the bounded same-phase minimum-carrier dichotomy now survives under explicit row-map injectivity. Thus a same-phase maximal circuit step in a pointed parent has a minimum irredundant strictly feasible common-carrier presentation for which either the selected excess/neutral-defect resource is strict, or an indispensable target-only row was already trapped and becomes newly tight, with the corresponding single-tight witness.

This is a structural reduction, not an ordinary-edge routing theorem. It does not by itself solve the pointed deletion-outer graph cost or the Open d>=4 circuit-to-edge refinement theorem.
