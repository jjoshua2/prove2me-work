# Injective / one-row-deletion cubic circuit walk verification

Date: 2026-09-11.

Frozen proof source commit: `03c77f05a6f2876196c9c206ef33ff7e70131d83`.

Hosted verification:

- GitHub Actions run: `34666307907`
- job: `103478771634`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- artifact: `10289322319`
- artifact digest: `sha256:6f52c63759e896de55a477537ffe03a79187feac450a44bc3466ce884681cec5`

The following declarations compiled and the repository axiom checker accepted each with only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`:

- `HirschCircuit.rowCircuitWalk_explicit_cubic_of_injective`
- `HirschDeletion.rowsWithout_card_le`
- `HirschDeletion.hpoly_rowsWithout_eq_deletionOuterSet`
- `HirschDeletion.rowMap_rowsWithout_injective_of_bounded`
- `HirschDeletion.rowCircuitWalk_explicit_cubic_of_one_row_deletion`
- `HirschDeletion.rowCircuitWalk_explicit_cubic_of_deletionOuterSet`

Formal consequence: boundedness is not required by the constructive `17*n^3` standard-form circuit walk after row-map injectivity is available. Every one-row deletion outer of a nonempty bounded parent has an injective remaining-row map, so even when that deletion outer is unbounded it admits a cubic row-circuit walk from every feasible point to every vertex.

This is a circuit-walk existence theorem only. It does **not** bound ordinary graph distance in the unbounded deletion outer and does not solve `Hirsch.polynomial_edge_refinement_of_circuit_walks_dim_ge_four`.
