# Hosted verification: injective / one-row-deletion cubic circuit walk

Date: 2026-09-11 (America/New_York)

## Frozen proof source

- branch: `formal/injective-cubic-deletion-walk`
- proof source commit: `03c77f05a6f2876196c9c206ef33ff7e70131d83`
- workflow run: `34666307907`
- job: `103478771634`
- Lean: `4.30.0`
- Mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`

Artifact:

- id: `10289322319`
- name: `injective-deletion-cubic-verification`
- digest: `sha256:6f52c63759e896de55a477537ffe03a79187feac450a44bc3466ce884681cec5`

## Result

Both candidate modules built successfully:

- `Solutions.PolynomialInjectiveCubicCircuitWalk`
- `Solutions.PolynomialOneRowDeletionCubicCircuitWalk`

The axiom audit checked all six public declarations below and found only the accepted logical axioms `propext`, `Classical.choice`, and `Quot.sound`:

1. `HirschCircuit.rowCircuitWalk_explicit_cubic_of_injective`
2. `HirschDeletion.rowsWithout_card_le`
3. `HirschDeletion.hpoly_rowsWithout_eq_deletionOuterSet`
4. `HirschDeletion.rowMap_rowsWithout_injective_of_bounded`
5. `HirschDeletion.rowCircuitWalk_explicit_cubic_of_one_row_deletion`
6. `HirschDeletion.rowCircuitWalk_explicit_cubic_of_deletionOuterSet`

The audit script reported:

`Axiom audit passed: 6 required declarations; 6 reports checked; only standard logical axioms.`

## Mathematical scope

The standard-slice cubic construction does not require boundedness. Once `rowMap a` is injective, every feasible source can reach every vertex target by a padded row-circuit walk of length `17*n^3`.

For a one-row deletion outer of a bounded nonempty parent, existing pointedness gives the required injectivity even when that deletion outer is unbounded. The canonical retained-row presentation is exactly `HirschCapVertices.deletionOuterSet`, so the result applies directly to the exterior-cap outer.

This removes circuit-walk existence as an obstruction in the old-outer term `D` from the current exterior-cap interface. It does **not** give an ordinary edge route or a graph-diameter bound. Circuit-to-edge refinement on the pointed lower-row presentation remains the substantive dynamic problem.

No Prove2Me publication or mutation was performed by this verification run.
