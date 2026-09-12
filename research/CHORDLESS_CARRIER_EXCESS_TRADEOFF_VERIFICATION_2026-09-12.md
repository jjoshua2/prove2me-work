# Chordless carrier excess tradeoff verification

Date: 2026-09-12.

Frozen theorem head: `0bd3c11469fdc32da2ce7da4b352ecacae2b1d57`.

Hosted verification:
- run `34699503940`
- job `103568639195`
- artifact `10299901583`
- artifact digest `sha256:6c8a99852da873bfd3102780b81577c3ca2d1d408bc9e0f9ba99a604817be6e7`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The first and only hosted gate built `Solutions.PolynomialChordlessCarrierExcessTradeoff`, ran the source directly through Lean, and transitive-axiom-audited:
- `HirschCircuitLocalization.commonFace_minExcess_add_selected_sub_three_le_of_chordless_rowFaces`
- `HirschCircuitLocalization.commonFace_minExcess_le_three_of_chordless_maximal_rowFace_support`

The gate completed successfully and the strict axiom checker accepted only the repository-standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx` was accepted.

## Formal contribution

Let a chordless parent-vertex face path have a selected finite support `cuts`, injectively identified with original H-presentation rows, with each selected face exactly the corresponding row face. For a fixed selected cut `i` and actual parent extreme portal vertices `p,q` tight on its row, the theorem proves

`(M_min(p,q) - h(p,q)) + (cuts.card - 3) <= n - d`.

The proof composes three previously verified ingredients. Chordless support counting leaves at least `cuts.card-3` selected labels distinct from and nonadjacent to the current label; nonadjacency of the corresponding closed extreme row faces forces disjointness; those disjoint rows are strictly slack throughout the current portal-pair carrier; and the strict-row resource theorem subtracts them from the carrier's minimum-presentation excess.

A concrete corollary handles maximum support: if `cuts.card = n-d`, then every such actual portal-pair carrier has minimum-presentation excess at most 3. This places those local carriers in the already-verified small-excess routing regime once the current target-cone clipping output is upgraded to retain the same shortest/chordless mixed path.

This is a local recursive-resource theorem, not yet a global diameter bound. No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
