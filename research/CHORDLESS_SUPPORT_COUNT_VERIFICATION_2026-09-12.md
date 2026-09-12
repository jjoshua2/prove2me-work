# Chordless support count verification

Date: 2026-09-12.

Frozen theorem head: `d42a8e828666b782d8467158642ca56bd3457d45`.

Hosted verification:
- run `34698938562`
- job `103567164887`
- artifact `10299562186`
- artifact digest `sha256:ab36b879c73e88564dd247bbbe845f4c86e49c88560b45af2359ac43fad24d34`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The successful final gate built `Solutions.PolynomialChordlessSupportCount`, ran the source file directly through Lean, and transitive-axiom-audited:
- `HirschRegionRoute.chordless_support_neighbor_eq_prev_or_next`
- `HirschRegionRoute.supportNeighborFinset_card_le_two`
- `HirschRegionRoute.mem_nonneighborSelectedFinset`
- `HirschRegionRoute.nonneighborSelectedFinset_card_ge_sub_three`

All four reports contain only `propext`, `Classical.choice`, and `Quot.sound`; the strict checker reports: `Axiom audit passed: 4 required declarations; 4 reports checked; only standard logical axioms.`

## Formal contribution

On a chordless used-region path, any graph-neighbor of a fixed support label is its immediate predecessor or immediate successor, so the current label has at most two neighbors inside the whole path support.

For any selected finite subset `cuts` of path-support labels containing the current label, `nonneighborSelectedFinset` removes the current label and all selected support-neighbors. Every surviving label is selected, distinct from the current label, and graph-nonadjacent to it, and

`cuts.card - 3 <= nonneighborSelectedFinset.card`.

Strategic role: when `cuts` is the final-cut support of a shortest mixed clipping path, merged PR #189 turns each surviving nonneighbor into a disjoint row face and hence a row strictly slack throughout the current portal-pair carrier. Merged PR #186 then converts at least `r-3` such rows into local minimum-presentation excess savings, yielding the target shape `localExcess + (r-3) <= n-d`.

This is graph/support accounting only, not yet the polyhedral composition theorem. No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
