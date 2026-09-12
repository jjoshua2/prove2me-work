# Simultaneous clipping used-cut projection — verification receipt

Date: 2026-09-12. Repository: `jjoshua2/prove2me-work`.

## Verified source

The corrected used-cut projection on branch `formal/simultaneous-clip-used-labels` passed Actions run `34691284576`, job `103546862924`, under Lean 4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

The first attempt exposed two local source errors only: a malformed `filterMap` case split for old-edge labels and a missing `HirschRegionRoute` namespace opening. Those were repaired without changing the theorem statement or clipping geometry. The replacement build completed successfully.

Audited declarations:

- `HirschRadial.clipUsedCutLabels_nodup` — `propext`, `Quot.sound`;
- `HirschRadial.clipUsedOldLabels_nodup` — `propext`, `Quot.sound`;
- `HirschRadial.clipUsedRegionCost_sum_eq_cut_old` — `propext`;
- `HirschRadial.clipUsedOldLabels_length_le` — `propext`, `Classical.choice`, `Quot.sound`;
- `HirschRadial.route_clip_of_lifted_endpoints_with_parent_routes_used_cuts` — `propext`, `Classical.choice`, `Quot.sound`.

No `sorryAx` or nonstandard axiom remains.

## Formal result

Given a specified outer parent edge/stay route of padded length `D`, the simultaneous-clipping repair now returns a `Nodup` list `cuts` containing only final cut-face labels actually used by the simple repair-region route, together with a genuine final-polytope edge/stay route of padded length

```text
D + (cuts.map B).sum.
```

The proof starts from the verified simple combined-region label list. Cut labels are projected with `filterMap`. Old parent-edge labels are also projected and remain `Nodup`, so there can be at most `D` of them because they lie in `Fin D`. Endpoint singleton regions cost zero. Exact combined-region cost therefore decomposes as used-cut cost plus the number of used old edges, which is then padded by `D`.

This strictly refines the previous all-cut sum for an individual repair route. It does not assert that the selected cut-face budgets are themselves polynomial or that used-cut sets globally de-duplicate across different outer models/steps.

No Prove2Me mutation or credential use occurred in this verification.
