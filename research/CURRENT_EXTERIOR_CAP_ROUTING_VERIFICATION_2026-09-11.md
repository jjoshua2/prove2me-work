# Current exterior-cap routing — hosted verification receipt

Date: 2026-09-11

Frozen proof source commit `b196d8927ef4c442435f3081ad42947ac23d8c46` passed the focused hosted gate under Lean 4.30.0 and Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

- PR: #150
- Actions run: `34657118412`
- job: `103451829683`
- conclusion: **success**
- artifact: `10286247560`, `current-exterior-cap-routing-verification`
- artifact digest: `sha256:fa7432d724a56c1016ea084b3db9d63786925ea559b98e9c64c5900f09498d3e`

`Solutions/PolynomialCurrentExteriorCapRouting.lean` built successfully. The focused gate axiom-audited:

- `HirschExteriorCurrent.augmented_route_bound_of_cap_classification`
- `HirschExteriorCurrent.diamLE_single_clip_of_augmented_outer_routes`
- `HirschExteriorCurrent.diamLE_single_clip_of_old_routes_and_cap_classification`

All complete axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The checker reported:

`Axiom audit passed: 3 required declarations; 5 reports checked; only standard logical axioms.`

## Result

The current-main radial/face-cover stack now has an end-to-end exterior-cap interface with no historical ancestry:

1. if old outer vertices have graph-route budget `D` and every new compact-outer vertex is a cap vertex adjacent to an old one, all compact-outer vertices admit an augmented route of length `D+1`;
2. augmented routes may use genuine outer edges or explicit non-edge cap chords;
3. if every cap chord retracts into the one final exposed cut face of budget `B`, radial repair produces a genuine final-parent vertex/edge route of length `D+1+B`.

The cap chord is never misidentified as an edge. Endpoint attachment spokes and all cap shortcuts share one final face budget.

## Boundary

This closes the exterior-cap **geometry and route assembly**, not the remaining cost theorem. The numerical inputs remain explicit:

- `D`: graph cost among the old vertices of the uncapped one-row deletion outer;
- `B`: graph budget for the final deleted-row blocker facet.

PR #149 supplies a same-excess/lower-dimension mechanism for repeated blocker-facet reentries, but does not automatically provide `B` for an arbitrary pair. The one-row deletion outer may be unbounded, so the bounded-only lower-excess diameter hypothesis does not automatically provide `D`.

No Prove2Me registration or submission occurred in this verification run.
