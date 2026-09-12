# Simultaneous clipping with deferred selected cut-pair costs

Date: 2026-09-12.

Frozen theorem head: `7b75e7ca3c300177236b3b8e897906ad74f690c6`.

Hosted verification:
- run `34705587725`
- job `103584922735`
- artifact `10301269745`
- artifact digest `sha256:5925e9c915080f2a6320b46e1564cc49c7ca0484fcee59b7dfde53fba9058aab`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialSimultaneousClipDeferredPairLegs` and transitive-axiom-audited both public declarations. Their reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschRadial.route_clip_of_lifted_endpoints_with_shortest_deferred_cut_legs`
- `HirschRadial.route_clip_with_shortest_deferred_cut_legs`

Formal contribution: the radial repair geometry now selects the outer route, mixed cut/old-edge/singleton cover, metric-shortest/chordless mixed region path, concrete parent-vertex portal pairs, and projected actual cut legs **before** any local final-cut route-cost function is introduced. A subsequent callback needs ordinary parent-edge routes only for those selected cut legs. Old-edge legs are discharged internally at cost one, endpoint singleton legs at zero, and the final padded route has exact upper budget

`D + sum(B(actual selected cut portal pairs))`.

This closes the generic simultaneous-clipping quantifier-order gap identified in the current Polynomial Hirsch handoff. It deliberately does not instantiate the selected cut-pair routes. The next maximum-support composition can combine the same returned chordless path with the verified support/excess theorem (#193) and exact small-carrier routing (#114).

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
