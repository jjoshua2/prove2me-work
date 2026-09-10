# Late Polynomial Hirsch research-status submission — 2026-09-10

The two newest circuit-localization / defect-completion research continuations were posted to the Polynomial Hirsch mission discussion as **research-only** material. They were not registered as theorem nodes and no `Proved` status is claimed.

- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`
- Discussion comment ID: `fe01bcfb-7ae4-4c03-aa9b-1ad4272341e9`
- Actions run: `34489508438`
- Receipt artifact: `10157130181`
- Artifact digest: `sha256:a1eb049d86828861fe053797d68b6e1e767800dd84786f4d7bea062665ed1618`
- Platform observed: Prove2Me `0.9.9`
- Tags: `strategy`, `reference`, `attempt`

The posting script performed a readback and confirmed resolved references to:

- `Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`), status `Open`;
- `Hirsch.simultaneous_clipping_diameter_of_compact_outer` (`75d26f37-e0bd-4d73-9128-688fe7d5a80c`), status `Proved`.

The posted research consists of:

1. `research/BalancedIsometricCircuitLocalization.md`: the ordinary localization inequality `2*h <= N-D+1` for vertex circuit pairs, the intrinsic rank-defect accounting `(f-h)+delta <= N-D`, exact circuit-noninheritance examples, and the balanced isometric installation diagnostic.
2. `research/OptimalCircuitDefectCompletion.md`: the ordinary claimed exact completion resource `e+delta`, the proper-face-containing completion construction, balanced minimum dimension, and the extra-unit obstruction when an external parallel realizing edge is required at maximum defect.

Both have exact computational receipts in `research/balanced_isometric_circuit_receipt.json` and `research/odc_verification_receipt.json`, respectively. Neither has a Lean proof or Prove2Me theorem verdict yet.

The one-shot push-triggered posting workflow was removed from its publication branch after successful readback. The formal mission tree remains unchanged: the open frontier is still `Hirsch.polynomial_edge_refinement_of_circuit_walks`.
