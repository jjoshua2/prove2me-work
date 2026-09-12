# Deferred local routing costs: accepted publication

[Hirsch.shortest_region_path_with_deferred_pair_costs](https://prove2.me/theorems/ba2632b3-1bec-43f9-8755-960e4b04936c) is **Proved**. Submission `59a4c70a-7584-4f2e-a429-23598e316dd8` is **ACCEPTED**.

The theorem selects a shortest, chordless region path and its actual portal pairs before the routing graph and costs are supplied. Only those selected pairs need local routes. The resulting route costs at most their sum. This permits a later proof to use geometric facts about the chosen support when discharging local routing obligations.

The previous shortest-clipping statement is valid, but its universal `hFaces` premise prevents that particular use without a stronger interface. The new theorem provides the generic assembly primitive. Specializing it to simultaneous clipping and summing the maximum-support carrier costs remain next work; this publication does not close Polynomial Hirsch.

- Frozen source: [6db6759777606ad5c5243b716a4fe1ea59c80c8d](https://github.com/jjoshua2/prove2me-work/blob/6db6759777606ad5c5243b716a4fe1ea59c80c8d/Solutions/PolynomialDeferredRegionCostsPublic.lean).
- Standalone proof SHA-256: `6a18e70d18defed5c6fd3f265ceba127f28f10e501170ddfa83c90aad373c2e5`.
- Lean 4.30.0 / Mathlib c5ea003.
- Local source and exact standalone compilation passed, with only `propext`, `Classical.choice`, and `Quot.sound` in both axiom audits.
- No existing equivalent was found in the scoped Hirsch catalog or the additional shortest-region/deferred/pair-cost searches.
- The root remains Open with `common_face_diameter_of_dim_ge_six` as its sole open leaf.

The [publication packet](publication_packets/deferred_region_costs/) contains the exact formal statement, natural-language description, standalone proof, explanation, axiom logs, hash audit, registration response, accepted verdict and authenticated live readback.
