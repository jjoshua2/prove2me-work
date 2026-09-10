# Verified carrier-to-edge integration — 2026-09-10

This integration imports only the previously kernel-verified carrier geometry, not the uncompiled later rank/defect/checkpoint candidates.

## Exact source and verification

- Source commit: `71efbbcb66528871c0ff0508fe6b31b6c1b7b646`.
- Imported file: `Solutions/PolynomialCircuitCarrierEdge.lean`.
- Git blob: `b8514742e99630b5ada7ceacb77ddefda7e1e695` (copied without alteration).
- Successful Actions run: `34533747844`; job `103060393789`.
- Artifact: `10174595952`; archive SHA-256 `8d1d768f4db018fc8d6e178dd3d43992c6ea0341183e9613a5a909028bd966e4`.
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
- Three required declarations and six axiom reports; only `propext`, `Classical.choice`, and `Quot.sound`.

The artifact was downloaded again and the archive digest, successful-build marker, required declarations, and axiom whitelist were independently rechecked in this continuation. The saved build log is in `research/verification/carrier_edge_34533747844.log`.

GitHub comparison of integration base `be4a78fb75b2d2c1c17f513811202106a4088ceb` with the verified source commit reports exactly two added files: this Lean module and the historical experiment workflow. No imported source or pin changed. The workflow is deliberately NOT imported. Thus this integrates the exact previously compiled source closure; it is not a claim of a new compilation in this session.

## Mathematical scope

The module proves:

1. `HirschPolynomialAccess.rowCircuitStep_adj_of_commonFace_line`.
2. `HirschPolynomialAccess.commonFace_line_of_dim_le_one`.
3. `HirschPolynomialAccess.rowCircuitStep_adj_of_commonFaceDim_le_one`.

A maximal row-circuit augmentation leaving a vertex is an ordinary graph edge if its common-tight-row face lies on the augmentation line. The last theorem derives this line condition from common-face dimension at most one. It does not assume the target is a vertex: the geometric conclusion establishes an actual extreme segment.

This is a sufficient local criterion, not a proof that all circuit steps have one-dimensional carriers and not a solution of Polynomial Hirsch. The sole formal Open frontier stays `Hirsch.polynomial_edge_refinement_of_circuit_walks` (`099c6686-560c-48fc-b2c2-18b6a620a06e`).

## Pending work is separate

The current research branch already contains a newer rank fix and active-defect identities. The earlier chat checkpoint packet must NOT overwrite those files or redeclare the same identity. Its nonvertex localization and carrier-budget routing extension need a reconciled draft and a successful local Lean gate before promotion. No Prove2Me acceptance is claimed for the three imported declarations.

Rebuild locally with `lake build Solutions.PolynomialCircuitCarrierEdge`. Existing server-accepted checkpoint and localization theorems need no duplicate publication.
