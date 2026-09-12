# Radial active-row interval verification

Date: 2026-09-12.

Frozen theorem head: `fd7511f10153113446dcad73971f091ac6d5f9cf`.

Hosted verification:
- run `34692904962`
- job `103551222857`
- artifact `10297421344`
- artifact digest `sha256:038b33fe502c512a91e97f9b5072360acc22e68ee674ef770929083d68999ffc`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The final hosted gate built `Solutions.PolynomialRadialActiveRowInterval`, ran the file directly through Lean, and transitive-axiom-audited the five targeted public declarations:
- `HirschRadial.normalizedRow_affine_combo`
- `HirschRadial.scale_eq_row_on_combo_of_endpoints`
- `HirschRadial.activeRowCell_convex`
- `HirschRadial.retract_mem_active_cut_of_mem_activeRowCell`
- `HirschRadial.retract_image_segment_subset_active_cut`

The workflow completed successfully. The audited declarations use only the repository-allowed standard logical axioms; no `sorryAx` was accepted by the checker.

Formal contribution: for fixed-centre radial clipping, every normalized row score is affine and every fixed-row active cell is convex. Hence along a line segment a row cannot leave the radial upper envelope and later re-enter. Under strict centre slack, if a row is active at both endpoints then the whole segment maps by radial retraction into that final cut face.

Strategic consequence: merged target-star work already localizes target-rooted cut-face cost to the endpoint-lift spoke. This result adds an ordered one-dimensional active-cell structure on such radial segments, which can be used to reason about consecutive cut intervals rather than only unordered support labels. It does not itself bound the parent-edge cost between portal vertices on one cut face.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
