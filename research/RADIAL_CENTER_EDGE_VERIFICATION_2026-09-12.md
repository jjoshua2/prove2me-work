# Radial center-edge no-cut-charge verification

Date: 2026-09-12.

Frozen theorem head: `b8a085744ea37784245bb490d5bec8a02f859702`.

Hosted verification:
- run `34691971558`
- job `103548715819`
- artifact `10297470849`
- artifact digest `sha256:f30cf348229edcd6ec86fb2269f90b86ad83c2802f4e2e59145e21367bcab1d5`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialRadialCenterEdge` and transitive-axiom-audited all three declarations with only `propext`, `Classical.choice`, and `Quot.sound`.

Verified declarations:
- `HirschRadial.retract_mem_center_segment`
- `HirschRadial.retract_center_segment_mem_clip_subsegment`
- `HirschRadial.retract_image_center_segment_subset_clip_subsegment`

Formal contribution: radial retraction of a point on a segment starting at the strict centre never leaves that same segment. If both segment endpoints lie in the convex outer region, its radial image lies in the clipped old-edge subsegment. Therefore a target-cone center/star edge can be covered entirely by its old-edge repair region and does not need a final cut-face label.

This localizes all nontrivial final-face costs in the rooted target-cone repair to the endpoint-lift spoke. It does not bound those spoke face costs and does not imply a global Polynomial Hirsch bound.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
