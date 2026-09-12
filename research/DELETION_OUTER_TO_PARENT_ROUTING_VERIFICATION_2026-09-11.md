# Deletion-outer graph budget to parent routing verification

Date: 2026-09-11.

Frozen theorem source commit: `9ceb9245b8b5128d554d35f3fb06c3313d60d70e`.

Hosted verification:
- run `34672886527`
- job `103497483351`
- artifact `10291227341`
- digest `sha256:64cfec47283acff1f311c9d2ea4bd5e9dec60dfb0aa58d94289a4514b7c7e7c1`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The focused gate compiled `Solutions.PolynomialDeletionOuterToParentRouting` and axiom-audited both public declarations with only the repository-allowed logical axioms `propext`, `Classical.choice`, and `Quot.sound`:

- `HirschDeletionRouting.hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route`
- `HirschDeletionRouting.hpoly_diamLE_of_deletionOuter_diam_and_parent_face_route_of_strictRows`

Formal meaning: for a bounded parent, an explicit graph budget `D` on the potentially unbounded one-row deletion outer and an ambient parent-edge route budget `B` on the deleted-row face imply parent `DiamLE (D + 1 + B)`. The explicit cap is only a compact proof device; the theorem does not assume the deletion outer is bounded.

No polynomial bound for `D` or `B` is asserted. In particular a naive recursive use of both children yields a Pascal-type recurrence and does not establish a fixed-degree Polynomial Hirsch bound.
