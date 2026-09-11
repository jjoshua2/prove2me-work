# Excess-two common-carrier publication staging

The compact publication driver has passed the pinned Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f` gate at source commit `d85e9ff15194bd413c5f7e71e6f1f10e2b98697c`. Both audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The first Prove2Me proof submission was rejected only because its wrapper declared `Hirsch.solution` inside `namespace Hirsch`; the server expects a root-level declaration named exactly `solution`. The corrected retry changes only that wrapper shape, reuses the existing theorem `ca4c980f-86d7-4810-be9e-30e473b9dd70`, and resubmits no theorem registration.
