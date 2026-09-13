# Accepted evidence — finite allocation pointwise primal-dual budgets

Prove2Me accepted `Hirsch.finite_allocation_pointwise_primal_dual_budgets`.

- Theorem ID: `2c1c4631-ba41-4cff-aa3b-d4ef1ce80a46`
- Submission ID: `930c75c8-3cc5-4ea0-abaf-a01012f50709`
- Final Actions run: `34784350207`
- Frozen audited proof head: `138958023c529f34cf91c1c24add46ca92b01a84`
- Authenticated publisher result: `ACCEPTED`, live status `Proved`
- Registration mode: `PUBLISHED`
- Solution SHA-256: `a79c6e1b1d6fc66a8cbd02fc8fda3d79816088a136d5eac090a444ac441f85c6`
- Statement SHA-256: `6ed29d80bd8aeaaff3426a213d1a8c250b186d590b6b21d2e0a9c4e326eb84a3`
- Driver / solution / statement compile exit codes: all `0`
- Axiom audit: only `Classical.choice`, `Quot.sound`, and `propext`
- Verified packet artifact: `10326510248`, archive digest `sha256:980c33669ffe49be93dd1ac3965b594f8ba5ae8b5d9fd9c2670f892b32c92625`
- Publication-receipt artifact: `10325693772`, archive digest `sha256:2aba828391ee41968be217cbf3dab1c4545a2759915211962bd02854bfde3ae4`

The first hosted attempt was intentionally not promoted: it exposed the exact binder typo `∀ s x : E` and temporary local platform stubs introduced `sorryAx`. The corrected packet changed the binder to `∀ s, ∀ x : E`, removed those stubs, and became a self-contained 61-line Mathlib proof. The final frozen packet then compiled and audited cleanly before the trusted publisher submitted it.

The theorem assumes an already-established pointwise finite-allocation criterion and supplied original-H primal/dual support witnesses. It proves that the universal feasible-point tests are equivalent to one explicit scalar budget per fixed multiplier. It does not construct the multiplier catalogue, construct or certify the support witnesses, discover a summand, route a residual polyhedron, or prove Polynomial Hirsch.
