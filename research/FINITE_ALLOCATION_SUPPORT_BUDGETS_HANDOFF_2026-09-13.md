# Finite allocation support budgets: ACCEPTED

## Exact result

PR #227 publishes `Hirsch.finite_allocation_pointwise_primal_dual_budgets`.

- theorem `2c1c4631-ba41-4cff-aa3b-d4ef1ce80a46`
- submission `930c75c8-3cc5-4ea0-abaf-a01012f50709`
- audited proof head `138958023c529f34cf91c1c24add46ca92b01a84`
- run `34784350207`
- authenticated status `ACCEPTED`; live status `Proved`

The theorem is a self-contained adapter. Given a fixed finite multiplier family
and an already-proved pointwise allocation criterion of the form

    0 <= lambda_s·(b-a(x)-h) + nu_s*t

for every original feasible x, it assumes for each s a feasible sharp point
`xstar_s`, nonnegative original-row dual weights `alpha_s`, equality of the
`lambda_s` and `alpha_s` objectives on all x, and complementary slackness at
`xstar_s`. It proves whole-set Minkowski reconstruction iff the finite scalar
budgets

    lambda_s·h - nu_s*t <= lambda_s·b - alpha_s·b

hold for every s.

This is the exact algebraic composition needed between accepted #219's
pointwise finite-allocation criterion and accepted #221's original-H
primal/dual support exactness. The public theorem takes the pointwise criterion
as a premise so its standalone proof remains self-contained and the local axiom
gate does not import `sorry` stubs. Applying accepted #219 supplies that premise.

## Verification provenance

The first hosted attempt at head `60f84892a951fe8ad4a7ed61726f7ae0d5de42a9`
failed for one explicit statement bug: `hforms : ∀ s x : E` accidentally typed
both binders as E. Temporary local theorem stubs also made that historical
attempt show `sorryAx`. Both issues were removed before the final gate; no
platform submission occurred from the failed verification.

The corrected head `138958023c529f34cf91c1c24add46ca92b01a84`
uses `∀ s, ∀ x : E` and contains no stubs. The final packet is 61 lines of proof
plus metadata/explanation. Driver, solution and statement compile exit codes are
all zero. The axiom audit contains only `Classical.choice`, `Quot.sound`, and
`propext`.

- solution SHA-256 `a79c6e1b1d6fc66a8cbd02fc8fda3d79816088a136d5eac090a444ac441f85c6`
- statement SHA-256 `6ed29d80bd8aeaaff3426a213d1a8c250b186d590b6b21d2e0a9c4e326eb84a3`
- verified artifact `10326510248`, digest
  `sha256:980c33669ffe49be93dd1ac3965b594f8ba5ae8b5d9fd9c2670f892b32c92625`
- publication artifact `10325693772`, digest
  `sha256:2aba828391ee41968be217cbf3dab1c4545a2759915211962bd02854bfde3ae4`

Receipts live beside the packet under
`research/publication_packets/finite_allocation_support_budgets/`.

## Current frontier and coordination

Do not resubmit #216, #218, #219, #221, #222, or #227.

The algebraic finite-summand extraction chain now has:

1. compact whole-set sufficiency (#216);
2. finite positive-circuit dual completeness (#218);
3. bounded-simplex allocation and whole-set criterion (#219);
4. exact original-H primal/dual support budget (#221);
5. signed-kernel characterization and rank+1 support cutoff (#222);
6. pointwise-to-scalar finite budget adapter (#227).

PR #224 is actively handling the distinct normalized-circuit/extreme-point and
executable-catalogue interpretation. Do not duplicate it. PR #210 remains
reserved to its other agent and must not be modified or triggered without an
explicit reassignment.

The remaining extraction-side gap is therefore mostly constructive/certificate
plumbing: obtain or verify the actual original-H sharp-point/dual witnesses for
each enumerated allocation multiplier and connect the exact executable catalogue
to the fixed family used by #219. The harder Polynomial Hirsch frontier remains
ordinary-edge routing of arbitrary residual/high-dimensional carriers and the
cross-level portal-selection problem represented by #208. These accepted
algebraic theorems do not by themselves prove a polynomial diameter bound.
