# Target-cone used-face support verification

Date: 2026-09-12.

Frozen theorem head: `321e2e0d94a16b0f8e0d11ff856b3828d0b438b0`.

Hosted verification:
- run `34690775528`
- job `103545490134`
- artifact `10296348830`
- artifact digest `sha256:71ae66013b80cdb4ba895a09f4e19a56a5c94658cec18a257bc39513ee331f62`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The ready-for-review one-shot gate built `Solutions.PolynomialTargetConeUsedFaceSupport` and transitive-axiom-audited
`HirschTargetDeletion.target_slack_batch_reinsertion_with_used_parent_faces`.
Its transitive axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

Formal contribution: for a fixed parent target vertex `v`, let `J` be exactly the rows strictly slack at `v`. The target-tight rows define the verified compact star outer. Simultaneously restoring the rows in `J` now has a path-sensitive support form:

- every pair of parent vertices has a repaired route of cost
  `2 + sum_{i in cuts} B_i`;
- `v` has a repaired route to every parent vertex of cost
  `1 + sum_{i in cuts} B_i`;
- in each conclusion `cuts : List J` is `Nodup` and `cuts.length ≤ n-d`.

Thus one repaired route invokes at most `n-d` distinct target-slack face budgets and never pays for unused target-slack faces. The theorem does not bound the weighted sum of those face budgets; in particular, substituting a uniform same-excess recursive diameter bound still gives the known multiplicative obstruction and is not a fixed-degree Polynomial Hirsch proof.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
