# Target-cone pair-specific portal-cost verification

Date: 2026-09-12.

Frozen theorem head: `141f0582f39b771ea0778d3eb506c260dca33833`.

Hosted verification:
- run `34692359547`
- job `103549756491`
- artifact `10298110776`
- artifact digest `sha256:a328d9091756a67eabd68c5c311eff186bb407de3b4c34c87f2a4596b13ef1c6`
- Lean 4.30.0 / Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`

The one-shot hosted gate built `Solutions.PolynomialTargetConePairPortalCosts` and transitive-axiom-audited
`HirschTargetDeletion.target_slack_batch_reinsertion_with_pair_specific_portal_costs`.
The report contains only `propext`, `Classical.choice`, and `Quot.sound`.

Formal contribution: fix a parent target vertex `v` and let `J` be exactly the rows strictly slack at `v`. Every pairwise target-cone repair now returns a duplicate-free list of at most `n-d` actual target-slack `RegionLeg`s, each carrying a parent extreme entry/exit pair tight on its row, with route cost

`2 + sum B(row, entry, exit)`.

Every target-rooted repair has the analogous exact form with cost

`1 + sum B(row, entry, exit)`.

Thus the target-cone interface no longer needs whole-face diameter budgets: the remaining recursive obstruction is exactly the weighted sum of costs assigned to the concrete portal pairs actually used. No decreasing resource for those pair costs, and hence no fixed-degree Polynomial Hirsch recurrence, is claimed here.

No Prove2Me credentials or mutation were used. The one-shot verifier is removed before integration.
