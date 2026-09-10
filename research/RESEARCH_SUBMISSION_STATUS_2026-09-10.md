# Polynomial Hirsch research submission status — 2026-09-10

This is the durable index for the research-continuation submission performed after the 2026-09-10 theorem-publication sweep.

The guiding rule was strict: kernel-verified theorem-level results belong on Prove2Me as theorem/proof submissions; ordinary mathematical proofs and exact computational certificates without Lean verification belong in the Polynomial Hirsch mission discussion with an explicit evidence boundary. No result below is relabeled `Proved` unless it already has an actual platform verdict.

## Mission

- Mission: **The Polynomial Hirsch Conjecture**
- Mission ID: `6078cb2d-3594-44b1-a01a-fd452ddae274`
- Platform observed during submission: Prove2Me `0.9.8`

## Research-status comment 1 — newer continuation

- Comment ID: `13a736dd-c71c-4121-8ec8-78f25be23dfb`
- Actions run: `34433853507`
- Receipt/audit artifact: `10135458660`
- Tags: `strategy`, `reference`, `attempt`

Submitted research:

1. `QuasipolynomialRankRepairCost.md` — quasipolynomial equality-rank box-section repair cost.
2. `LinkingRankEdgeDirectionCost.md` — polynomial section-edge direction catalogue under fixed genuine linking rank.
3. `GrowingRankCircuitStructure.md` — explicit polynomial weighted-wheel circuit catalogue with growing equality rank.
4. `SingleStepUniversality.md` — remote-edge installation / one-maximal-circuit-step universality, showing the one-step restriction is not a genuinely easier Open child.

All four have ordinary mathematical arguments plus executed exact-rational evidence, but no Lean proof/axiom audit/Prove2Me `ACCEPTED` verdict. Accordingly they were submitted as research status, not theorem nodes.

The detailed local handoff for these four is `research/RESEARCH_UPDATE_2026-09-10.md`.

## Research-status comment 2 — earlier Library-only continuation

- Comment ID: `1c2ae99b-9e68-45b5-bb24-fb57596deb78`
- Actions run: `34434089929`
- Receipt/audit artifact: `10135540092`
- Tags: `strategy`, `reference`, `attempt`

Submitted research:

5. `SimultaneousClippingFullDiameter.md` — ordinary all-final-vertex compact-parent simultaneous clipping bound `D + sum_i B_i`; the end-to-end candidate modules in that packet were compiler-unverified and therefore were not claimed Proved.
6. `UnboundedClippingOneRay.md` — ordinary pointed-unbounded `D + 1 + sum_i B_i` extension, with sharp universal `+1`; its reusable explicit exterior-cap witness is separately platform-Proved as `Hirsch.simultaneous_clip_diameter_of_exterior_cap` (`2e20b0a7-503c-4be4-bd9c-446b88f77c8e`), while the universal cap-existence / pointed-H-polyhedron assembly remains ordinary mathematics.
7. `BalancedCommonFaceCostBarrier.md` — exact infinite-family cost barrier against automatic balanced-child/common-face charging; this is a falsification harness, not a Lean theorem or a Polynomial Hirsch counterexample.
8. `RankControlledBoxRepairCost.md` — elementary rank-controlled box-section precursor, later quantitatively strengthened by the quasipolynomial `G`-bound above.

These were also submitted only as research status where not already represented by a genuine Prove2Me theorem.

## Research-status comment 3 — PR-only cone-carrier result

- Comment ID: `cb4b2523-09a9-4081-952e-f774cc67d9b9`
- Actions run: `34434299402`
- Receipt/audit artifact: `10135608727`
- Tags: `strategy`, `reference`, `attempt`

Submitted research:

9. `research/ConeCarrierDescent.md` on draft PR #53 (`chatgpt/verify-simultaneous-clipping`) — for apex-preserving clipping of a pointed cone by `m` new cuts of rank `r`, an ordinary nested-carrier construction gives

`diam(P) <= 2 E(m,r) <= 2 sum_{j=1}^r binom(m,j) <= 2((m+1)^r-1)`

with the sharper ray/polygon base cases recorded in the note. Exact regression coverage is 40 apex-preserving rational instances, 695 vertices, 8,813 unordered pairs, 484 carriers, 655 independent-basis certificates, plus five apex-removal falsifiers; two complete runs reproduce SHA-256 `8ea13789aa3f0763d28ec5814b6b93ca241ba7a2dab569a97389413d8aab5514`.

The note itself explicitly states that the universal theorem is not Lean-formalized. It was therefore posted as a non-cyclic sufficient research certificate, not registered as Proved.

## Formal Prove2Me state after every research post

Each of the three posting workflows immediately reran the authenticated strict publication audit. Every audit passed with the same state:

- **41** expected theorem publications at `Proved`;
- **1** expected theorem at `Open`;
- stable public definitions still at `Definition`;
- **zero audit failures**.

The one genuine Open frontier remains:

`Hirsch.polynomial_edge_refinement_of_circuit_walks`

- theorem ID: `099c6686-560c-48fc-b2c2-18b6a620a06e`
- live status: **Open**

No SC1/EC1 one-step reformulation was created as a child, because the single-step universality reduction shows that such a restriction retains the original quantitative difficulty rather than reducing it.

## Publication hygiene

The mission-posting jobs used temporary push-triggered `ubuntu-slim` workflows only to perform the authenticated writes and immediate read-only audits. Those one-shot workflow files were removed after successful submission. The permanent manual publication audit on `main` remains `.github/workflows/audit-prove2me-publications.yml`.

This file is the compact status index; detailed theorem-publication receipts remain in `research/PUBLICATION_UPDATE_2026-09-10.md`, and the detailed newer research handoff remains in `research/RESEARCH_UPDATE_2026-09-10.md`.
