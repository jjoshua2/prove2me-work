# Publication-only staging: high-excess independent-row-block routing

The theorem source is frozen to PR #132 commit `4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b` and has separately passed the hosted current-main verification recorded in `research/HIGH_EXCESS_ROW_BLOCK_HOSTED_VERIFICATION_2026-09-11.md`.

This staging branch contains only publication machinery/trigger material. The owner-only base workflow reconstructs the frozen row-block proof, compiles and axiom-audits a dependency-free driver with the small-excess theorem as an explicit premise, then checks the exact Prove2Me theorem ID/type/status for `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` before verifying the unconditional public theorem.

Two publication-infrastructure failures are recorded fail-closed:

1. Run `34643820723` failed before authentication because the generated driver imported `Definitions.Def_Hirsch_model` before its local `.olean` had been built.
2. Run `34644132950` successfully compiled/audited the dependency-free driver and passed authenticated preflight. It registered theorem `27737675-3725-4a3d-92d7-92a87e91031e`, but submission `14382e80-77be-4026-85af-41b3ada2e0fe` received WA with exactly `Unknown identifier solution`. The uploaded packet had mistakenly defined `Hirsch.solution` rather than Prove2Me's required root-level declaration `solution`.

The new wrapper changes only that distinguished declaration's namespace. The frozen row-block theorem, driver bytes, mathematical proof, target theorem statement, and checked Prove2Me dependency are unchanged. The already-registered theorem is reused for the retry.

No claim of Prove2Me acceptance is made until an authenticated workflow returns ACCEPTED and live Proved. The d>=4 circuit-to-edge frontier must remain Open before and after the transaction. Do not merge this publication branch; preserve the receipt on main, remove the one-shot workflow, then close the staging PR unmerged.
