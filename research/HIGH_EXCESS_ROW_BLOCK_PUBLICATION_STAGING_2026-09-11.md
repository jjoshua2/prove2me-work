# Publication-only staging: high-excess independent-row-block routing

The theorem source is frozen to PR #132 commit `4924c6ea81cda80c6a8bd54ce2a0d3d784525b3b` and has separately passed the hosted current-main verification recorded in `research/HIGH_EXCESS_ROW_BLOCK_HOSTED_VERIFICATION_2026-09-11.md`.

This staging branch contains only publication machinery/trigger material. The owner-only base workflow reconstructs the frozen row-block proof, compiles and axiom-audits a dependency-free driver with the small-excess theorem as an explicit premise, then checks the exact Prove2Me theorem ID/type/status for `Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three` before registering/verifying the unconditional public theorem.

No claim of Prove2Me acceptance is made until the authenticated workflow returns ACCEPTED and live Proved. The d>=4 circuit-to-edge frontier must remain Open before and after the transaction. Do not merge this publication branch; preserve the receipt on main, remove the one-shot workflow, then close the staging PR unmerged.
