# ACCEPTED: additive simultaneous affine-envelope exposed-edge budget

- Theorem: `Hirsch.affine_envelope_exposed_edge_budget`
- Theorem ID: `98b9fed3-829a-49fe-b099-e46f0f2b08a8`
- Submission ID: `19eef3a9-597b-492d-a108-e2c999e1676b`
- Authenticated verdict: ACCEPTED; publisher live theorem readback: Proved.
- Frozen accepted proof head: `5be362ef7a907fa0bfc4edd8f13d8fbd8233e18e`
- Final run: `34794299415`; workflow-main head: `1ba75aba77a4c696b78eb31679fd163b391cd5d5`.
- Actual top-level trigger: https://github.com/jjoshua2/prove2me-work/pull/239#issuecomment-5657566909
- Resolved-run acknowledgement: issuecomment-5657567997.
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/239#issuecomment-5657610493
- Solution Git blob: `c6ea054c19c061539eba3f19427fd9ec6ef17336`.
- Solution SHA-256: `ab44f8be93f9918aba2516f88c185cd89dc670512b773a176f169501ee689650`.
- Driver / solution / target-statement compile exits: all zero.
- Three audited declarations: only propext, Classical.choice and Quot.sound.
- Verified artifact10329530572, ZIP SHA256 `aad296734b6b4f912718bd350cf90f0233d0f5aa4dd3517f17e0204a50fb55df`.
- Publication artifact10328792773, ZIP SHA256 `de0f057b477ea75227b3d806325fa8c45be9a1263599a5655c6ff3310786fd08`.

Both archives were downloaded and their hashes recomputed. All five frozen packet file hashes match; solution, problem and explanation match the local final packet. Raw manifest, audit, compile logs and publication-receipt.json are preserved beside this note; full frozen driver/statement and original archives accompany the conversation bundle. The publisher log was read and confirms the authenticated ACCEPTED report. Gate, verify and publish succeeded; report-verify was skipped. This is the publisher's recorded live readback, not a second direct platform API poll by this chat.

The first prepared run34794086601 failed at one same-pick reflexivity goal after `simp only [rank, hi]`. The explicit `exact le_rfl` repair changed one line only, preserving the statement and every mathematical assumption. The failed driver and generated sorryAx were not acceptance evidence; that run never registered or submitted a theorem. The corrected packet was submitted to Prove2Me once. Failed diagnostics remain under research/verification/simultaneous_lift/.

The accepted theorem proves the FINITE affine-envelope/exposed-edge certificate and its SUM of factor-state budgets. The full normal-fan existence and geometric L+(L+1)sum_i(v_i-1) lift theorem are proved in the mathematical note, not silently claimed as the public Lean theorem. The Python constructor/checker is not Lean-extracted. Deza–Pournin's classical fibre/edge-surjectivity arguments are credited; no historical novelty claim. No arbitrary-carrier diameter bound is asserted. Do not resubmit this accepted packet.
