# First gate: internal face-local construction clean; public wrapper failed

This is FAILURE evidence, not an acceptance receipt. PR #332 remains open/draft.
Target: Hirsch.face_local_ordered_target_routes.
Tested proof2758b9d7b9ad8a393a270b9c2c93b356ecae772f, source
 e044971a320c27c5b899a961063ae99a2b4cdc6c (1297 lines/55795 bytes).
No submitted source or metadata changed after this gate.

Actual publication request5778888834 and acknowledgement5778891809 resolve
run35744801081 to that exact proof. Gate106803499029 passed. The secret-free
verifier106803568293 failed driver compilation with ONE reported error at
1265:78 in the public wrapper's local hl conversion of a finite vertex-value set.
The remaining goal prints the same Finset.image expression on both sides.
Two unused-simp warnings at1136 are harmless; no linter was disabled.

Seven named helper reports contain only propext, Classical.choice and Quot.sound,
including acquire_on_face, route_for_flag and the full internal optimal_flag_routes.
The public solution report contains failed-elaboration sorryAx. No admission was
written, but the COMPLETE packet is NOT verified. Standalone solution/statement
stages were not reached; publish106804105425 and report-verify106804105917 skipped.
There is no theorem/submission ID, registration, submission, ACCEPTED or Proved.

The proposed single-site repair uses extensional membership simplification in hl.
It is UNAPPLIED to this packet and UNCOMPILED. Exact patch and proposal hashes:
research/verification/face-local-target-flags/first-attempt/proposed-local-repair.patch
and repair-proposal.json. Proposed full source1298 lines/55847 bytes, blob
7cea8154a7fb8647105e4420b8fef167fac324c5, SHA256
0ff21754450c5ab02cf83504d00a3a5832bf88fa7ba06d14413c06a2de316690.
Apply/reverse checks pass without changing the target, any helper or metadata.
That does not establish compilation; further errors can appear. No second trigger.

The new mathematical chain constructs full original-edge phases on shrinking
planned target faces and minimizes the ordered conditional row-level sum, with
same-route K*min(d,m-d) under the local-charge antecedent. It derives the flag and
all phase geometry from exact finite H/hull equality and actual extreme endpoints.
The optimal sum is not proved uniformly polynomial; no full Polynomial Hirsch or
shortestness claim is made. Full scope remains in the unchanged explanation.md.

Executed18-model tests retain650 routes/733 original edges,7 nonshortest routes,
36 multiedge phases,18 nonacquiring steps,184 improvements over the optimal global
budget and30238 checked eligible orders. Nine malformed small controls fail.
Five known triangular cases through64D check124 more edges and4 controls. Their
family interpretation is written/exact, not another Lean instance or #282's work.
Clean four-script replay reproduces all five full outputs. Python/JSON remain
unverified; full outputs are exported/regenerate and summaries are labelled derived.

Only request artifact10701287910 exists,307 bytes, rehashed SHA256
b6c7b873285f5cba5e745482b6282a684d139dc1177e30c0e3d1a385c5fb93dd.
Preserved: its exact request, tested inputs, full displayed error context/all8
reports, selected runner lines, source/replay records and proposed patch. The
complete decoded verifier log was read through cleanup; the extracted diagnostics
are not a complete raw runner archive. No absent artifact or receipt is invented.

Handoff: research/FACE_LOCAL_TARGET_FLAGS_HANDOFF.md. Keep this same PR draft until
a future complete gate passes. Lean4.30.0/Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f,
strict0.10.8, accepted inputs, #326/#282/#210 and publication safeguards unchanged.
