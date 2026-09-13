# ACCEPTED: finite positive-circuit dual tests

The direct 242-line proof is unchanged from proof head
`ad4345bb17066c91b13d09ab0c8e757cbc5b65c9`. It compiled on the first prepared
hosted gate and passed the transitive axiom audit. The trusted publisher then
returned ACCEPTED and recorded authenticated live status Proved. No new
submission or verification run is required for this unchanged proof packet.

Theorem: `Hirsch.finite_positive_circuit_dual_tests`
Theorem ID: `8f3c4cc7-be73-4ecf-9e17-816c710e20d7`
Submission ID: `3fd7936c-8271-4a24-b342-d60bfd29529f`
Run: https://github.com/jjoshua2/prove2me-work/actions/runs/34778403314
Trigger: https://github.com/jjoshua2/prove2me-work/pull/218#issuecomment-5655628372
Acknowledgement: https://github.com/jjoshua2/prove2me-work/pull/218#issuecomment-5655629283
Verdict: https://github.com/jjoshua2/prove2me-work/pull/218#issuecomment-5655650520

The trigger was a NEW top-level PR conversation comment, read back after
posting. No workflow_dispatch was used. The immutable resolved request agrees
with this proof SHA; the workflow/trusted publisher SHA is the different main
commit `a7db9296e6645e92048f37089f0645f8a292f27c`.

Jobs: gate 103780774675; verify 103780797930; publish 103781069317.
The separate module-only report-verify job was correctly skipped for publication.
All three packet compiler exit codes are 0. All four printed declarations use
only Classical.choice, Quot.sound and propext. The solution has only a
push_neg deprecation warning and an unnecessarySimpa warning. The statement
file's intended target placeholder is not imported as the proof and does not
occur in the proof's transitive axioms.

## Preserved bytes and independently checked digests

The files under receipts/ are exact downloaded request/audit/manifest/compiler
log files, not reconstructed platform responses. publication-receipt.json is
the exact trusted publisher artifact. download-integrity.json is explicitly a
local cross-check summary, not a raw authenticated API response. Every frozen
manifest hash matched, and the downloaded solution, problem and explanation
matched the prepared bytes exactly.

Solution SHA-256: `7b64b82bf4cec0fa348bed86676911eeec2725fccdcf75018e03ac1a418f7520`.
Git blob: `ed0d7a3e17e4afcbd9301a0b44da40b56c2c6ab2`.

Request artifact 10323829615 archive SHA-256:
`e23fb417961f7e211768350f3af1674ba19b4dfc1d303b5ae3653483b6ec53ce`.
Verified artifact 10324430655 archive SHA-256:
`a3f354839e2338e4a5358de1e6805a2d5b89b7fa6c8f45a4d5125127cc86c4fa`.
Publication artifact 10324440494 archive SHA-256:
`7026254f27ca40c2b39bca6cffb494f60c8da24ba051f0e322d803cc0ca0ae76`.
All three archives were downloaded and independently digest-checked.

## Mathematical boundary

One fixed positive-circuit family detects all linear inequalities on the
nonnegative kernel. Its support reduction and uniqueness proofs are complete,
not new assumptions. This is classical finite conic geometry formalized for
the project, not a mathematical priority claim or a proof of Polynomial Hirsch.

The exact allocation alternative needed to combine it with accepted #216 is
spelled out in research/FINITE_CIRCUIT_ALLOCATION_NEXT.md. The rank+1 bound,
executable enumeration correctness, whole allocation-to-Minkowski composition,
and arbitrary residual ordinary-edge routing are not asserted by this theorem.
No root dependency edge was manufactured. #210, #208, accepted #216, the pin,
workflows, permissions and secret separation were not changed or triggered.

No local Lean installation was available in this conversation's container;
the actual successful compilation was the pinned hosted verify job. The old
preparation.json remains a historical pre-gate record, not the latest status.
