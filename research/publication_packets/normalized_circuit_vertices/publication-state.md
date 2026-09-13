# Current gate state: verified source, pending platform registration

At 2026-09-13 21:29:40 UTC the trusted publisher returned `PUBLISH_PENDING`,
not ACCEPTED, for `Hirsch.normalized_positive_circuits_iff_extreme_points`.

- Exact audited proof head: `cfb93bd2618cf153f8eb00b11918be3ae874b9a7`.
- Actions run: `34783508448`.
- Existing Prove2Me registration job: `b18391ed-b0fc-4e35-8ef2-eadaf500a154`.
- Bot comment: `https://github.com/jjoshua2/prove2me-work/pull/224#issuecomment-5656273613`.
- Solution, driver and statement all compiled with exit0 on the FIRST unchanged gate.
- All four axiom printouts use only propext, Classical.choice and Quot.sound.
- No theorem ID, proof submission ID, or authenticated acceptance is present yet.

`publication-receipt.json` is the unchanged trusted aggregate receipt downloaded
from artifact10325772389. Its archive digest is independently checked in the
clearly labeled `publication-readback.json`. The archive contained only the
aggregate receipt and generated comment, not raw per-job platform responses;
none are fabricated here. Compilation evidence is in `packet-audit.json`,
`verified-artifact.json`, `artifact-readback.json`, and `verification-evidence.md`.

The workflow's trusted main was3f14b493, which includes safe registration-job
recovery. This is not the old lost-job-identity timeout. A later authorized
retry must RESUME the exact matching existing registration rather than create
a second theorem. First read the latest PR comments/receipts and pending job
state; never infer acceptance from the successful Actions run alone. Do not
blindly post duplicate comments while a run is active. This turn made one
publication request and no repeat registration.

Keep this PR draft until the existing registration completes and the frozen
proof is submitted/accepted, or record a precise terminal platform failure.
No source repair or recompile is justified by registration delay alone.
Do not alter the theorem, pin, allowlist, or secret split to address it.

The mathematical source and problem statement are unchanged after the gate.
The companion Python upload was independently blocked by a tool safety-status
check and was not retried through another route. Its three scripts, exact
regression receipts and worked witness examples remain in the conversation's
complete downloadable bundle. They are not committed or executed in Actions.
This proof-publication status applies only to the Lean characterization, not
to formal verification of those Python programs or a new diameter bound.
