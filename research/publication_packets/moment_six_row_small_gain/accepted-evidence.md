# ACCEPTED: six-row no-uniform-local-contraction theorem

Theorem: `Hirsch.moment_six_row_no_uniform_local_contraction`.
Theorem ID: `9771bc05-8eb9-4606-a21e-79715873624e`.
Submission ID: `07282fd9-6960-4e2e-bb91-c94a4d994362`.
Authenticated verdict **ACCEPTED**; trusted publisher readback **Proved**.
Do not resubmit this packet.

## Actual publication and frozen source

New top-level conversation comment5735814901 on open same-repository PR #304
invoked `/prove2me publish research/publication_packets/moment_six_row_small_gain`.
It was read back. Bot5735817052 resolved proof/evidence head
ac447cd1aa424a3ec0300ca237e32c20a76bbdda and run35391838355.
The verdict comment5735894829 was posted at2026-09-18T20:37:50Z and read back.
Gate105751735333, verify105751791130 and publish105752391163 completed
successfully; report-verify105752392862 was skipped. The publisher log was read
through trusted-main checkout, authenticated verdict, artifact upload and comment.

The 1001-line solution is unchanged from the earlier passing compiler gate:
blob6a26ad84c3d9b84f16a597ef87e27e41a110d9f7,
SHA2562e48c94e404ad7c006ec8442d10766195327413d5923afd58878582908609fe7.
All three driver/solution/target-statement compile exit codes are zero. All five
transitive reports contain only propext, Classical.choice and Quot.sound. The
intentional placeholder in the separate target stub is not part of the proof.
All five frozen source/target/explanation files match the previous verified bytes.
The new raw manifest records ac447cd1; the earlier manifest records e991bc9b.
Both are preserved, and neither implies a change to the mathematical source.

This was the FIRST actual platform submission, not the first compiler gate.
Two earlier compiler failures remain preserved. The third gate35386824182
compiled the complete proof but publication stopped before registration at the
old platform-version check. This fourth gate recompiled the SAME proof after
compatibility maintenance. Exactly one publication trigger was issued in this
continuation. No mathematical source, target, explanation, hypothesis or pin
was changed to obtain acceptance.

## Reviewed protocol maintenance, not a bypass

Separate PR #305 merged at ec1f9940496d8cb0ed9308ede632d0ec3b62de67, the trusted
main used by this run. Official upstream release a0677c0c4738f16e386545640ceafef4a731cf87
was reviewed. SKILL.md matches its exact0.10.5 blob; the sole runtime edit changes
the exact expected-version literal from0.10.4 to0.10.5. Mismatch rejection stays
in place. Eight offline tests and source assertions pass. No actor allowlist,
API host, redirect policy, workflow, duplicate guard, Lean/Mathlib pin or
verify/publish credential isolation changed. No key was requested or exposed.
The raw authenticated refresh response is not exported or invented.

## Original archives and raw/derived boundary

All three original new archives were downloaded and hashes recomputed:

- request10566168625: e2204b59697e3d9a45d2dbca0dd02b84277e5443a54cbb12da025a287db68a01;
- verified10565754385: 5e86d4ef3d6f6e6e5ebeea63e720525100e8c204019ba4a6fe39c4db70706ba8;
- publication10565648959: 86d7b868bbd2924469979154996e45b76129f9825411b36eeb9d882b5fd75901.

The raw aggregate receipt and publisher comment are committed in this packet.
The current raw manifest, audit and resolved request are under
research/verification/moment-small-gain/publication-resume-*.json.
Earlier full compiler logs and frozen proof files remain unchanged. The selected
publisher excerpt is explicitly an excerpt, not a full raw runner log. Derived
readback metadata is separate. Proved is the publisher's authenticated readback,
not a second direct platform poll from this chat. Individual platform response
bodies absent from the export are not fabricated. No fresh root/leaf mission
poll is claimed. Local Lean/Lake was unavailable; compilation evidence is the
pinned hosted gate, not Python or source-text checking.

## Mathematical scope and new written observation

For every delta>0, construct the original2D/six-row moment family with
0<e<1/4, actual source and target vertices, the COMPLETE two-neighbor set at the
source, positive score gains below delta times the full target gap at BOTH
neighbors, and a three-original-edge route to the target. No vertex, neighbor,
edge or route oracle is supplied. This defeats uniform one-step fractional
contraction for this score, not short paths or Polynomial Hirsch.

The separate MOMENT_TWO_STEP_GAIN_NOTE.md adds a written extension derived this
continuation: the same example also has arbitrarily small gain at EVERY vertex
within two edges of the source, while the target is three edges away. The full
six-cycle and two additional gain formulas are justified there, with a bound
below5e. Nine symbolic identities and41 complete rational graphs support it.
That extension is NOT in this accepted Lean theorem and has no separate platform
verdict. No new packet is submitted for it.

The original59-model rational regression was rerun and reproduces both complete
outputs byte-for-byte. These tests and the new symbolic checks do not establish
formal correctness of Python, JSON parsing, or an additional Lean theorem.
#300/#302, reserved #210, other owned branches and previously accepted targets
were not modified or triggered.
