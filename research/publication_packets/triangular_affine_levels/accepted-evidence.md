# ACCEPTED: actual triangular extreme points force exponential affine levels

Public theorem: `Hirsch.triangular_extreme_points_force_exponential_affine_levels`.
Theorem ID: `75f43150-aee7-4659-a310-709b352b68a7`.
Submission ID: `fd4ebea0-49c5-4ffb-9555-bbc7509ea2fe`.
Authenticated verdict: **ACCEPTED**; trusted publisher receipt: **live Proved**.

The new top-level comment5705092558 on OPEN same-repository PR #280 triggered run35154649613. The bot acknowledged the exact proof SHA189b32df9e1c50c1c0b771bf6f43033094e06fea in comment5705095084. Trusted workflow main was129c7d4947113733fca17b9b600e93ac65470b12. The final authenticated verdict was posted and read back as comment5705145249.

All three driver/solution/target-statement compilations exited zero. Five printed declarations use only propext, Classical.choice and Quot.sound. One unused-simp-argument warning is retained. The deliberate target placeholder in statement.lean is not an admission in solution.lean. The 395-line proof's first ACTUAL platform submission was accepted; this was not its first compiler gate.

## First compiler failure and exact repair

Run35154253380 at proof21c672bcb24b981ea635e956e63e2ea9d55fc5f4 failed driver compilation. At line192, unrestricted simplification produced a disjunction of scalar equality or e=0 that linarith did not split. Supplying the existing e!=0 hypothesis and using congrArg repairs that exact diagnostic. At line254, rfl substitution removed lo/hi names used below; named equalities plus rewriting preserve them. Those are the only repaired proof sites. Every theorem statement, assumption and conclusion, and all problem/explanation bytes, remained unchanged. The accepted #279 proof body is reused unchanged except its root/print name.

The first failed source, exact selected compiler excerpts, request, derived failure record and patch are retained under research/verification/triangular-affine-levels/. The first run produced no verified packet, registration, submission or publication receipt. Its generated sorryAx reports are explicitly FAILED elaboration evidence, not an accepted audit. The repaired source passed the consolidated validation; no further proof edits or triggers followed.

## Immutable evidence

The original archives were downloaded and their SHA256 digests recomputed:

- First failed request10470656370: 9bffdb3fae44da5f82dca66886025cd1bdc98c4047c5c96b33732c0b8f095c8f.
- Successful request10469893489: b721ff4113bb11520fa6f7199f4629934f7328ca8e286cbe1a15eb9b8c62a2a7.
- Verified packet10470033883: f7215fdc8ac298da966394fd8474d236cdf87fd693d16b63d507a9142d4dedb5.
- Publication10469939202: 940d07baef5dc58e9334012b581ffbe0e2bcc94627cb80f98b5a3feb1a863204.

All five frozen packet file hashes match the immutable manifest. Solution blobf28f3e409914e88aad0d9a1698caad79897612c7, SHA2564d83822ff911107a5183c2426c910af651d1d0ca67cf5cdeabfc5efb4ac9bcee. Raw compile logs/audit/manifest, publication receipt and exact publisher comment are preserved; derived inspection metadata is separate. Final gate/verify/publish jobs completed successfully, report-verify was skipped. Publish log104992108734 was read through verdict, artifact upload and comment. The publisher's receipt reports live Proved; raw target/source API bodies are not exported and are not fabricated. This is not a second direct platform poll from the chat.

## Mathematical scope

For every real0<e<1/2 and every d=n+1, the theorem CONSTRUCTS exactly2^d points, proves each is a Mathlib extreme point of the explicit triangular inequality set, and proves2^d<=K(K-1) for an actual coordinate image under every injective affine embedding. No point family, exponential count, positive distinct displacement family or detecting coordinate is assumed. The recursive extremality proof quantifies over arbitrary feasible open-segment endpoints, not only listed points.

This closes the constructive extreme-point application left after #279. It does not classify every extreme point or graph edge, prove shortest paths, or solve Polynomial Hirsch. Large coordinate inventories are not diameter lower bounds. Classical family and prior accepted counting are credited; no historical novelty claim. Supporting exact tests and the clean replay are not additional Lean theorems. Do not resubmit this ACCEPTED packet.
