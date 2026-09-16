# Reviewed Prove2Me 0.10.4 compatibility refresh

This maintenance change repairs the exact version mismatch blocking the existing compiled #275 bundle. It is not a proof, platform verdict, permission expansion, or guard bypass.

## Upstream review

Reviewed the complete official release comparison v0.10.3..v0.10.4:
https://github.com/prove2me/prove2me_workspace/compare/v0.10.3...v0.10.4

Previous commit: 8d697eeda2f65d396209a9b4f888602de1f55fbf.
Release commit: ed0951e954b66514a6bf29ff716021b3407123d9 (2026-09-15).
Exactly two upstream files changed: SKILL.md version 0.10.3 -> 0.10.4 and references/communicate.md. The latter documents server-set is_agent provenance for comments/replies. Registration, proof submission, verification polling, authentication endpoint and payload schemas have no documented change in this release comparison. No client-supplied is_agent field is needed.

The two refreshed files match upstream byte-for-byte:
- SKILL.md blob 39798b14c10fbc6843fffa5f968cf48e68e73593.
- references/communicate.md blob a5128681757cb431927b69ab2e879c4840867a8f.

## Narrow runtime change

scripts/prove2me_comment_publish.py imports VersionCheckedAPI from scripts/publish_projective_small_blocks.py. That class still required the literal 0.10.3 despite the new official release. Its ONLY runtime change here is the expected literal to 0.10.4. It still rejects old, missing, malformed and future versions before assigning a token. The auth URL, method, payload, timeout, receipt handling, duplicate-theorem recovery, compiled-artifact hashes, actor allowlist, workflow permissions, Lean/Mathlib pin and secret isolation are unchanged. Removing or automatically accepting the version guard is not part of this fix.

The original runtime file was reconstructed from its fetched content and checked against blob c574e0dc5aeaa2164dc3c7498b7707a44677dd3e before editing. The new blob is 91aaddfbe4c65c043ab3646412217a04521417c2.

## Actual offline checks

python3 scripts/test_reviewed_platform_version.py

Nine unittest cases pass. They execute the actual refresh class with a fake opener, test the exact auth URL/body, token/expiry handling, reject unsupported/missing/malformed versions, verify both official documentation blob identities, and prove that reverting the single version literal recovers the exact old runtime blob. No key or token was read from the environment or sent over a network; fixture strings are not credentials. These tests are not a live authenticated platform probe and do not imply a proof is accepted.

## Safe continuation

A concurrent #275 retry (35135897207) completed verification but failed publication while this review was being prepared. Do not repeat or overlap active publication runs. After this change reaches trusted main, reread #275's exact head, latest comments, packet hashes and any registration/submission receipts. A NEW top-level /prove2me publish research/publication_packets/affine_pair_conditioning comment can then use the unchanged existing bundle and the trusted publisher's duplicate-recovery logic. Preserve the actual authenticated verdict; never infer it from compilation. The current proof source and statement are not changed by this PR.
