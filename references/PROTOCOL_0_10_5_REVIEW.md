# Reviewed solver-protocol refresh: 0.10.5

Source: prove2me/prove2me_workspace commit
`a0677c0c4738f16e386545640ceafef4a731cf87` (2026-09-18), parent
`ed0951e954b66514a6bf29ff716021b3407123d9`.
The commit's complete two-file diff was inspected through the GitHub connector.
Canonical upstream commit:
https://github.com/prove2me/prove2me_workspace/commit/a0677c0c4738f16e386545640ceafef4a731cf87

## Scope and compatibility assessment

The release changes SKILL.md's metadata version from 0.10.4 to 0.10.5 and updates
the mission-captain guide. The guide adds the editable `Changes requested`
moderation status, owner/moderator review rounds (`reviews`), per-item `flags`,
and instructions for repairing a rejected proposal or private-mission release.
Published statements remain immutable. Human review/launch remains human-only.

No direct solver registration, verification, polling, accepted-source readback,
or authentication endpoint contract is changed by this reviewed release diff.
There is no theorem/Lean environment update in it. The local SKILL.md is the
exact upstream 0.10.5 blob `3b64e0d72acd92c8e052b65624c059978ca66748`.
This maintenance does not exercise mission creation, moderation or release.
Before such captain operations, read the updated authoritative upstream guide:
https://github.com/prove2me/prove2me_workspace/blob/a0677c0c4738f16e386545640ceafef4a731cf87/references/mission_captain.md
The local legacy captain reference is not represented as newly synchronized.

## Minimal runtime change and unchanged boundaries

In `scripts/publish_projective_small_blocks.py`, the only changed bytes are the
expected-version literal in VersionCheckedAPI.refresh: 0.10.4 becomes 0.10.5.
The guard remains exact string equality; missing, old, future and malformed
versions are rejected BEFORE the returned token is installed. There is no
wildcard, runtime auto-accept, suppression, extra credential input, or new host.
The error does not echo the raw authentication response.

The inherited redirect-denying transport, API URL, request structure, token
handling, packet/axiom/hash checks, duplicate guards, comment parser, actor
allowlist and workflow secret separation are unchanged. No workflow file,
allowlist or Lean/Mathlib pin is modified. The supported theorem publisher
continues to run trusted-main code, never candidate-branch Python with a secret.

## Offline tests and limitations

Run `python3 scripts/test_prove2me_version_0105.py`. Eight unit tests execute the
actual class AST with an inert base and a fake opener; the refresh method itself
is unchanged. They test exact acceptance, twelve mismatch/missing cases,
unchanged destination/method/payload/timeout, missing-token failure, expiry,
propagated transport errors, and absence of credential-like dummy output.
Two source assertions bind the exact upstream SKILL blob and prove that reverting
the single runtime literal restores the original script Git blob
`91aaddfbe4c65c043ab3646412217a04521417c2`.
These are offline unit tests, not authenticated service calls, full HTTP
integration tests, Lean verification, or a Prove2Me verdict.

## Resume the already verified #304 proof

Run 35386824182 compiled and audited proof
`e991bc9b85bc60381f1b5fea283f4538dfaaa228`; the subsequent publisher stopped on
the old version check before theorem registration. Its authenticated response
version was not exported. Public upstream advertises 0.10.5, but the next actual
refresh must still satisfy the exact guard; no successful connection is assumed.
After this maintenance is integrated, recheck #304 comments and receipts and
use one NEW normal top-level publication comment for the SAME packet. Do not
change or rename its theorem, weaken its assumptions, duplicate a pending or
accepted submission, or use an old-run rerun that checks out the old main SHA.
