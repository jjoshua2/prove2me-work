# Publication stopped before registration: strict protocol refresh required

Run35460242988 compiled all three packet modes and passed five standard-axiom
reports. Publisher105942959283 stopped before theorem registration/submission:

    Platform skill version changed; refresh the skill before publishing.

The actual refresh response body and returned version were not logged. No
publication receipt exists. Bot5744227133 confirms this absence. It is not a
Lean failure, mathematical rejection, or permission/secret failure.

Trusted main6b0ed8524c0b16b3e4acbc1f5c73708e2d221082 uses VersionCheckedAPI from
scripts/publish_projective_small_blocks.py, blob
e03550a5dd351b67cc4921d66fe13171d474681b. Its refresh method explicitly rejects
any version other than0.10.5 before assigning the refreshed access token.

Official prove2me/prove2me_workspace commit
32b755663224d6c3f572406e893e9b10ca652202, dated2026-09-19T17:35:25Z, has parent
a0677c0c4738f16e386545640ceafef4a731cf87. Its COMPLETE diff changes only:

    metadata.version: 0.10.5 -> 0.10.6

The new official SKILL.md blob is9848cfa34065eb650e2de3fb9be81786045cfca5.
No endpoint or reference-file change appears in that commit. These are inspected
upstream source facts, not a fabricated authenticated refresh body.

Next maintenance should review that exact release, synchronize the trusted
skill/client version, and test matching, stale, future, missing and malformed
version responses locally without credentials. Preserve EXACT-version rejection,
API-host restrictions, allowlist, duplicate safeguards and the separate trusted
publisher. No disabling guard, using a candidate PR script with secrets, or
requesting credentials in chat. No such maintenance was applied this turn.

After maintenance is integrated into trusted main, refresh live PR comments and
receipts before a normal new top-level publication command on existing #313.
Use the SAME theorem/packet and unchanged Lean source. The previous attempt
registered/submitted nothing, but newer pending or accepted activity must still
be checked before any resume. No speculative retry of the old frozen workflow.
