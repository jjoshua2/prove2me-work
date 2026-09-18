# Publisher version compatibility blocker, not a proof failure

Run35386824182 fully compiled and audited the exact1001-line proof. Publisher
job105736124723 stopped before registration with:

    Platform skill version changed; refresh the skill before publishing.

Trusted main d6e667d1d2ffa4eaa012e941fadec2898b6f9c5c imports VersionCheckedAPI
from scripts/publish_projective_small_blocks.py. That class requires the refresh
response's version to equal0.10.4. The official workspace now advertises0.10.5:
prove2me/prove2me_workspace commit a0677c0c4738f16e386545640ceafef4a731cf87,
SKILL.md blob3b64e0d72acd92c8e052b65624c059978ca66748. The actual authenticated
response's version value is not printed, so this record does not invent it.

The official commit was read: its SKILL change is0.10.4->0.10.5; the other
change is references/mission_captain.md, documenting moderator review rounds,
Changes requested, per-item flags and correction-by-replacement/private-release
flows. It changes neither the Lean pin nor the solver proof's mathematics.
No credentials were requested or exported, and the version guard was not disabled.

Next publication prerequisite is a reviewed trusted-main protocol refresh against
that official release, keeping exact-version rejection, duplicate protection,
endpoint restrictions and verify/publish isolation. Do not merely remove the guard
or modify untrusted PR code to obtain secrets. This continuation makes NO trusted
publisher, skill, workflow, allowlist or secret change and launches no extra run.

After compatibility is restored, retain the exact compiled solution and metadata;
check live comments and platform duplicate safeguards before a normal publication
resume. No theorem/submission was created by the observed version-failed attempt,
but a later agent must check again rather than assume that remains true. The
current frozen request and verified artifact provide the exact proof bytes.
