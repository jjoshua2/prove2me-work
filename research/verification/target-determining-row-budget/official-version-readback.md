# Read-only official compatibility evidence

The official repository prove2me/prove2me_workspace was read through GitHub.
Its main ref resolved to d26f4afe39dc674c3c91195a80876f0cff354b33. SKILL.md at
that exact commit has blob2f03fc8448f16fe79af91e8c6590ea972a75c9ff and metadata
version0.10.8. This is an observed official file version, not a reconstruction
of the failed runtime refresh JSON. That response's version was not logged.

The trusted publisher at bfacf0fca8aac4205569070d224ee8cc736ef38d uses
scripts/publish_projective_small_blocks.py, blob099844737f4f8d61a4ea26e28967bf464959673c.
Its VersionCheckedAPI.refresh accepts only version0.10.7, and raises the observed
error BEFORE assigning the access token when the returned version differs.
The comment publisher imports this class. No theorem registration or proof
submission is reached on this failed refresh path.

No guard, allowed-actor list, workflow, credentials or toolchain was changed.
The current proof remains frozen. A new protocol version requires a SEPARATE
review of the official skill/API changes and an approved trusted-main update
that keeps strict version and verification/publication isolation. This note is
not that review and does not assert API compatibility. Do not merely suppress
the guard, accept arbitrary versions, or change it on this proof branch.
