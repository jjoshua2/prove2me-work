# Reviewed compatibility with official Prove2Me 0.11.0

This is separate trusted-publisher maintenance for PR344, not a proof-branch
version-check bypass, a licensing grant, or a theorem acceptance receipt.

## Official release inspected

Official prove2me/prove2me_workspace tag v0.11.0 points to
2284ae75d2f54883065a7baf8b89fcaea73e67d1, whose parent is the reviewed v0.10.9
commit d49883a1d357fdfee1456ab38e8f40b81e89dcb7. The complete displayed commit diff
changes exactly SKILL.md and references/setup.md. It adds the version metadata,
a public-contributions notice and the optional earlier-contribution licensing
endpoints/flow. There are no changed proof-submission, authentication or Lean
setup contracts in that published diff. Unpublished backend code was not audited.

Sources: official commit and tag above; SKILL blob
c8c3a16713736b5c375db1363cad763b1063c7b1. PR344 run36031864783's publisher stopped
at the existing exact0.10.9 guard after its complete Lean pass. The actual
refresh-response version was not logged and is not inferred as a captured value.

## Exact production change

VersionCheckedAPI.refresh now requires exactly0.11.0 instead of0.10.9. Every
other version, including a missing or malformed value, remains rejected before
token installation. The API host, request body/header/method, timeout, exception,
token installation, expiry and duplicate/pending-job handling are unchanged.
No workflow or credential boundary changes are made.

Original production blob:b233d800b8cfd148ca37b0c4a7e4928b82158239.
New production blob:9826983817f3bc159068b0e9ae4960a39459d1d7.
Replacing the one new literal back with0.10.9 exactly recovers the old blob.
The root SKILL.md preserves its existing local content except its version,
the release's public-contribution notice and the two licensing endpoint entries.
The notice links here for the complete new flow rather than falsely claiming
that all local reference files have been synchronized wholesale.

## Earlier-contribution licensing: no automatic grant

The official release documents that public contributions use Apache2.0 under
the site terms, excluding private content. It adds GET /me/licensing and
POST /me/licensing for earlier public contributions. Account access or permission
to contribute is NOT authorization to accept that retrospective grant.

If an authenticated GET /me or GET /me/licensing shows status pending, tell the
human once and direct them to https://prove2.me/terms#earlier-contributions.
accepted/not_required require no action; inactive means not effective; unavailable
means lookup failure, not acceptance. Only after explicit owner authorization
may an agent POST {"accept": true, "terms_version": "<current status version>"}
to /api/v1/me/licensing. Confirm status accepted before reporting success.
A409 means a stale terms_version;400 means malformed input;503 means a temporary
failure. No error is acceptance. The release explicitly says licensing status
never blocks other endpoints.

THIS MAINTENANCE MAKES NO LICENSING REQUEST. It adds no acceptance code, does not
read the user's licensing state and does not assert that state is pending or
accepted. No consent has been given on the user's behalf. The offline test data
are dummy states, not authenticated account data. Normal already-authorized
proof publication resumes without invoking this optional endpoint.

## Offline regression and boundaries

Run python3 scripts/test_prove2me_protocol_0110.py. Eight methods pass, including
ten rejected-version cases, four nonmapping responses and five dummy licensing
states. Tests extract the actual production class by AST and use an in-memory
opener, never live credentials or network. They verify the exact one-literal diff,
accepted/rejected/missing versions, missing token, original expiry behaviour,
exact request shape and absence of licensing calls or prerequisites. The older
revision-specific protocol tests are retained unchanged as history.

The theorem proof, metadata and explanation in #344 stay frozen at
f9a606ff784dc8882473ac6e8cd9d80e548d2d38. All three compiler stages and all five
reports in both proof logs already pass in run36031864783. Its publication
stopped before registration/submission. This maintenance supplies no platform
verdict. After ordinary review and merge on trusted main, recheck live #344
and use the established new top-level publication request on the same packet;
retain duplicate/pending guards and inspect the actual response.

No Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f change, source repair,
allowlist change, secret exposure, unrelated branch merge or retrospective
licensing grant is included. This is the same separate-review pattern as #342,
with the additional0.11.0 licensing safeguards explicitly retained.
