# Prove2Me 0.10.8: standalone publisher compatibility review

This is operational maintenance, separate from the Lean-verified #330 proof.
It does not establish platform acceptance, release a mission, or change any
proof, theorem metadata, Lean/Mathlib pin, workflow or actor allowlist.

## Official basis

Reviewed official prove2me/prove2me_workspace commit
`d26f4afe39dc674c3c91195a80876f0cff354b33`, parent
`37902acaf434c14c09f8daaeaaaae2a6fda5c477`.
The full changed-file patch has four paths: SKILL.md, references/campaigns.md,
references/mission_captain.md, and references/mission_solver.md.
The official SKILL blob is `2f03fc8448f16fe79af91e8c6590ea972a75c9ff`.
Its version is 0.10.8. The release documents a mission make-public endpoint,
additional captain faithfulness guidance, and guidance to build missing Mathlib
foundations. It does not change the standalone setup/prove/contribute references.
This supports compatibility of the existing standalone publisher call sequence;
only an actual authenticated run can establish the live outcome.

The failed #330 refresh response did NOT record its runtime version. Nothing in
this review retroactively invents that response, a theorem ID, or an acceptance.

## Narrow implementation

The only production-Python change is the exact expected version literal in
VersionCheckedAPI.refresh: 0.10.7 becomes 0.10.8. The conditional remains `!=`;
unknown, older, newer, missing and malformed versions still raise before installing
the returned token. API URL, timeout, token assignment, expiry, registration,
submission, polling, source checks and duplicate protections are unchanged.
The old publisher Git blob is `099844737f4f8d61a4ea26e28967bf464959673c`;
the new one is `80a674c8a31a37e0122d0bcdf43c17a389e418de`.

SKILL.md receives the reviewed version and new endpoint-table row. Existing role
reference files are not represented as fully synchronized upstream copies here;
the release-specific addendum below records the changed guidance. Before any
mission-management work, read the immutable upstream role references themselves.
This PR's standalone publisher neither uses nor gains a mission-release endpoint.

## Release-specific role addendum

The official mission-release call is POST /missions/:mission_id/make-public,
NOT the theorem-level make-public call. It requires the human's explicit
confirmation: publication is immediate and permanent. The response's made_public
list covers linked mission artifacts and dependencies; unlinked supporting
artifacts can remain private. Mission visibility can remain private pending
moderator review. A 403 denotes wrong creator; a 409 can mean already public or
pending release. A bounced release can be requested again after correction.
None of those calls is authorized or performed by this compatibility maintenance.

The new captain principle is to preserve faithful statements regardless of proof
difficulty. The solver guidance is to search for existing foundations and build
missing ones rather than weaken a target because Mathlib lacks prerequisites.
Campaign-release guidance points to the same explicitly confirmed mission flow.

## Executed offline regression

Command: `python3 scripts/test_prove2me_protocol_0108.py`.
Six unittest methods pass, including nine rejected-version subcases. They execute
the actual production refresh class extracted by AST, with a stub parent and
in-memory JSON opener. Only dummy strings are used. No network call or real
credential is used or recorded. Source Git hashes prove that reversing the one
version replacement restores the entire original production file byte-for-byte.
Tests cover exact endpoint/method/body/timeout, acceptance of 0.10.8, rejection
before token installation, missing version/token, and existing default expiry.
These are Python tests, not a Lean compile or an authenticated platform check.
No Actions file or policy checker changes, so no expensive Lean gate is needed
for this maintenance itself.

## Lifecycle and handoff

Review and integrate this maintenance in its own PR on trusted main. It must not
be inserted into #330's proof branch as a way around trusted-main isolation.
Then recheck #330 comments/jobs and actual packet hashes before creating one new
top-level publication command on the existing PR. Keep its proof bytes unchanged,
preserve the first failed publisher evidence, and follow the new receipt rather
than assume acceptance. #326, #282, reserved #210 and other owners remain untouched.
