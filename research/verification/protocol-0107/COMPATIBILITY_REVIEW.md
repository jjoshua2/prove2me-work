# Prove2Me 0.10.7 compatibility review

## Official evidence

Reviewed the complete official commit diff, not just the version string:
https://github.com/prove2me/prove2me_workspace/commit/37902acaf434c14c09f8daaeaaaae2a6fda5c477

The release is dated 2026-09-20T21:29:59Z and has parent
32b755663224d6c3f572406e893e9b10ca652202 (0.10.6). It changes exactly two files:
SKILL.md's version and references/mission_captain.md's statement-faithfulness
section. There are no API endpoint, payload or authentication-code changes in
this release diff. This is evidence about the published workspace release, not
a claim that an unlogged authenticated response was independently observed.

The eight expanded principles concern section-wide assumptions, two-way matching
of hypotheses and conclusions, defaults of total functions on bad input, exact
quantification domains, edge inputs, manual formula checks, shared definitions,
and conventions at changes of regime. These were reviewed in full at the official
commit. The old local captain reference is NOT silently called synchronized here;
consult the immutable official reference for captain work. This solver maintenance
does not create or curate a mission proposal.

## Narrow implementation

Only one runtime literal changes: VersionCheckedAPI.refresh now requires exactly
0.10.7 rather than 0.10.6. Restoring that literal reproduces the entire previous
publisher blob e20f826cdd582ad9ed5ec775c45d0f63b1069ae6, as checked by the new test.
The new publisher blob is 099844737f4f8d61a4ea26e28967bf464959673c; SHA256
cf75db27010b5cf1a2fefde7c09982f683f1e12e1415c2f290a89380289a51f5.

SKILL.md is updated to 0.10.7. Its local copy also makes the Pick a target step
explicit with the words 'to formalize against'; it is not asserted byte-identical
to the upstream skill blob. The endpoint table and all authentication and submission
rules are unchanged. This prose addition grants no new permission.

No API host, redirect behavior, duplicate/pending/accepted guard, workflow, actor
allowlist, cache setup, Lean/Mathlib pin, proof packet or credential isolation
changes. The existing mismatch error remains fatal. No credential was read locally.

## Actual executed offline verification

python3 scripts/test_protocol_refresh_0107.py

All 12 cases pass using the ACTUAL source method isolated through AST extraction.
Two supported responses exercise explicit/default expiry. Nine unsupported version
forms are rejected, including 0.10.6, 0.10.5, 0.10.8, absent/null/numeric version,
suffix, whitespace and v-prefix. A missing-token response also fails. Tests verify
the exact official URL, POST body, JSON content type and timeout, no unsolicited
Authorization header, unchanged state on these failures, and no printed output.
Python syntax compilation passed for both changed/new scripts. The JSON file is a
compact serialization of these executed test results, not a platform receipt.

This is not a full-repository Python test run or local Lean compilation. Older
version-specific test scripts remain historical and need their pinned heads.
The runtime has no Lean/Lake and cannot resolve public source/toolchain hosts.
No expensive Actions test was used to develop this compatibility change.

## Publication scope

PR #320's source remains at verified proof 2efb69e4e25165bfd2a5abc2fe2673d950114ab9,
blob d601bb6d8c223609a9b9b269385421f4e0bbc39b. All five files in its downloaded
frozen manifest were independently rehashed in this continuation and match.
Its failed publication run35624792380 stopped before registration/submission.
This maintenance must be reviewed on a separate PR and normally merged before
another NEW top-level publication comment on #320. The next publisher must still
perform live exact-target/pending/accepted checks; do not duplicate work or weaken
the version guard if the service differs again. No service success is implied here.
