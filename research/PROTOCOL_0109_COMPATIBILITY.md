# Reviewed Prove2Me 0.10.9 compatibility

This is a separate operational change, not a proof-branch workaround. PR #341's
proof passed complete compilation and all eight standard-only reports in run
35950971172, but the trusted publisher stopped at its exact version guard.
Publisher107479528492 returned "Platform skill version changed; refresh the skill
before publishing." No registration, proof submission or receipt was produced.
The version field from the runtime response was not printed; no raw response
body is invented here.

## Official release reviewed

The official prove2me/prove2me_workspace tag v0.10.9 resolves to
 d49883a1d357fdfee1456ab38e8f40b81e89dcb7,
whose parent/version v0.10.8 is d26f4afe39dc674c3c91195a80876f0cff354b33.
The complete commit diff is one changed line in SKILL.md: 0.10.8 -> 0.10.9.
No reference file, endpoint contract, implementation, or Lean environment file
is changed in that release. The entire tagged skill and the full release diff
were read. This is a version-only compatibility assessment, not a claim to have
audited unpublished backend code or a live authenticated response.

## Narrow production change

VersionCheckedAPI.refresh still rejects every response whose version is not the
one reviewed exact string. Its sole production change is '0.10.8' -> '0.10.9'.
The new file blob b233d800b8cfd148ca37b0c4a7e4928b82158239 reverses byte-for-byte
to 80a674c8a31a37e0122d0bcdf43c17a389e418de when that literal is reverted.
API host, request method/body, timeout, exception, token installation and expiry
logic are unchanged. No permissive fallback or set of accepted versions is added.

The repository SKILL.md is updated only at its version field. Existing local
text/reference choices are preserved; it is not claimed to be an exact full
upstream snapshot. Two transcription-only documentation changes were caught by
a detached comparison and excluded before this branch was prepared. Detached
commit7770b81d2feb7f37a9dbc220530a68e2a11ed5a7 is NOT in the branch's ancestry.

No proof, theorem metadata, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f pin, workflow, allowed actor, duplicate
recovery, receipt format or verifier/publisher credential split is changed.
The blocked radial supporting-script upload is not retried or routed around.

## Executed offline tests

    python3 scripts/test_prove2me_protocol_0109.py

Six methods PASS, including nine rejected-version subcases. The test extracts
the actual production class by AST and uses an in-memory opener with dummy
strings. It checks the single-literal change, acceptance of 0.10.9, rejection
of old/new/unknown/malformed/missing versions before token installation, missing
token failure, exact host/method/body/header/timeout, and existing default expiry.
No live credentials, network calls, publication, or Lean execution are used.
Historical protocol test files remain unchanged as revision-specific evidence.

After separate review and eligible integration into trusted main, recheck #341's
live state and unchanged verified packet, then resume with one new top-level
publication comment. Only that authenticated run can establish registration or
acceptance; this operational update supplies neither.
