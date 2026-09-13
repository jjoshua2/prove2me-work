# Actual successful compilation and axiom audit

The corrected packet at proof head1f13787356e7aee48c2fa6e026915f2d4c0805b2
passed the pinned Lean4.30.0 verification gate in Actions run34785744936.
Driver, solution and statement exit codes are all0. All four audited
declarations use only propext, Classical.choice and Quot.sound. The three
concrete finite examples also passed by decide +kernel, not native_decide.
This certifies both the generic checker theorem and those concrete examples;
it does not certify the Python parser or every future exported table.

The original gate34785381971 failed before any platform registration at two
cast-normalization sites and default decide reduction. The repair changes
only elaboration/decision construction: explicit beta-normalization, direct
inferInstanceAs, and kernel-mode decide. Public statement, assumptions, finite
checker predicates, example data and expected outputs are unchanged. The first
failure remains documented in research/CHECKED_CIRCUIT_FIRST_GATE.json.

The successful verified artifact10326900522 was downloaded and independently
hashed as04bf5e00dfb646ac51efc55cdd8b7a8d4727fc9b089fd7f80f1800f65461b8a7.
All five frozen hashes were recomputed; solution, problem and explanation
match the PR packet byte-for-byte. packet-audit.json and verified-artifact.json
are exact downloaded records. artifact-readback.json is an explicitly labeled
local derived check, not a fabricated raw platform response. Full original
archive and compiler logs are in the downloadable conversation package.

Compilation/audit success is not Prove2Me acceptance. The trusted publisher is
a separate job; consult its actual later receipt and verdict. No duplicate
registration should be requested just because its status is not yet terminal.

The two companion Python files are actually committed on this PR and tested
locally; the frozen proof job does not execute untrusted candidate Python.
All older accepted packets and other agents' branches are unchanged.
