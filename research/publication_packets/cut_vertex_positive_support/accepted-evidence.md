# ACCEPTED: constructed positive support and unique active-cut recovery

The trusted comment publisher reports ACCEPTED and authenticated live Proved
for `Hirsch.cut_vertex_positive_support_certificate`. Do not resubmit it.

- Theorem: `1043e661-f761-4ee3-9d75-2822a58c77f9`.
- Submission: `ac775547-35a3-498c-ab38-ad117c2a4d11`.
- Registration: PUBLISHED.
- Frozen proof head: `64b73e31cdf368e36e6bd76f1710f4fc97760ebb`.
- Run: `35208220079`.
- Actual publication command: https://github.com/jjoshua2/prove2me-work/pull/291#issuecomment-5712490425
- Resolved-head comment: https://github.com/jjoshua2/prove2me-work/pull/291#issuecomment-5712492494
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/291#issuecomment-5712544947
- Verdict time: September 17, 2026, 10:05 UTC (06:05 America/New_York).

## Exact compiled proof and evidence

The 322-line standalone solution passed its FIRST pinned compiler/axiom gate
and FIRST actual platform submission unchanged. Driver, solution and target
statement exit codes are all zero. All four transitive proof reports contain
only propext, Classical.choice and Quot.sound. There were no repair commits,
new axioms, self-imports or proof admissions. The separate target stub uses
by sorry only to specify its type, not as part of the submitted proof.

Source blob: `ab4d4fa5c0c4e976c62c1b856ace11bec3bf0afd`.
Source SHA256: `7dc54444294016077ebd86c7132a1a26e5250af584a7311e49067f364891c2cb`.
The 8163-byte accepted #290 namespace prefix is reused byte-for-byte, excluding
only its old public solution and print suffix. It is a real proof dependency,
not a newly assumed theorem. The old accepted theorem was not republished.

All THREE original archives were downloaded and independently hashed:

- request artifact10491300549, SHA256 `1173e15f217d52d6a9be2bfe96144339dcec74cb76c6ebcf9c17e01f0b7aec19`;
- verification artifact10491146791, SHA256 `7595b41fcca904270cb8c192d7c6d960fbcf3a74c9a10787bb8fbe6904cd1d00`;
- publication artifact10490658215, SHA256 `90342159c45d8e8f9dcc4ad7ef363afe2c1ba988ed132493c8d40dc017547ff7`.

All five frozen packet file hashes were recomputed. Source, metadata and
explanation match the originally prepared bytes. The raw request, packet audit,
verified artifact, verification manifest, solution compile log and aggregate
publication receipt are committed separately from derived readbacks. No absent
individual API objects have been invented. The initial prepared manifest is
preserved verbatim; source-manifest.json now indexes the accepted state.
Post-gate changes are evidence only, not proof, target or explanation changes.
No local Lean/Lake executable was available; successful compilation is the
pinned hosted gate, not a supporting Python test relabeled as a local build.

## Exact new mathematical interface

For any actual extreme point x of convexHull(S) cut by finitely many halfspaces,
the theorem CONSTRUCTS a positive affinely independent finite support in S.
No support, weights, affine independence, active-image rank, or support-size
bound is an input. The support's active-cut images remain affinely independent,
and n is bounded by BOTH d+1 and number of active cuts+1. On that selected
support, all active cut values and total weight one uniquely recover the real
weights, even among signed alternatives. S need not be finite or compact.
Support points belong to the base and may individually lie outside the cut set.

This closes the positive support-selection/recovery step after accepted #290
and the written #277 cut-image argument. It is classical Caratheodory/convex
geometry formalized for this interface, not a historical novelty claim.
Uniqueness concerns the weights on the selected support, not the support
itself: different positive supports can represent the same cut vertex.

## Next exact obligation, without an assumed quantitative shortcut

Choose a minimal independent subsystem of the ACTIVE evaluations sufficient
for the selected support. Concretely, one expects to retain the mass row and
n-1 independent active rows, giving an invertible square system for the weights.
That row-selection theorem is NOT included in this packet. Combined with the
new existence theorem it should feed finite cut-image enumeration without an
externally supplied support or injectivity certificate. Finite support size
alone does not bound the total support/catalogue inventory for arbitrary
carriers, and neither this result nor #290 proves Polynomial Hirsch.

The other agent's #289 odd moment catalogue and all independently owned branches
were left untouched. Coordination is #290 comment5712364514. No workflow,
permission, pin, secret handling or pending/accepted submission was changed.

## Separate exact supporting tests

Six original-H models produce34 cut vertices from178 square systems. The test
selects68 positive independent supports and uniquely recovers their weights,
including34 cases with redundant generators and43 selected point occurrences
outside the cut set. Six sharp examples include dimension0 and extend to16.
Seven malformed/out-of-scope controls and inactive gaps through2^-240 are
retained. A clean workspace reproduces the report and all49980 fixture bytes
exactly. The six-addition source patch also applies byte-for-byte in an empty
Git workspace and the Python test compiles. These are supporting tests, not
Lean-extracted runtime or parser correctness. They are not the basis of the
ACCEPTED verdict.
