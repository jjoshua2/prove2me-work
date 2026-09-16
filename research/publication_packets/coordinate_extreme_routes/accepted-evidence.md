# ACCEPTED: finite-coordinate extreme routes

Public theorem: `Hirsch.finite_coordinate_extreme_route_bound`.
Theorem ID: `1f61b140-7502-4508-a812-53fe712f2ad4`.
Submission ID: `119b7820-4131-4c99-ac87-46ec35dc7249`.
The trusted publisher reports ACCEPTED and authenticated live status Proved.

## Exact trigger and unchanged proof

- PR: #283.
- New top-level command: https://github.com/jjoshua2/prove2me-work/pull/283#issuecomment-5706200622
- Resolved acknowledgement: comment5706201864.
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/283#issuecomment-5706229397
- Run:35163571909; gate,verify,publish all completed successfully; report-verify skipped.
- Frozen accepted proof:74dbb5e144bc9ab4c822daff63dabe4f387d9d76.
- Trusted main:0fe67e3b5da7890bb0f31c2d001a616190cd9e76.
- Solution Git blob:c25b49fed5cedde9c9f7fc457ee214ad8dff1a14.
- Solution SHA256:35b893cad7520244bbcc60707983a6b9a004dd537235a6c0d4efa2bcffe94b7e.
- Verdict comment time:2026-09-16T23:47:40Z.

The357-line proof passed its FIRST prepared compiler/axiom gate and its FIRST
actual platform submission, with no source or metadata edit. Exactly one
publication trigger was issued. All later commits add evidence or handoff
material only. No accepted/pending packet was resubmitted and no other agent's
branch was changed. No workflow, token, protocol, toolchain or secret separation
change was required.

All three compile exits (driver,solution,target statement) are zero. The five
printed declarations descend,ascend,rank_routes,levelRank_bound and solution
use only propext,Classical.choice,Quot.sound. The target statement's placeholder
warning is not an admission in solution.lean; the latter's transitive axiom
reports contain no sorryAx. Local Lean/Lake was unavailable, so compilation is
specifically the hosted pinned evidence, not the finite Python tests.

## Preserved original evidence and independent readback

Raw aggregate publication-receipt.json and publication-comment.md are copied
from the original publisher archive. Raw packet-audit.json, manifest.json,
verified-artifact.json, all three compile logs and publish-request.json are
copied from the original verification/request archives. The archive contains
an aggregate publisher result, not individual raw Prove2Me API responses;
none are fabricated. Live Proved is the publisher's authenticated readback,
not a second platform query by this chat.

All three ZIPs were downloaded and their digests recomputed:

- request10474180200:cf28d85f2ae1d64b1e6ed75c722579b9353c383a67fc3f608ae2411eef365031;
- verified10474245131:8015cb7afdb357c4003281776af4eef3e1584be605c5a8d2d8064ecab0d1a2b7;
- publication10474067279:9c7e1ed49288847a96bbd155fa6fe9d5f9d3ac4db8d7db4f838e8379bb7e9a57.

Every one of the five frozen file hashes was independently recomputed.
Solution,problem and explanation equal the prepared packet byte-for-byte.
The publisher job log was read through verdict, artifact upload and PR comment.
The separately labelled artifact-readback.json is a derived inspection record.

## What is now formal, and what is not

The theorem constructs an actual finite adjacency sequence inside a specified
admissible finite face, bounded by the sum of actual real-coordinate level
counts minus one. The local premises are symmetric adjacency, injective
coordinates, coordinate-extreme face closure and one-step up/down improvement.
No connectedness, short path or finite-length route is assumed. The proof
constructs walks, ranks levels and assembles the two-front induction.

This is the finite combinatorial interface used by research #274/#277. It is
not the full geometric instantiation of those premises on arbitrary compact
polytope edge graphs, not #277's aggregate-cut alphabet theorem, and not a
polynomial global level bound for arbitrary carriers. It promises neither
shortestness nor one globally monotone objective. Classical attribution and
the remaining geometric adapter are explained in explanation.md.

The supporting regression reproduces its complete report byte-for-byte,
SHA256232957a0626afa53eaaa538427db3be14aeea32a196d1daaecbf820a02b914b1:
32 models,257 admissible faces,1623 local-improvement checks,2451 constructed
walks and6733 edges versus4697 shortest-path edges,with812 nonshortest walks.
The four negatively tested inputs violate structural requirements; the test
harness is NOT a proof that each requirement is independently necessary.
In particular the frozen explanation's word "countermodels" must not be
read as claiming four isolated necessity theorems. No such claim occurs in
the Lean theorem. These are finite semantic checks, not verified Python.
