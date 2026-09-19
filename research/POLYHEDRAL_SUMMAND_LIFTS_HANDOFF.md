# PR #310: original-H endpoint lifts and route transfer — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live exact
heads/comments before continuing. This resumed existing #310 from main
c766c3f769b06912c481fd305d857e73d9546811. Other owned #244/#300/#302 work and
reserved #210 remain untouched. No duplicate PR or accepted target was submitted.

## Authoritative current result

Hirsch.polyhedral_summand_endpoint_lifts_and_routes is ACCEPTED, with authenticated
publisher live Proved. Theoremab046a79-d0fb-47da-abac-df85c1ace598,
submissionb4a42675-7736-461c-830a-639d9d778c46.
Frozen proof9107fa9c847d1ed9ccea4fab30ad1b7aaf04b7e5; run35419573011.
NEW top-level trigger5739124217, acknowledgement5739125519 and authenticated
verdict5739147492 were read back. Do not resubmit this packet.

All three compiles exit0, all five transitive reports contain only propext,
Classical.choice and Quot.sound. Gate/verify/publish completed successfully;
report-verify skipped. Read the packet's accepted-evidence.md, raw receipt,
audit and full compile logs. Derived run details are under
verification/polyhedral-summand-lifts/resume-publication-readback.json.
Proved is the trusted publisher's readback, not a separate platform/root poll.
Local Lean/Lake was unavailable; the pinned hosted gate supplies formal evidence.

## Previous convexity blocker is closed

The accepted603-line/27878-byte source is exactly the saved proposal:
blob4235c1e90effe3546d3ad6595032b093ef00028b,
SHA2569c742306ff5c2bfd16bbf64e74d224450f19bf69f3d1d634415a37ccdcf58687.
Only body_convex's last proof step changed to add_le_add and explicit factoring
with s+t=1. Every statement, assumption, public root, metadata and the complete
accepted343-line #309 prefix is unchanged. The saved repair is now applied and
verified; do not treat its historical UNCOMPILED record as current status.

There were THREE comment-triggered attempts overall, but only TWO actual Lean
compilations. First35415267769 stopped before Lean on a documentation token;
second35415626388 failed the convexity proof. This continuation posted exactly
ONE new gate, which passed and made the FIRST actual platform submission.
No post-success proof edits or further triggers. Both earlier source/request/
diagnostic histories remain. The old handoff and proof note are copied to
handoff-before-acceptance.md and proof-note-before-acceptance.md.

## Closed original-endpoint applicability

P is any finite original H-polyhedron. At every actual extreme u, the original
active-row kernel is zero, by a symmetric finite-slack perturbation. Summing
all active rows gives a functional uniquely maximized at u. Its compact maximizing
face in nonempty compact Q has an extreme point q, also extreme in Q. Applying
the functional to a convex decomposition of u+q forces both first components
to be u, then Q extremality proves u+q is an actual sum vertex.

No objective, rank, basis, finite Q catalogue or compatible endpoint is assumed.
P may be unbounded, lower-dimensional, nonsimple or redundantly represented;
Q need not be polytopal. The proof covers tied maximizing faces and dimension0.
Convexity of P is derived directly from its ORIGINAL inequalities.

For independently chosen P vertices u,v, the result constructs their compatible
sum endpoints, uses an ASSUMED genuine uniform all-pairs exposed-edge bound B
on P+Q, and invokes accepted #309 unchanged. Unique decomposition identifies
both contracted endpoints as exactly u,v; deleting stationary transitions gives
an original exposed/extreme-edge route of length at most B. The endpoint-lifting
and endpoint-identification obligations are therefore CLOSED.

## Actual remaining conjecture-level requirement

Nonempty compact convex Q and an actual uniform sum-route bound remain explicit.
This result does not construct a short-routable completion of an arbitrary P or
control its row/facet complexity. A conjecture proof still needs such a construction
with a bound in the original input parameters, or a different direct route argument.
Neither arbitrary projections nor assuming every completion has moment/Gale
structure is justified. Do not recreate another conditional endpoint-lifting
child; reuse this accepted theorem. No shortestness or historical novelty claim.

## Evidence and exact regression

All five frozen packet hashes and all five original ZIP hashes were checked.
Raw receipt/manifest/audit/logs are distinct from labelled derived readbacks;
absent individual platform response bodies are not invented. The publisher log
was inspected through verdict, artifact upload, comment and cleanup.

The unchanged two-script exact regression reran:25 models,114 lifts,566 endpoint
pairs,3033 generator comparisons;1186 sum steps contract to741 factor steps,
removing445 stationary transitions. Five tied maximizing faces, four unbounded/
lower-dimensional lifts and12 selected box examples through dimension64 are
retained. Nineteen saved records audit with construction disabled; five forgeries
fail. These are supporting checks, not Lean-extracted code or a verified H parser.

Full report12100bytes SHA256
f0deb1fb5d00e4acc5f2612ff8ffa15485843abfc4769b92a56f76b6bc35c810;
fixture22185bytes SHA256
d83747025439cedb4ae48843292747ab102c47716e53e490743a7459c56ad61f.
Both match prior bytes exactly. Full archives and fixtures accompany the bundle.

    python3 scripts/test_polyhedral_summand_lifts.py --out /tmp/summand-lifts

No existing main proof, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5 guard, workflow, allowlist,
duplicate safeguards or verify/publish credential split changed. Use live PR
metadata for the later evidence/merge commit, not the frozen proof SHA above.
