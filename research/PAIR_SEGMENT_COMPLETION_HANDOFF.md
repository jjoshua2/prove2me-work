# PR #311: explicit pair-segment completion — ACCEPTED

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and current PR
heads/comments before taking further work. This continuation resumed the existing
#311 from main 24b519ae1e7907a0d063cd36731d435da9918765. Other owned work and
reserved #210 were untouched; no duplicate packet or new branch was created.

## Current authoritative result — do not resubmit

Hirsch.finite_hull_pair_segment_completion is ACCEPTED, with trusted publisher
live Proved. Theorem f8820d5a-523e-42b2-a856-1ebfaf2c93db, submission
0307a57f-c4be-4cf2-ac81-80e04b743201. Frozen proof
13930c76be3706447fc4d6dfd02f5ce4cf221a2e; run 35422809743.
NEW top-level command 5739508003, resolved acknowledgement 5739509123 and
verdict 5739529634 were read back. Gate, verify and publish completed successfully;
report-verify skipped. All three compile modes exit zero; all five transitive
reports contain only propext, Classical.choice and Quot.sound.

Read the packet's accepted-evidence.md, raw publication-receipt.json,
packet-audit.json, manifest and complete compile logs. The derived final run
record is verification/pair-segment-completion/final-publication-readback.json.
Proved is the publisher's authenticated readback, not a separate direct platform
or root/leaf mission poll. Missing individual API responses are not invented.

## Both proof repairs are closed; failures remain history

Accepted source 283 lines / 11766 bytes, blob
756319de8d9d6d2d00941f48a87ff9c572ce35e6, SHA256
ac3bddf6ecc4dd20b3360e75d759013620bee82593065481205e7fe966a85bb5.
It matches the previously saved two-helper proposal exactly. Its only changes
from the second gate are explicit smul_sum equalities in point_combo and explicit
pair/update reduction followed by abelian normalization in replace_endpoint.
All signatures, assumptions, corrected public statement AND root proof, and both
metadata files remained unchanged. No post-success proof edits or new triggers.

First run 35420782170 failed on binder scope, nonexistent update-lemma names and
an unreduced membership goal. The public sum syntax was malformed and needed
parentheses in source AND formal_statement; intended mathematics was retained,
but metadata bytes changed before any registration. Second run 35421714330
failed at the two helper bodies now repaired. Both failed-elaboration histories,
raw requests, source/target snapshots and proposals remain preserved. The old
handoff is copied verbatim to handoff-before-acceptance.md. Earlier proposal
readbacks saying UNCOMPILED describe their earlier time; both proposals have now
been applied and the full current proof is accepted.

This was the THIRD compiler gate overall and FIRST actual platform submission,
with ONE new trigger this turn. Local Lean/Lake was absent and compiler-host DNS
failed. Actual formal evidence is the pinned hosted gate, not the source or
rational checks. This result does not retroactively turn earlier runs green.

## Exact mathematical obligation now closed

For any n>0 real generators v_i in R^d, P=conv{v_i} is an actual Minkowski summand
of the explicit Z=sum_(i,j)[v_i,v_j]. The other summand is not supplied: it is
Q={q: q+v_i in Z for all i}, whose nonemptiness, compactness and convexity are
proved, together with WHOLE-SET equality P+Q=Z. The coefficient cube describes
all of Z, not merely its sampled points or a vertex subset.

For any f choose k maximizing f(v_i), select v_k on slots (k,i) and maximizing
endpoints elsewhere. The resulting z maximizes f on Z. One-slot replacement
gives z-v_k+v_i in Z for EVERY i, yielding a genuine erosion witness q=z-v_k.
The zero objective proves nonemptiness. Coefficient compactness/convexity and a
compact bounding translate establish the body properties. Convex hull closure
extends translations to all of P, and strict separation proves equality.

No independence, full dimension, distinctness, generic objective, assumed support
equality or summand is a premise. Repeated/interior generators, n=1 and d=0
are included. The represented ordered segment-slot count is exactly n^2,
including diagonal and duplicate slots. No minimality or facet count is asserted.
This concrete completion obligation is CLOSED; reuse the accepted proof rather
than another child assuming the same erosion equality.

## Remaining conjecture-facing work

The packet does not construct a short walk of actual exposed edges in Z.
Coefficient-cube edges may project to nonedges and must not be used without a
whole-face proof. The next route theorem needs actual endpoint vertices, genuine
original exposed segments and a count that handles repeated/zero directions.
Accepted #309 gives summand contraction and #310 gives original-H endpoint lifts
once an appropriate sum-route bound is available; neither is to be resubmitted.

The n^2 budget is in INPUT GENERATORS. A full vertex inventory of a polytope
specified by H inequalities can be large, so this construction gives no
polynomial bound in original facets. Applying it to dual generators would still
need a proved transfer to the primal ordinary-edge graph. A large count here is
not a lower bound for every other completion. No unrestricted Polynomial Hirsch,
new best classical bound or historical priority is claimed.

## Evidence and reproducibility

The three new original artifacts are request 10578700424, verification
10578780479 and publication 10578640739. The two older request archives are
preserved. All FIVE archive hashes and all FIVE frozen packet hashes were
recomputed; raw evidence and derived summaries are labelled separately. The
publisher log was read through verdict, upload, comment and cleanup; it is not
mislabelled as a completely committed runner log. Full archives accompany export.

The unchanged exact regression reran and repeated in a clean script-only
workspace: 46 complete planar models, 1208 support witnesses, 6627 replacements,
42189 coefficient bounds, nine selected instances through d64, nineteen saved
witnesses audited with discovery disabled and four rejected forgeries.
Report 12437 bytes, SHA256
978578e2dd9cc9edee710aecd9a9ec86babc7661f5ed2ac995bde887670bdd5b;
fixture 33706 bytes, SHA256
efc7e10a8b59cd961323e85556ac6f5919c001d0c2f2d8c3a4f26ea2343ce625.
They reproduce the previous bytes exactly. Supporting tests are not Lean-extracted
Python/JSON verification. The full outputs are bundled and regenerate:

    python3 scripts/test_pair_segment_completion.py --out /tmp/pair-completion

Lean4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5
guard, workflows, actor allowlist, duplicate guards and trusted verify/publish
credential separation are unchanged. Consult live PR metadata for the later
evidence/merge SHA; it is different from the frozen accepted proof SHA.
