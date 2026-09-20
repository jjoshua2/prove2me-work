# PR #319: all-completion edge-direction inheritance — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and LIVE exact
PR heads/comments before further work. Main at selection was
56edc3105ff0dd1f373d28601b578cc0c441a7b2. This resumed the existing local-only
candidate instead of duplicating accepted #316/#317/#318. Coordination on #318
was 5750301673, posted/read back. Reserved #210 and other owned work are untouched.

## Authoritative accepted state: do not resubmit

Hirsch.zonotope_completion_original_direction_obstruction is ACCEPTED, with
trusted publisher readback Proved. Theorem da8f6dad-a557-46a6-99ad-11ef6d2e5a9c;
submission eff892fe-babc-4217-ae49-2eb46336d233.
Frozen proof 7b1d1e7199de25855c5eadafe277a763796eaeb5;
run 35515972056. NEW top-level trigger 5750350283, resolved acknowledgement
5750351204 and authenticated verdict 5750368908 were read back.
Gate/verify/publish completed successfully; report-verify skipped.

All three compile modes exit zero; all five transitive reports contain only
propext, Classical.choice and Quot.sound. FIRST compiler gate and FIRST platform
submission, exactly ONE trigger; no proof repair or post-gate source/metadata edit.
Local Lean/Lake was unavailable. Formal compilation is the pinned hosted evidence,
not source comparisons or rational tests. Proved is the publisher's authenticated
readback, not another direct platform or mission-root poll. Missing API bodies
and full runner-log files are not invented.

Read the packet's accepted-evidence.md, raw publication-receipt.json, audit,
manifest and full compiler logs. Derived readbacks are under
research/verification/completion-directions, separately labelled.

## Closed generic mathematical interface

For finite P=conv(C), nonempty compact Q and actual whole-set equality
P+Q=sum_i[0,w_i], every genuine exposed edge direction of P must be parallel to
a nonzero w_i. C need not list vertices only; Q need not be convex. A selected
family of r pairwise nonparallel actual original edges yields a DERIVED injective
selection of r parallel generators and r<=m. Accepted #317 then gives opposite
actual completion vertices for which EVERY genuine exposed-edge walk has length
at least r. Graphs, exposing objectives, direction matching and route cost are
not supplied as oracles. Other generators may be zero, repeated or dependent.

The contradiction proof removes the edge direction by transverse projection,
then uses finite regularization on projected generators and original corner gaps.
The constructed objective remains constant along the edge and maximal there,
but would be regular on Z if no parallel generator existed. Maximizing on compact
Q translates both distinct edge endpoints into a supposedly singleton Z face.
This proves inheritance. It is not an arbitrary projection-of-edges argument.

The inheritance/lower-bound interface is CLOSED. Reuse it rather than creating
another child with the same direction inheritance as a hypothesis or conclusion.
The theorem is about global COMPLETION distance, not original summand distance.
No new original-H upper bound, shortestness or Polynomial Hirsch counterexample.

## Written all-completion obstruction and remaining formal boundary

research/ZONOTOPE_COMPLETION_OBSTRUCTION.md proves in ordinary mathematics that
0<=x0<=1 and e*x_(i-1)<=x_i<=1-e*x_(i-1), with0<e<1/2, define a d-dimensional
polytope with exactly2d genuine facets, cube graph/diameter d, and2^d-1 distinct
unoriented edge directions. Thus EVERY compact-summand zonotope completion has
global diameter at least2^d-1. Unlike #317's canonical-cube example, choosing a
smaller zonotope completion cannot remove this deformed-cube obstruction.

The all-dimensional facet/edge-count/translation application is NOT a second
Lean theorem in the accepted packet. It is a written proof plus exact finite
checks. Preserve that qualification. Formalizing those concrete steps would make
the whole strategy obstruction kernel-certified. Do not call the generic packet
alone a formal original-facet exponential family theorem.

For the conjecture, a useful positive quantitative continuation must charge the
steps surviving contraction or use a different geometric class/argument. A bound
on every completion edge, even after changing the zonotope completion, cannot be
uniformly polynomial in original facets on the written family. This says nothing
against a short route in P itself; its graph is a cube. #318 separately restricts
best compatible lifts for a specified rich generator inventory; it does not
replace this arbitrary-completion inheritance result.

## Source identity, historical local preparation and reproducibility

Accepted source945lines/39901bytes, blob791a71ce939f7f6181dcd3a51681ef4f263a55b4,
SHA2568ffc6b7da55ed39449ee1a21f8a0bdb38c2b4d56b592c940ef52bc00ce0aae05.
The629-line #317 prefix and81-line #313 regularization section are byte-identical;
both old packets' five hashes were rechecked. Original local candidate source and
target type are unchanged. Metadata only refreshed old local-only status wording
before the first request; old files and handoff remain in the original local ZIP.
They are historical, not current submission status.

Three original request/verified/publication ZIPs and all five frozen files were
rehashed. Raw extracted evidence is committed. Full ZIPs, 9885-byte report and
303297-byte fixture accompany the export and regenerate. The repository includes
the exact293-line test script, compact summary and replay hashes, not the full
large fixture. Two current runs, one in a clean script-only workspace, reproduce
the earlier outputs exactly. Historical test scope still says uncompiled to keep
those bytes stable; actual current formal status is this receipt.

Tests:18 small H models/3822 square systems/378 vertices/963 edge occurrences;
46422 support comparisons;4092 distances;28 exact whole planar completions;
64 selected d8/16/32/64 edges without complete high-dimensional enumeration;
82 saved-edge audits and28 saved-completion audits with producers disabled;
seven forgery controls. Tests do not certify a Python/JSON parser or replace Lean.

    python3 scripts/test_completion_direction_obstruction.py --out /tmp/completion-directions

Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.6,
workflows, allowlist, duplicate safeguards and verify/publish secret isolation
remain unchanged. Root STATUS and all pre-existing main files are untouched.
Use live PR metadata for the later evidence/merge commits.
