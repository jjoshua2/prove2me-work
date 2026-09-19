# PR #311: pair-segment completion — two helper proofs remain

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments/receipts before work. This continuation resumed the existing
#311 at main24b519ae1e7907a0d063cd36731d435da9918765. No duplicate PR or theorem
was created. Other owned #244/#300/#302 and reserved #210 remain untouched.
Accepted #309/#310 were not resubmitted.

## Current authoritative state: OPEN/DRAFT, no platform verdict

Target: Hirsch.finite_hull_pair_segment_completion.
Packet: research/publication_packets/pair_segment_completion.
Branch: proof/pair-segment-completion.
Latest tested proof: c1e5b8fe9517dd4a0284480c40598438ef860d9f.
NEW top-level publication comment5739380499 was posted and read back. Bot
5739381485 resolved that exact proof and run35421714330. Gate105840524620
succeeded; verify105840548099 failed driver compilation with exit1;
publish105840656050 and report-verify105840656023 were skipped. All jobs are
completed. There is no complete passing packet audit, verified-packet artifact,
platform registration/submission ID, ACCEPTED verdict or live Proved result.

The requested compact_zonotope report now contains only propext,
Classical.choice and Quot.sound. The other FOUR requested reports
(translate_hull, support_witness, completion, solution) contain sorryAx from
failed elaboration. One standard-only helper is not a passing complete packet
or a separate platform acceptance. The full runner log was inspected; committed
resume-diagnostics-excerpt.log contains explicitly selected exact lines only.

Exactly ONE new hosted attempt occurred this continuation, TWO overall.
No third trigger and no post-failure publication-source or metadata edits.
Local Lean/Lake was absent and the compiler host did not resolve. Source matching,
patch replay and rational regression are not Lean compilation.

## Saved scope/API repair was actually applied and tested

The previous 274-line proposal is now on the PR exactly:
solution blob9790db8a54ee6640c4e5d902c53b6b03e187d3d7,
SHA25647ac25515cdbff7270a285f9906399aca4aa63750d3de7315764c6887d454a8a;
problem blob31b3c124c57068b5300f31dacbc37a04d147fa96,
SHA256bf6d1ca55dbb24d725299e9ed390d9659a8ed22e6abf921259733e1c9bc88e42.
The repaired source is11294bytes and the problem2901bytes. Directory readback
confirmed exact blobs. The commit comparison changed these TWO packet files
only: full sum grouping, pinned update_self/update_of_ne names, and one explicit
translate-membership reduction. The explanation stayed byte-identical.

The old formal_statement was malformed and had never been registered. Its
parentheses necessarily changed BYTES; do not claim an unchanged previously
elaborated target. The intended mathematical formula, all hypotheses, name and
n^2 segment-slot count were preserved. The new gate no longer reports the
unknown-e, unknown-update-name or translate-membership errors, but this does
not imply an independent passing audit of every other helper.

First run35420782170, original source/target, request and diagnostics remain
preserved as a failed attempt. The previous handoff is copied byte-identically
to handoff-before-resume.md. Old proposed-local-repair.patch and its readback
are historical: that proposal HAS now been applied and tested. Use the NEW
proposed-two-helper-repair.patch for the outstanding candidate repair.

## Two remaining diagnostic sites and separate uncompiled proposal

At line54 in point_combo, the final simplifier leaves the distributivity of
scalar multiplication over finite vector sums unresolved. The pinned lemma
Finset.smul_sum exists in Mathlib/Algebra/BigOperators/GroupWithZero/Action.lean,
blob0d0fb1428930a156a680faba5b2772288c79f7cf at the committed Mathlib revision.
The proposal explicitly instantiates that lemma twice and combines the two
equalities after sum_add_distrib, instead of relying on broad simplification.

At line130 in replace_endpoint, the algebra tactic fails after simplifying
the changed-pair case, reporting a coefficient goal1=0. The proposal explicitly
exposes the pair projections and the updated coefficient before rewrites, then
uses abelian-group normalization for v_i=v_k+(v_i-v_k). This is an unverified
repair proposal, not evidence that the compiler accepted that diagnosis.

The proposal changes only those two HELPER PROOF BODIES, not their statements,
the corrected public statement AND its assembly, problem.json or explanation.
It is UNAPPLIED to the publication source and UNCOMPILED. Forward/reverse patch
application in a separate Git workspace reproduces both versions byte-for-byte.
Proposed283-line/11766-byte source:
blob756319de8d9d6d2d00941f48a87ff9c572ce35e6,
SHA256ac3bddf6ecc4dd20b3360e75d759013620bee82593065481205e7fe966a85bb5.
The full proposed file accompanies the bundle; the repository stores its patch
and labelled readback. Further errors may remain. The next required action is
full pinned verification of this existing obligation, not a duplicate child
assuming the completion or another speculative hosted edit loop.

## Mathematical scope and remaining conjecture boundary

For arbitrary n>0 real generators v_i in R^d, put P=conv{v_i},
Z=sum_(i,j)[v_i,v_j], and Q={q:q+v_i in Z for every i}. The target proves
compactness/convexity of Z,Q, nonemptiness of Q and WHOLE-SET equality P+Q=Z.
No completion, support equality, independence, full dimension or generic
objective is supplied. Repeated/interior generators, n1 and d0 are retained.

For each linear objective choose a maximizing generator k. Select v_k on every
ordered slot(k,i) and a maximizing endpoint elsewhere. Their sum z maximizes
the objective on Z. Changing slot(k,i) yields z-v_k+v_i in Z for EVERY i, so
q=z-v_k belongs to the actual erosion. Convexity gives all generator/hull
translations; strict separation with the support witnesses yields the reverse
inclusion. This remains the written argument; the complete Lean theorem is not
yet verified. Compactness of the coefficient image is the requested helper that
now has a standard-only report.

The explicit n^2 inventory counts represented ordered segment slots in INPUT
GENERATORS, including diagonals and repetitions. It is not an irredundant facet
count or a minimal completion budget. A large complete vertex inventory of an
H-polytope does not give a polynomial bound in its original rows. No short
actual Z-edge route is proved by this packet; coefficient-cube edges are not
assumed to project to ordinary original edges. Accepted #309/#310 remain
available for contraction and endpoint lifts once actual compatible sum routes
are established. A useful original-row budget and that routing step remain
separate, and unrestricted Polynomial Hirsch is not concluded.

## Current evidence and reproducible supporting checks

Both original request archives were downloaded and their hashes recomputed:
first10577217846,308bytes,
bdf820108f50381bd83c34d31b236c5fb4854afa994d7bbeb9e69ce60dbbbec6;
new10577848461,309bytes,
37a3630a0ecb8adaed366b0bf23354fc9ee22af877aba0dd6ca90cd6b2500c9e.
The raw new resume-resolved.json is retained. The second run's artifact listing
contains only the request, not a fabricated verified or publication archive.
Tested source/target snapshots, old handoff, selected exact diagnostics and
derived run/proposal records are separated by name and purpose.

The unchanged Fraction-only regression ran again and repeated in a clean
script-only workspace:46 whole-body planar models,1208 support witnesses,
6627 replacements,42189 coefficient bounds,9 selected instances through d64,
19 discovery-disabled saved audits and4 rejected forgeries. Complete report
and fixture match both the prior and the two current executions byte-for-byte:
report12437bytes,978578e2dd9cc9edee710aecd9a9ec86babc7661f5ed2ac995bde887670bdd5b;
fixture33706bytes,efc7e10a8b59cd961323e85556ac6f5919c001d0c2f2d8c3a4f26ea2343ce625.
They are supporting finite checks, not Lean-extracted code or a universal JSON
correctness theorem. Full outputs, original archives and proposal are bundled.

    python3 scripts/test_pair_segment_completion.py --out /tmp/pair-completion

No pre-existing main file, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5 guard, workflow, allowlist,
duplicate control or trusted verify/publish credential split changed. Consult
live PR metadata for the evidence head, distinct from the frozen tested proof.
