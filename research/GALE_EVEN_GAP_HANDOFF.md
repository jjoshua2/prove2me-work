# PR #307: selected-set Gale-even route — ACCEPTED

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
heads/comments before continuing. Starting main was
fcb4dae2a66cd420a181c5412e369ec4b0f744b8. This resumes the existing #307, not a
new theorem or duplicate PR. #300/#302 and reserved #210 remain untouched.

## Current authoritative packet state

`Hirsch.gale_even_gap_exchange_routes` is ACCEPTED; the trusted publisher records
live Proved. Theorem `1c79c95a-8107-4b7d-a81d-c1d120448924`, submission
`e6fb5adf-6d0f-468f-aa35-1409f6fdb263`. Accepted proof
`51c9e816f184dfda03b5373eaf91a69c06223b82`, run `35406946336`.
Actual new top-level trigger `5737529297`; resolved acknowledgement `5737530443`;
authenticated verdict `5737555526`. All were read back. Do not resubmit.

All three compile modes exited zero; all five transitive proof reports contain
only propext, Classical.choice and Quot.sound. Gate, verify and publish completed
successfully; report-verify was skipped. Read packet accepted-evidence.md,
publication-receipt.json, packet-audit.json and the separately labelled
verification/gale-even-gap/accepted-run-readback.json. The live Proved report is
the publisher's authenticated readback, not a fresh direct platform or root/leaf
poll. Local Lean/Lake was unavailable; successful compilation is the pinned
hosted evidence.

## Saved repair now verified, prior failures still preserved

The first run 35402347556 failed at enumerate_complement's final image equality.
It created no platform registration/submission. Its source, request and exact
selected diagnostic excerpt remain unchanged. The saved proposal appended rfl
after image_image. That exact 689-line proposal is now committed and accepted:
blob 9663ee6447a1d100923ba1c4b360fbbd0aaae9f3,
SHA256 5443bdf2da19e0d0ebbd69686e5488abbfb98fd20e01467b37de9ac50c1afd28.
Every public/helper statement, mathematical assumption, bound, public assembly,
accepted dependency body and target metadata stayed unchanged.

An intervening continuation's commit action was blocked, leaving only a local
repair and stored Git blob/tree. It launched no new gate. This continuation used
the normal create_commit and non-force update_ref successfully, then ONE new
publication comment. This is the SECOND compiler gate and FIRST actual platform
submission, not first-gate success. No post-success proof edits or further
triggers. Old failure readbacks and the separately preserved previous handoff
are history, superseded by the raw accepted receipt rather than silently erased.

## Closed mathematical interface

Inputs are actual selected finite sets S,T of cardinality d in Fin m, satisfying
literal Gale evenness: every pair of unselected labels has an even number of
selected labels strictly between it. The conclusion constructs a walk of length
at most 2*(m-d)+1 with distinct consecutive sets differing in exactly one label;
each intermediate set still has size d and the SAME predicate.

No complement enumeration, parity phase, graph, or bounded path is a premise.
Mathlib orderEmbOfFin enumerates the actual complement. If h_i is its i-th label
and C_i counts selected labels below it, the exact partition gives C_i+i=h_i.
The difference C_j-C_i is the selected gap count. This proves even gaps iff
indexed alternating parity in BOTH directions, including empty complements.
Reuse accepted #306's packing walk, then decode every step with exact image,
intersection and cardinality identities, never modulo-wrapping natural labels.

The entire accepted #306 proof is reused except its standalone root alias and
omitted old printouts; all five old manifest hashes were rechecked this turn.
Its theorem is not republished. Empty/full universes, d=0, d=m and equal endpoints
are covered. Repeated vertices and target-label loss are permitted; no shortest,
nonrevisiting, target-locking or monotone-score conclusion is made.

## Remaining conjecture-facing composition

The finite-set/enumeration/phase obligation is CLOSED. Do not create another
child merely assuming this route, enumeration or phase. #302 separately owns
the parity-to-numeric catalogue proof; at this live inspection it remained an
unaccepted draft and was not imported or edited. Once its exact equivalence is
verified, combine actual extreme-point reconstruction, this selected-set walk,
and accepted original common-row exposed-edge geometry. Prove all visited
points are actual vertices and all consecutive segments original edges, keeping
both normalization signs and every endpoint. That would yield the moment-class
2*(m-d)+1 route; it is NOT already established by this ORDER-ONLY packet.

Even that composed moment theorem would not settle arbitrary-carrier Polynomial
Hirsch. The unrestricted task still needs a uniform original-edge argument beyond
this special parity structure. No new best classical diameter bound is claimed.

## Durable evidence and supporting regression

All four original request/verification/publication ZIP hashes and all five frozen
packet file hashes were recomputed. Raw compile logs/audit/manifest and publication
receipt are separated from derived summaries. The export contains full fixtures
and original ZIPs; missing individual authenticated API responses are not invented.

The unchanged regression ran again: 2,047 subsets (596 legal), 13,724 endpoint
walks, 77,806 exchanges, 91,530 visited sets, 9,217 rank identities and 18,943 gap
identities. The complete report and fixture match prior bytes exactly:
report 84847b48a26a583b349f136e2900386cef69c791e8830d0aafb64f4383863cf1;
fixture 941975b53160bdbeaedfab25cd9577949b8e48dabf35a8776636d4d0cd2f4aeb.
3,651 repeated-vertex walks and 11,264 target-label-loss walks are retained.
Three selected larger cases, 69 saved audits and seven malformed controls are
supporting tests, not additional Lean theorems or verified Python/JSON.

    python3 scripts/test_gale_even_gap_routes.py --out /tmp/gale-gap-check

The current packet uses Lean4.30.0 / Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f. Root STATUS and all pre-existing main
files, strict0.10.5 version guard, workflows, allowlist, duplicate safeguards and
trusted verify/publish credential separation are unchanged. Consult live PR
metadata for final evidence/merge SHA rather than mistaking the frozen proof
SHA for the later evidence commit.
