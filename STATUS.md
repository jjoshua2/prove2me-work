# Current Polynomial Hirsch frontier

Repository `jjoshua2/prove2me-work`. Keep Lean `v4.30.0` and Mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Read AGENTS.md, CLOUD_AGENT.md,
SKILL.md, CONTINUE_HIRSCH.md, actual main and LIVE PR heads/comments before work.
Do not duplicate accepted or pending submissions.

This update records NEW FORMAL ACCEPTANCE #288. The preceding COMPLETE frontier
is preserved verbatim in immutable history:
[pre-#288 STATUS](https://github.com/jjoshua2/prove2me-work/blob/dfa4c0b4834fd302818646f56a0801fbbf54be75/STATUS.md),
blob `b737c70959d97201626e37d7d80a6fe38b5fbff5`. It retains the complete #286/#285
history, #284/#281, older proofs, research limitations, receipts and ownership.
Check live commits as well as this index; other work can precede status updates.

## Root and scope

The last preserved authenticated mission audit records root
`58eae2c9-6fd5-4d5d-8aa7-6d552ad80bac` and high-dimensional common-face leaf
`87a8b4f4-8b58-4340-8cb9-5fd1b548d01e` Open. This is NOT a fresh platform poll.
The goal remains a uniform polynomial ORIGINAL ordinary-edge upper bound for
arbitrary carriers. Count original image facets, not smaller extension rows.
A formally accepted incompatibility theorem is not that universal route result.

## NEW #288: ordered signs and minimal moment-row sets ACCEPTED and merged

Theorem: `Hirsch.moment_curve_ordered_minimal_nonfaces`.
Theorem ID: `07cdedd0-db22-48e8-897e-d9d3ab04bcf1`.
Submission ID: `83b6f1bb-cd20-431f-92ff-6f1eb201a917`.
Trusted publisher: **ACCEPTED**, authenticated readback **Proved**.
Accepted proof: `56f1b0b4e83300b55a055a798a7f0be1d0f47400`.
Evidence-only head: `84ef46e564337de4474fd4a3c3605b8e32a5a3c5`.
Merge: `dfa4c0b4834fd302818646f56a0801fbbf54be75`.
Run: `35176922050`; verdict time: `2026-09-17T03:09:39Z`
(September 16 at 23:09:39 America/New_York).

[Accepted proof, scope and next interface](research/publication_packets/moment_ordered_minimal_nonfaces/accepted-evidence.md),
[raw publisher receipt](research/publication_packets/moment_ordered_minimal_nonfaces/publication-receipt.json),
[raw compile/axiom audit](research/publication_packets/moment_ordered_minimal_nonfaces/packet-audit.json).
The exact proof, target, explanation, verified manifest, full driver log,
artifact readback, rational test and clean replay are on main. Historical
PREPARED metadata is superseded by acceptance. Do not resubmit this packet.

### Exact formal content

For any injective real parameter map a on m original labels, any k, and any
embedded chain b of 2k+3 strictly increasing PARAMETER values, let N be its
k+1 odd-ranked labels. With the original dimension-2k mean-centered moment rows,
averaged over ALL m labels, the theorem proves:

    |N| = k+1;
    no feasible x makes all rows of N tight;
    every proper T subset N has a feasible x making EXACTLY T tight.

The proof derives the ordered barycentric signs, not a supplied sign oracle.
For rank i the denominator has 2k+2-i negative upper factors, so its weight is
negative exactly at odd ranks. The accepted nonzero slack-polynomial theorem
then supplies a strictly slack odd row at every feasible point. Injectivity
gives |N|=k+1; proper subsets have size at most k and therefore receive the
accepted squared-root-polynomial witnesses. No dependence, rank, feasibility,
incompatibility, minimality or counting oracle is assumed.

Original labels may be scrambled; only their selected parameter values are
ordered. k=0 and empty proper subsets are covered. This is literally an original-
row statement, not an assertion that every boundary case has genuine polytope
facets. Geometric realization hypotheses must still be supplied where needed.

The complete namespace proof bodies of ACCEPTED #285 and #286 are reused
BYTE-FOR-BYTE, excluding only their old public solution and print suffixes:
#285 blob `3506c3b28278e52412e7867b08f81c096b836334`;
#286 blob `6050e16e234b64011ea8bb8b643cc9461c327ce3`.
These are actual proofs, not newly assumed helper statements. Neither earlier
public target was registered or submitted again. Their statements stay unchanged.

### Actual first-attempt verification and comment publication

The 606-line prepared source passed its FIRST pinned compiler gate and FIRST
actual platform submission unchanged. Driver, solution and target all exit 0;
all FIVE transitive proof reports use only propext, Classical.choice and
Quot.sound. Harmless warnings in reused accepted bodies remain in the raw log;
no linter suppression or proof cleanup changed the frozen bytes. The source
contains no admission or target import.

Exactly ONE new top-level comment triggered publication on the open same-repo PR:

    /prove2me publish research/publication_packets/moment_ordered_minimal_nonfaces

Trigger `5707849370`; resolved-head bot `5707850635`; verdict `5707873841`.
No workflow_dispatch, workflow, token, permission, pin or secret-split change.
Local Lean/Lake was unavailable; formal verification is the pinned hosted run,
not a rational test described as compilation. Proved is the trusted publisher's
authenticated readback, not a separate direct platform query by the chat.

All three original request/verification/publication ZIPs were downloaded and
independently hashed. All five frozen file hashes match; source, metadata and
explanation match the prepared bytes exactly. Accepted source SHA256:
`0cb180af7915af3e9da23aee512e4f5930b389a876b4bb6e014c3e69ea467ae6`.
The aggregate publisher receipt and raw audit/log/manifest are preserved unchanged.
No absent individual API-response objects are invented. The evidence commit adds
NINE files and changes ZERO of the four submitted files; all 13 PR files are
additions, with no earlier selector or proof changed.

### Supporting tests and reproducibility

The rational regression covers 120 nonuniform/scrambled-label cases, 840 signs,
720 moment equations, 1,368 proper subsets, 17,256 original inequalities,
14,520 strict rows and 360 feasible-point checks. Larger samples in dimensions
16/32/64 cover all immediate proper subsets plus the empty set, not the entire
exponential catalogue. A separate exhaustive small application checks 76 odd
minimal sets and 1,992 proper-face witnesses. Eighteen consumer audits pass with
witness production disabled; nine malformed assumptions/certificates fail.

A clean directory containing only the standalone test and source/metadata inputs
reproduces the report and 557,163-byte fixture exactly. The 13-addition patch also
applies in an independent empty Git checkout, reconstructs every file byte-for-
byte, and reruns the full test with identical outputs. The detailed fixture and
original artifacts are bundled; tests regenerate them. Python/JSON are not
Lean-extracted or formally verified. These are supporting checks, not the basis
of the platform verdict.

    python3 scripts/test_ordered_moment_packet.py

## What to reuse and what is still missing

#285's exact small-face witnesses and #286's constructed barycentric nonfaces
are ACCEPTED. #288 now also closes ordered parity and PER-CHAIN minimality.
Do not restart these proof obligations from the old local-only bundle. #285's
separate integration remains its owner's task; it was not edited or merged here.

The next formal application on this line is to select separators for EVERY
(k+1)-subset of the odd integer labels, identify the resulting odd-rank image,
count the complete distinct family, and compose it with accepted #281. The
current theorem does NOT formally implement that catalogue construction or its
binomial cardinality, nor the remaining full geometric realization/asymptotics.
Numerical catalogue checks do not replace those proofs.

#281's finite stellar persistence count q+t<=choose(m+t,2) and #284's protected-
facet state counts remain accepted with their separate hypotheses and receipts.
#267's written obstruction concerns total COMPLETE forward flagification size,
not original diameter or paths inside a huge implicit refinement. Earlier
positive class refinements and accepted allocation/Minkowski interfaces remain
valid. No theorem here is a new universal original-edge upper bound.

The main conjecture still needs such an upper bound, perhaps through controlled
path-local signatures or another valid construction. Do not assume a small
exceptional parameter, cheap repair or universally small complete forward flag
refinement as an unproved premise. #268 budget search and #271 checked exclusions
retain their positive/negative evidence boundaries. #269/#272 and newer direct
route formalizations retain their own structural assumptions; inspect actual
live sources and receipts before selecting overlapping work.

## Ownership and execution discipline

#282 triangular original-edge work, #270's deliberately partial draft, #264
energy, #255 shortening, #250 projected-image integration, #244 fibre assembly
and #238 support witnesses remain separate. Do not bypass blocked companion
integration. #208 needs its existing approved poll rather than resubmission;
#210 is retired/reserved. No other agent's branch or pending/accepted proof was
modified or retriggered by #288. Read the live queue before acting on old numbers.

Distinguish written mathematics, exact software, Lean compilation, axiom audit,
ACCEPTED and authenticated Proved. Preserve pins and trusted publisher isolation.
Use local compilation where available; the final hosted gate is not a repeated
speculative proof-editing loop. Preserve raw evidence separately from summaries.
