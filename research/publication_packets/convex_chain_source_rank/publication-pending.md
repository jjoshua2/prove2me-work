# Complete Lean proof; existing registration job is pending

PR #338 remains OPEN/DRAFT and unmerged. The saved spacing repair passed the
complete pinned compiler and axiom gate. This is not a Prove2Me acceptance.

## Exact result and identity

Target: Hirsch.strict_convex_chain_exact_source_rank.
Verified proof: de2e0175d0db46ecc13ccbe6c003efd535da6417.
Source: 351 lines / 15120 bytes, blob 668d5a54143923d16c293393c6affb3ab2759d16,
SHA256 dc2a830c3da548edd4d1949235fbb5c0eb4f4178e9a5665b5744b74fe5048afe.
Main at the gate: 6ee1612a05cede29039c4728825b7d5d255f14a8.

The exact saved repair adds four spaces in two local annotations, changing k<i
to k < i. Every other proof byte, declaration signature, public hypothesis,
problem.json and explanation.md remains unchanged. No proof or metadata was
edited after the successful gate. The original failed source and all nine
displayed diagnostics from run 35886406394 remain preserved.

New top-level request 5799614897 and acknowledgement 5799618152 resolved run
35895877060 to this proof. Driver, standalone solution and exact target statement
all exited zero. All SIX named reports in BOTH complete proof logs use only
propext, Classical.choice and Quot.sound, including public solution. No sorryAx
remains. The statement-only placeholder is not proof evidence.

The trusted publisher then returned PUBLISH_PENDING / registration QUEUED:

    publish job cfbe3736-58f8-4c07-9de0-63147127b046

The unchanged raw receipt and bot comment 5799811983 at 2026-09-23T17:38:33Z
record that existing job. No completed registration, theorem ID, proof submission,
submission ID, ACCEPTED verdict or authenticated Proved status was returned.
The publisher job exited successfully because it preserves resumable pending
registrations; a green workflow is NOT acceptance. There were two compiler
attempts overall, one registration request in this run and zero proof submissions.

## Next action: resume, do not re-register or repair

After fresh live ownership/comments/receipt checks, resume this SAME packet on
this SAME PR through the unchanged trusted comment publisher. Its exact-job
recovery guard finds the existing registration instead of creating a duplicate.
Do not rename the target, modify its statement, call submit-problem separately,
or reapply the spacing patch. Keep the verified inputs frozen. No additional
trigger was posted after the pending outcome in this continuation.

## Mathematical scope now supported by complete Lean verification

For n+1 ordered real abscissas w_i and strict triple-secant convexity of a_i,
the theorem computes the all-real distinct upper-height minimum min(k,n-k).
One derived M>0 gives counts k and n-k at -M and +M simultaneously for every
source. Positive translation, reciprocation and target-zero accounting give
exact rank min(k,n-k)+1 and twice-rank <= n+2. The lower bound and favorable
tilts are outputs, not hypotheses. Strictness and ordering remain essential;
signed ordinates, singleton/two-point chains, endpoints and cross-side ties remain.

The polygon-to-chart construction, original-edge/facet interpretation and Python
implementation are written/tested consequences, not additional Lean conclusions
of this finite-chain packet. No uniform high-dimensional original-edge bound,
changing-numerator result or new historical polygon-diameter theorem is claimed.

## Preserved evidence and fresh execution

All twelve raw verified files, both publisher files and the exact request are
preserved under repaired-attempt/. Complete compiler logs are unchanged. The
three original Actions archives were downloaded and rehashed; all fifteen
extracted members match. The raw packet, verified and receipt Git trees match
independent local hashing. Both full decoded runner logs were read through
cleanup; stored excerpts are selected, not complete raw archives. Missing
individual platform API response bodies are not reconstructed.

The unchanged small, 20-seed irregular and 64-vertex/eight-target suites reran.
All six complete outputs match prior bytes: 2030 planar routes, 11464 original-
edge occurrences, 1840 unique transitions and ten rejected malformed/premise
controls. The large scope remains a planar 64-vertex polygon, not dimension64.
Python, JSON and the written geometric bridge are not kernel-verified.

The export-only inspector passes 105 content-consistency checks and eight
corrupted-copy controls before manifest checks. This checks stored evidence;
it neither executes Lean nor authenticates arbitrary JSON. Local Lean/Lake/Elan
and checked caches were absent; toolchain-host DNS failed. Actual compilation
is the hosted Lean 4.30.0 / Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f gate.
Strict protocol 0.10.8, duplicate guards and verifier/publisher isolation remain.
Handoff: research/CONVEX_CHAIN_SOURCE_RANK_HANDOFF.md. Other owners are untouched.
