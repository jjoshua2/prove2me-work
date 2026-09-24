# PR #326: affine-roof routes — second full gate has one reported error

## Current lifecycle and exact proof

Keep this existing PR OPEN/DRAFT. Do not merge as accepted, reapply the first
repair, or repeat either failed publication request. Read STATUS.md, AGENTS.md,
CLOUD_AGENT.md, SKILL.md, CONTINUE_HIRSCH.md and live heads/comments first.
#325 is already accepted and merged; its old pending summaries are historical.
#282 and reserved #210 remain untouched.

Repository: jjoshua2/prove2me-work.
PR/branch: #326, proof/independent-affine-roof-routes.
Target: Hirsch.independent_affine_roof_original_routes.
Packet: research/publication_packets/affine_roof_routes.
Current TESTED proof: 5d9c065f308255846337d810b27105128ddaa3cf.
Trusted main for this run: 7b1db85d8182cf43ddcf6eae30ca77442906e843.
Later evidence-only commits do not change that tested-source identity.

Coordination 5769871135 was posted/read back. Actual NEW top-level publication
request 5769934069 was posted 2026-09-22T01:27:54Z and read back. Acknowledgement
5769936477 resolved the exact proof to run 35675854643. Gate 106582120479 passed;
verify 106582157039 failed driver compilation, exit 1. Publish 106582388578 and
report-verify 106582388664 were skipped. Separate solution/statement compiles
were not reached. No complete passing audit, verified archive, theorem
registration, proof submission, theorem/submission ID, ACCEPTED or Proved result
was produced. No independent platform/root poll occurred.

## Progress relative to the first failed run

Applied EXACTLY the saved two-file proposal before this gate. It corrected
comparison parsing, three product-equality inference problems, finite-index
values and reserved local identifiers. Metadata changed comparison whitespace
only to match the public type; the accepted prefix and explanation are unchanged.
The intended mathematical hypotheses and conclusions are unchanged.

Tested solution: 1608 lines / 71702 bytes.
Blob: 4ecc055d476fa69133903c8eeef8347f04c5e1ca.
SHA256: a8bf4aa83140f687318dc3cc6f33a57752c4e612d791a9d480f7b1529b0aae75.
Problem blob: 97558d6d59e0797d3066ab16a516fcd71c576502.
Unchanged explanation blob: cc5b18cb13d1ed0c4057a65fd1dbfd0a33a59393.
The repaired files were read back by exact blobs. The full patch apply/reverse
and target-type checks passed locally; these were not Lean compilation.

The second compiler reports ONE error, at 1148 in extreme_classification.
Its nonzero-fiber branch has hj : z.2 j != 0 and he : z.2 j = H, but the broad
simp call rewrites the Boolean test too early and leaves:

    H = 0 -> 0 = H.

All earlier error groups are resolved in this run. The four new requested
reports for lift_extreme, vertical_edge, fiber_route and original_row_count
now contain only propext, Classical.choice and Quot.sound, as do all five
inherited finite reports. extreme_classification, roof_routes and solution
still report failed-elaboration sorryAx. No admission was written, but the
complete file remains FAILED. A clean helper report is not complete verification.

## Separate next repair: UNAPPLIED and UNCOMPILED

Use second-attempt/proposed-classification-repair.patch under the evidence path.
It changes only the positive/nonzero branch of extreme_classification. First
expose bit (if z.2 j = 0 then false else true) * H = z.2 j, select if_neg hj,
then use he.symm with only bit/if_true/one_mul simplification. This avoids changing
the test through a simultaneous rewrite. No new positivity or other premise is
added. All declaration signatures, the accepted prefix, complete public root
statement AND proof, metadata and explanation remain unchanged.

Proposed source: 1610 lines / 71815 bytes.
Proposed blob: 00c2e4433609aefa71e70659c82b479111fceea6.
Proposed SHA256: 2c155db2ecca71efbbd6c401d063e509deb2d5984b8dde15fa65824e5d432149.
Forward/reverse patch application reproduces the whole files exactly. This is
NOT applied to the publication source and NOT compiled. Further errors may
appear after it. No post-gate source/metadata edit or another trigger occurred.

## Mathematical scope remains the same

P is both a finite 0/1 hull in ambient R^n and its original m halfspaces. Add
k independent intervals 0<=y_j<=c_j+A_j x with strictly positive heights on P.
The written argument and candidate derive actual vertex classification, whole
original horizontal/vertical edges, a Hamming fiber leg of at most k steps,
and a lifted 0/1 base leg of at most n steps. The target asserts both L<=n+k
and L<=m+k, against m+2k displayed original inequalities, with k unrestricted.

No supplied labels/catalogue, graph, neighbor, basis, rank, base path or cheap
residual route is assumed. Nonsimple/lower-dimensional bases, redundant rows,
n0/k0 and equal endpoints remain. Exact base H/hull equality, 0/1 structure,
independent intervals and strict positivity remain structural hypotheses; they
are not proved for arbitrary carriers. No shortestness, all-facet nonrevisiting,
complete graph-isomorphism or efficient H-to-V assertion. This does not solve
uniform Polynomial Hirsch. Classical attribution is in the unchanged explanation.

## Durable evidence and freshly rerun computations

research/verification/affine-roof-routes/second-attempt/ preserves the complete
tested packet inputs, prior complete handoff, raw frozen request, single complete
error context, all twelve axiom reports, and labelled derived source/run/replay
records. The transcript omits timestamps, linter bodies and setup/cleanup; it is
NOT a raw full-runner archive. The complete decoded verifier log was read through
cleanup. No absent compiler artifact or platform API response is fabricated.

Only request artifact 10672499135 was produced: 308 bytes, SHA256
3698046a2594716d4410623a3474d2b107a0de85b61b964a61190eecf210fb7f.
Its ZIP was downloaded/rehashed and resolved.json is unchanged. The original
first failure 35673924236 and all its files remain preserved, including the
old saved patch (now applied). This is the SECOND hosted compile attempt and
ONE new trigger this continuation, not a speculative same-turn compiler loop.

The unchanged exact scripts ran again: 13 small models, 721 routes / 1224
original-edge occurrences versus 1168 shortest edges, with all 56 nonshortest
outputs retained. Four large cases certify another 120 original edges through
64 dimensions; nine malformed controls fail. All five full reports/fixtures
match the previous bytes. The first combined local command hit its 45-second
limit after the 32D large case; the unchanged large script subsequently completed
all cases. That timeout log remains in the export, not hidden as an initial pass.
No large graph or exponential level enumeration was performed; those counts
remain written-family formula evaluations, not extra Lean theorems.

The full fixtures and logs are included in the export and regenerate from the
two existing scripts and unchanged #322 reference. Python/JSON are not kernel-
verified. The successful local process has exited; no continuing background job
or future monitoring is promised.

## Exact next action

Resume THIS PR after live ownership/pending checks. Review/apply the single-site
classification patch, compile locally if a pinned environment is available,
then use a complete prepared gate. Do not weaken the target or restart the old
parsing patch. No Lean/Lake/cached toolchain was found in this runtime; DNS to
toolchain/raw GitHub failed. Preserve Lean4.30.0, Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f and strict0.10.7 publication. Do not alter
workflows, allowlists, duplicate guards or verifier/publisher credential separation.
