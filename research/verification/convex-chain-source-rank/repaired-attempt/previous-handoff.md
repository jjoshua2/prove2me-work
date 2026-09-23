# PR #338: strict convex-chain rank — first gate failed at two comparison tokens

Read the five repository instructions and LIVE main/queue/comments before action.
This is the strict-chain exact-rank obligation; do not duplicate the separate
changing-numerator claim5786607495 or touch #326/#282/reserved #210.

Repository jjoshua2/prove2me-work; PR338 OPEN/DRAFT and unmerged.
Branch proof/convex-chain-source-rank.
Target Hirsch.strict_convex_chain_exact_source_rank.
Packet research/publication_packets/convex_chain_source_rank.
Frozen tested proof e7e191e7d8557d54f2cd296d43308b2d80ff794b on main
6ee1612a05cede29039c4728825b7d5d255f14a8.
Source351 lines/15116 bytes, blobf38406afe0468a91aac1efd1b7a847e67db05176,
SHA256153682c72d5f9627f7155bb712e61db22fbaa11a2e9cd7d9502bd1c7dc4e7e02.
Later evidence commits do not replace this exact tested proof identity.

Request5798271256; acknowledgement5798274474; run35886406394.
Gate107267547134 success; verify107267624342 failure, driver exit1.
Separate solution/statement not reached; publish107268320514 and report-verify
107268321204 skipped. One hosted attempt, zero registrations/submissions.
No IDs, receipt, ACCEPTED or Proved. No second trigger or post-gate proof edit.

## Exact next patch

At source lines104 and162, change only k<i to k < i. Both actual diagnostics
parse the unspaced form as PrincipalSeg. Nine displayed errors include the
associated type/unsolved-goal cascades. The three named reports tilt_chain,
extreme_tilts and reciprocal_card are standard-only; rank_lower_bound,
exact_rank and solution still depend on failed-elaboration sorryAx.

Exact patch: research/verification/convex-chain-source-rank/first-attempt/
proposed-spacing-repair.patch. It is UNAPPLIED and UNCOMPILED. Proposed full
source351 lines/15120 bytes, computed blob668d5a54143923d16c293393c6affb3ab2759d16,
SHA256dc2a830c3da548edd4d1949235fbb5c0eb4f4178e9a5665b5744b74fe5048afe.
Roundtrip applies/reverses exactly; all other proof bytes, public type and
metadata are unchanged. Further errors may appear. Recheck live pending/ownership,
apply the saved patch, compile locally if available, then one complete prepared
gate on THIS PR. Do not weaken a hypothesis or resubmit accepted dependencies.

## Result being completed

For n+1 ordered abscissas and strictly convex ordinates, minimum distinct values
of a_i+t*w_i above source k is EXACTLY min(k,n-k). The proof derives a single
M>0 with extreme counts k and n-k at -M/+M for every k, then a positive shift
and reciprocal source rank min(k,n-k)+1 (including target zero). Two tilts replace
all-real search. The lower bound comes from an injective complete side forced
by secant convexity, not a supplied rank condition. Strictness matters; constant
ordinates defeat the claim if it is weakened. Signed a and singleton/endpoints
are included.

The original-polygon chart, extremality-to-convexity argument, supporting-edge
construction and half-facet interpretation are complete WRITTEN mathematics in
explanation.md, not separately formalized by this sequence theorem. No uniform
arbitrary-dimensional bound or new historical polygon theorem is asserted.
After completing this packet, the conjecture-facing problem remains higher-
dimensional structural control of the original-input rank, not more planar
search lemmas or an assumed favorable chart.

## Reproduction and artifacts

    python3 scripts/test_convex_chain_closed_rank.py --out /tmp/chain-small
    python3 scripts/test_convex_chain_closed_rank.py --random 20 --out /tmp/chain-random
    python3 scripts/test_convex_chain_closed_rank.py --large --out /tmp/chain-large

New scripts: convex_chain_closed_rank.py, test_convex_chain_closed_rank.py.
Dependencies are unchanged inverse_rank_planar.py and test_inverse_rank_reduction.py
from #337. No previously blocked code is used.24 completed configurations check
2030 routes/11464 edge occurrences; the64-vertex/eight-target NEW-method scope
is complete with512 routes/8192 edges. Old-method timeout status is unchanged.
All six outputs repeat byte-for-byte in a clean four-script workspace. Ten
malformed/premise controls fail. The exploratory3934 states are not included in
regression totals. Python/JSON and offline hash checks are not Lean proofs.

Only request archive10762459258 was produced and rehashed. Raw ZIP and full
fixtures accompany the export; exact resolved request, complete displayed errors,
all six reports and selected runner lines are committed. Extracts are not a full
raw runner log. Local Lean/cache unavailable, toolchain-host DNS failed. Retain
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
accepted bytes, allowlists, duplicate guards and verifier/publisher isolation.
