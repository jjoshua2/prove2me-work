# PR #338: accepted exact convex-chain rank

Read the five project instructions and LIVE heads/comments before continuing.
The pending-registration blocker is resolved. Do not reapply the old spacing
repair, rename this theorem, re-register it or submit its proof again.

Repository jjoshua2/prove2me-work; PR338; branch proof/convex-chain-source-rank.
Packet research/publication_packets/convex_chain_source_rank.
Target Hirsch.strict_convex_chain_exact_source_rank.
Accepted submission commit223b5abfc8666393b2b60bec387f4e49d3f626b8.
Initial verified proofde2e0175d0db46ecc13ccbe6c003efd535da6417.
Both have identical proof/metadata bytes. Source351 lines/15120 bytes,
blob668d5a54143923d16c293393c6affb3ab2759d16, SHA256
 dc2a830c3da548edd4d1949235fbb5c0eb4f4178e9a5665b5744b74fe5048afe.

Theorem e5c0158b-f340-4262-865a-7f6936b83db1.
Submission a2f3ea44-ec31-41a9-a4da-d3929d79340c.
New request5801952351; acknowledgement5801955039; run35912718942;
accepted bot verdict5802016156 at2026-09-23T20:01:26Z.
Raw publisher receipt: ACCEPTED / registration REUSED / live_status Proved.
Proved is the trusted publisher's authenticated readback, not an independent poll.

Prior registration job cfbe3736-58f8-4c07-9de0-63147127b046 and its QUEUED receipt
remain historical evidence. The unchanged guarded publisher found the existing
exact theorem, avoiding a new registration. The run completed the first actual
proof submission. All three compile stages exit0 and all six reports in both
full proof logs are standard-only. Three hosted compiler runs overall, two
passing; no source or metadata change during the resume. No further publication.

Check live PR lifecycle before integration. If not already merged, complete only
normal eligible review and expected-head merge of this existing accepted PR.
Preserve other-owned #326/#282/reserved #210 and changing-numerator work.

## Scope and next mathematics

The finite-chain theorem proves exact all-real upper-height optimum min(k,n-k),
one source-independent pair of extreme tilts and reciprocal rank min(k,n-k)+1,
with twice-rank<=n+2. Ordered abscissas and strict secant convexity remain explicit.
The original-polygon chart and edge/facet arguments are written/tested, not new
Lean conclusions of this packet. The mission remains a uniform polynomial bound
on original ordinary-edge routes for arbitrary carriers. A new step should address
that actual geometric/rank gap without re-publishing this finite-chain result or
claiming that a polynomial vertex-inventory bound is a facet-parameter bound.

## Evidence and reproduction

packet/accepted-evidence.md and publication-receipt.json hold the current result.
publication-pending.md and first-gate-evidence.md are historical. All prior raw
records remain in their original verification directories. New exact verified,
receipt and request files, previous handoff and derived readback/replay checks
are in research/verification/convex-chain-source-rank/resumed-publication/.
Both complete decoded runner logs were read; stored runner excerpts are selected.
No missing individual platform API body was invented.

All six outputs of the unchanged four-script suite reproduced their prior bytes:
2030 planar routes/11464 original-edge occurrences and ten malformed/premise
controls. The64-vertex/eight-target scope completed. Python/JSON and the polygon
bridge are not kernel-verified. Reproduction:

    python3 scripts/test_convex_chain_closed_rank.py --out /tmp/chain-small
    python3 scripts/test_convex_chain_closed_rank.py --random 20 --out /tmp/chain-random
    python3 scripts/test_convex_chain_closed_rank.py --large --out /tmp/chain-large

Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
accepted proof bytes, actor allowlists, duplicate guards and secret separation.
