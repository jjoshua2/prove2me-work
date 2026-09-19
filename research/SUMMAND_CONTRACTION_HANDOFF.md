# PR #309: generic summand-route contraction — compiler repair required

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and current open
heads/comments before continuing. Baseline main38475846e6cb588434893f912821617892306b29
already contains accepted #308. Do not resubmit #308 or change reserved #210.
This is the reverse of #244's owned forward fibre lifting; its core-route
assembly and all #300/#302 work were untouched. Coordination on #308 was
comment5738035171, before this packet was written.

## Exact current state

Target: Hirsch.minkowski_summand_exposed_route_contraction.
Packet: research/publication_packets/minkowski_summand_route_contraction.
Actual new top-level publish comment5738089713 was posted and read back.
Acknowledgement5738091246 resolved proof90a8789546920b5d55387739cb7e735cc8d2c64a
and run35411458055. Gate105811756327 succeeded; verify105811784206 failed;
publish105811927334 and report-verify105811929086 were skipped. The run is
completed/failure. There is NO theorem/submission ID, ACCEPTED verdict, live
Proved readback, verified-packet artifact or publication receipt.

One complete gate was triggered. The public source remains the unchanged
376-line prepared file, blobdc0e8cb6e5c7c4dcb829c56c79b418f48ca570f5,
SHA2565d753c0a11be9b147995a453601c303ae2c2c9b97b52ecaf32397518c81dc2b4.
The two metadata files are unchanged. Local Lean/Lake was absent and compiler
host DNS failed. Finite tests are NOT Lean compilation.

## Two actual diagnostic sites and the saved proposal

At line83 in segment_parameter, module normalization left the scalar equality
s=1-t. The existing hypothesis s+t=1 was not rewritten into that expression.
The proposal derives s=1-t with linarith and rewrites it before module.
At line197 in left_face_of_sum_edge, ha has type alpha=0 -> False, and ha.symm
was not accepted as field notation. The proposal uses explicit Ne.symm ha.

The exact proposed-local-repair.patch changes those two sites only; it has NOT
been applied to the submitted solution or compiled. It applies and reverses
byte-for-byte in a clean Git workspace. Proposed377-line source SHA256:
aa484136eb3bc13a03538f72a7cc8d1c188017cacfc1deb4990056cb5539f367.
All existing signatures, original assumptions, public statement AND root body
remain unchanged. Completing these repairs could expose further errors; do not
claim the entire candidate is verified because only two sites were reported.

vertex_decomposition emitted only propext, Classical.choice and Quot.sound.
The other four final reports contain sorryAx from failed elaboration. That is
failure evidence, NOT a passed packet audit. No second trigger was posted.
The raw resolved request and original315-byte request ZIP (artifact10574717840)
were downloaded; SHA25639d672c346c0e7a3906c89e6b5c8ca5e61ff80028dc337dc8948e122a5395067
matches. Full runner logs were read; the preserved text is the complete compiler
error/axiom block, explicitly not the runner setup/cleanup log.

## Mathematical interface

For arbitrary convex P,Q in R^d and an actual finite exposed-edge vertex walk
of their Minkowski sum, derive unique extreme summand decompositions. Each
component of a whole exposed sum segment is a whole exposed factor segment
or singleton, with nonnegative cooriented displacement fractions alpha,1-alpha.
Delete stationary component steps to construct a genuine original exposed and
extreme-edge walk in EACH factor, each of length at most the input N.
The two factor lengths are bounded individually; their SUM need not be <=N
because both factors may move at one sum edge.

Uniqueness comes from cross-sum midpoints. Component extrema follow by translation
of any convex decomposition. To prove the whole component face, put D=z1-z0;
the cross-sum p1+q0 supplies p1-p0=alpha D. For any component maximizer x,
x+q0=z0+sD and x+q1=z0+tD imply t=s+1-alpha. Since both belong to the full
sum segment, 0<=s<=alpha. This proves exact face containment, including alpha0;
convexity gives the converse. The same exposing objective works on both factors.
No vertex map, support-face/rank oracle or component adjacency is an input.
The32-line accepted #306 compression proof is copied verbatim in this namespace;
its old target is not resubmitted.

A finite ACTUAL sum walk and genuine convex Minkowski structure ARE hypotheses.
The theorem does not derive a short sum walk for arbitrary carriers, a small
sum presentation, or lifts of every independently selected factor endpoint.
Those are separate future applicability obligations. Arbitrary linear projection
is not an allowed substitute: a tetrahedron edge can project to a square diagonal.
There is no new universal polynomial bound, no claim of shortest factor paths,
and no historical novelty claim. Classical polytope contraction is credited to
Deza–Pournin, arXiv1806.07643, Can.Math.Bull.62(4),2019.

## Exact regression and reproducibility

Standalone Fraction-only script test_summand_contraction.py checks56 finite
sum models,519 sum vertices,518 cyclic/directed edge records and10,270
endpoint/orientation walks. There are47,122 sum-edge occurrences,24,894 left
and23,454 right factor edges.21 edge records move both factors;55 explicit
backtracking controls retain repeated vertices.5,294 factor support comparisons
check complete exposed faces against the listed finite generating sets.
Twelve product-box/segment cases reach dimension64 without full graph enumeration.
Eighteen saved records audit with construction disabled; five forgeries fail.

The script is not Lean-extracted or a verified parser. The exact22,324-byte
report and13,455-byte fixture reproduce byte-for-byte in a clean one-script
workspace. Their complete bytes and original ZIP are in the export; a labelled
summary and replay hashes are committed. Test source blobf952d8b5fa94ef4ce517f93f2b16ef720116578c,
SHA2563d4fada8d802541e5ff1984c364faa6b59f5ed26f59476dedc804938d80f787c.

    python3 scripts/test_summand_contraction.py --out /tmp/summand-contraction

The next immediate obligation is pinned local compilation of the two-site
proposal and a full transitive audit, then a fresh duplicate check before the
existing comment gate. No speculative Actions edit loop, assumption weakening,
workflow/pin/strict0.10.5-guard/allowlist/credential change is authorized by this
handoff. Existing main files and other owned branches remain unchanged.
