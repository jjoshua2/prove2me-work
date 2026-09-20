# PR #316: arbitrary zonotope endpoints — two-site compilation repair required

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live exact
PR heads/comments before continuing. This work started from main
c9a9a44a0d144efa66c07c2c26605adafd0c2dd3. The accepted #315 regular-objective
route was reused, not resubmitted. Reserved #210 and other owned work were not
modified or triggered. Coordination on #315 was comment5747567097.

## Current authoritative state

Target Hirsch.zonotope_all_endpoint_original_routes.
Packet research/publication_packets/zonotope_all_endpoint_routes.
PR #316 is OPEN/DRAFT, with no complete passing packet audit, theorem/submission
ID, ACCEPTED verdict or live Proved readback. Do not merge or resubmit an old
accepted target in its place.

The actual NEW top-level command5747621045 was read back. Acknowledgement
5747621792 resolved exact proofc0c2d6111ac1bad28f7a5cea60ad353fa1c8a26a and
run35489239756. Gate106021169315 succeeded; verify106021186209 failed exit1;
publish106021292098 and report-verify106021292014 were skipped. The run completed
with failure. Exactly ONE compiler/publication request was triggered. No second
request or publication-source change followed the failure.

The two helpers body_eq_corner_hull and corner_unique_objective printed only
propext, Classical.choice and Quot.sound. The regular-objective lemma, all-endpoint
assembly and public solution printed sorryAx from failed elaboration. These
reports are not passing complete verification or separate platform acceptances.

## Exact remaining errors and separate proposal

Line1160 in toggle_mem_corners: after simplification the right disjunct is True,
so Or.inr rfl supplies an equality proof where True is expected. Replace that
whole update-self branch with simp.

Line1241 in the public solution: intro introduced the local let-bound set Z as
hu, not the extremality proof. Add dsimp only before intro hu hv. The declaration
statement and all assumptions are unchanged; the root PROOF gains this reduction.
Do not inaccurately say the root proof body is byte-identical under this proposal.

The separate proposed-local-repair.patch is UNAPPLIED to publication source and
UNCOMPILED. It applies/reverses byte-exact. Proposed1247-line/54466-byte source:
blobc106008250409e7fc9eb3a3e8b187eb64d9f49e9,
SHA25680403727d5d0e7b3e11932dc937e76c3bdcd283c786a426bcfe44a7ea781aa87.
Further errors may appear after these corrections. No extra hosted gate was used.
Local Lean/Lake was not available and compiler-host DNS failed. Source checks and
Python regression are not Lean verification.

The tested source remains1247 lines/54504 bytes, blob
96e5c259bbab1fec733aa054f7cd1f90b1b1af30,
SHA256f74470f80704b84242a50dc983a4826f49a672870af4569b5a1dd9634df46405.
Both target metadata files remain unchanged. The entire1048-line accepted #315
namespace prefix is copied byte-for-byte; only its old public root/prints were
omitted. All five accepted dependency hashes were checked.

## Mathematical progress and exact hypotheses

For arbitrary real generators w_i, define their actual coefficient sum Z and
C as the finite images of ALL Boolean corners. C may include duplicate images
and nonvertices. The new hull lemma proves Z=convexHull(C), rather than assuming
a vertex catalogue. Since u is extreme in Z, deleting {u} leaves a convex set.
The hull of C minus {u} lies there and excludes u. It is closed because C is finite.
Strict separation therefore constructs f strictly larger at u than every other
corner image. These two substantive steps have standard-only helper reports.

The candidate then observes that the canonical saturated corner V(f) maximizes
f over the entire coefficient sum. Feasibility of u and strict corner separation
force V(f)=u. If nonzero w_i were tied, toggling its zero coefficient to one
would give a distinct corner V(f)+w_i at equal value, contradiction. Hence the
derived objective is regular and exposes the whole singleton {u}. Do this
independently for u,v and reuse accepted #315 to obtain L<=m genuine original
exposed/extreme edges joining the requested arbitrary endpoints.

The full candidate is NOT yet verified. It supplies no objective, regularity,
Boolean injectivity, vertex list, face/adjacency oracle or short route hypothesis.
Only actual endpoint extremality and the explicit segment-sum representation
are inputs. Zero/repeated/parallel/opposite and rank-deficient generators,
d=0,m=0 and equal endpoints remain covered in the statement.

The finite corner set is an existence-proof device, not polynomial-time
computation. m counts segment generators, NOT original H facets. Even after
this all-pairs packet passes, the general completion argument still needs a
controlled original-input generator budget or a different quantitative proof.
This is a classical zonotope bound, not historical novelty, shortestness or
unrestricted Polynomial Hirsch. Do not replace original complexity by an
exponentially expanded inventory.

## Preserved receipts and reproducible supporting tests

The complete compiler error/context/axiom block is committed as a scoped excerpt;
runner setup/cache/cleanup were inspected but are not claimed committed in full.
The original request ZIP10598607331 is314 bytes, SHA256
c0874d334ebad378428daeef4581c1574e0113e4979e8be2df91c302d016133e,
recomputed from downloaded bytes. Its raw resolved.json is preserved. No verified
packet or publisher receipt artifact exists for this failed run. Derived records
are labelled and do not fabricate a platform verdict.

The exact suite discovers84 planar vertices in18 complete small systems, checks
all502 endpoint pairs and874 original-edge occurrences against an independent
hull, and retains143 nonvertex corner images and138 duplicate Boolean images.
There are272 parallel-tie occurrences and84 zero-length walks. Support checks
include25860 endpoint comparisons,40046 chamber comparisons and2100 event-face
points. The planar tests happened to match shortest distances, but no formal
shortestness theorem is claimed.

Four zero-dimensional/zero-generator cases and four selected larger examples
in ambient dimensions8/16/32/64 (ranks8/16/6/6, lengths8/16/6/6) are separate
checks without large graph enumeration. Twenty-six saved records audit with
construction disabled; five forgeries and a nonvertex-corner control are retained.
Full report11723bytes SHA256
243bf692ad7ed0a4600d58e7895b1bfd11d6071f76924765641773da59bcd1dc;
fixture65977bytes SHA256
3c6be707b30cf0214b87d7096bf8abe05b206089b2f79d8de4641031b4ad34da.
Both reproduce byte-for-byte in a clean three-script workspace. The full files,
original request ZIP and accepted dependency bundle accompany the export;
repository summaries are explicitly labelled. The two existing test helpers
remain unchanged; the new script blob is2ed7f17d59c610ba335a8901ebc47fc4fe695c63.

    python3 scripts/test_zonotope_allpairs.py --out /tmp/zonotope-allpairs

Existing main files, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.6 guard, workflows,
allowlist, duplicate safeguards and verification/publication credential isolation
were untouched. Consult live PR metadata for the later evidence commit.
