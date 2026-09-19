# PR #310: original-H summand endpoint lifts — final assembly repair required

Read live STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and actual open
heads/comments before continuing. This continuation began at main
c766c3f769b06912c481fd305d857e73d9546811 and did not resubmit accepted #309.
Branch: proof/polyhedral-summand-endpoint-lifts. Other owned #244/#300/#302
work and reserved #210 were not edited or triggered. Coordination on #309 was
comment5738489814, posted/read back before work.

## Current authoritative status

Target: Hirsch.polyhedral_summand_endpoint_lifts_and_routes.
Packet: research/publication_packets/polyhedral_summand_endpoint_lifts.
PR #310 is OPEN/DRAFT. There is NO complete passing packet audit, Prove2Me
registration/submission ID, ACCEPTED verdict, live Proved, verified-packet
artifact or publication receipt. Do not call this packet accepted.

Latest command5738598809 was a real new top-level publication comment, read back.
Acknowledgement5738600111 resolved proof
2eeb484b1a82b821726be5e6f69d72b46e859c4d and run35415626388.
Gate105823612311 succeeded; verify105823631876 failed with exit1 at line537;
publish105823792853 and report-verify105823793024 were skipped. The run is
completed/failure. This was the FIRST actual Lean compilation and the second
comment-triggered attempt, after the packaging failure below. No third trigger.

The three substantive helpers active_score_unique, compact_extreme_maximizer
and lift_vertex printed only propext, Classical.choice and Quot.sound.
transfer_all_pairs and the public solution printed sorryAx from failed
elaboration. These are not successful whole-packet audit reports. The actual
endpoint-lift helper is checked within the failed driver, but no separate
platform publication or independently successful packet is claimed.

## One precise compiler obligation and separate proposal

Only body_convex reports an error: its final nlinarith does not combine
s*A_i(x)<=s*b_i and t*A_i(y)<=t*b_i with s+t=1. The saved proposal replaces that
last tactic by add_le_add and the explicit identity
s*b_i+t*b_i=(s+t)*b_i=b_i. It does not change the statement or assume convexity.
The complete public root and all later code remain unchanged.

The proposal is UNAPPLIED to the publication source and UNCOMPILED. It applies
and reverses byte-for-byte in a clean Git workspace. Proposed603-line source:
blob4235c1e90effe3546d3ad6595032b093ef00028b,
SHA2569c742306ff5c2bfd16bbf64e74d224450f19bf69f3d1d634415a37ccdcf58687.
Further errors may appear after this repair. The complete diagnostic/context/
axiom block is preserved in compiler-diagnostics.txt; runner setup/cache/cleanup
were read but are not mislabelled as part of that committed excerpt.

The tested601-line/27768-byte source stays unchanged at blob
44a53a9bb9d56f15a9ecb83abe4e30cfe9da9277,
SHA256ef4727c6a4270b6ebf209011e8af7c86de4437c0ed1f2a282cb5faf0b073e1fc.
Local Lean/Lake and compiler-host DNS were unavailable. Static equality and
finite regression are not Lean compilation. The next prerequisite is full
pinned compilation/auditing of the proposed repair, with a fresh duplicate check
before any normal comment submission. No speculative hosted edit loop.

## Earlier packaging failure, not a failed Lean proof

Initial command5738554540 and acknowledgement5738555355 resolved proof
92d2358a70e24fafaa683961dc7a11a88da87694 in run35415267769. It exited2 BEFORE
invoking Lean because the raw FORBIDDEN expression matched the English word
'admit' in a documentation sentence. No proof admission was used. The guard was
not relaxed: the sole net source change was that comment word to 'provide'.
All declarations/proof terms, assumptions, public root and metadata remained
unchanged. A missing-space transcription in an intermediate upload was caught
by exact diff and restored before any new gate; no run used that bad version.
The original source and raw request remain preserved separately.

Both request archives were downloaded and their hashes recomputed:
10574789331,319bytes,b9a022a3beae42ad5e740de3bc3d0a3bc7332076230b2f4528120c172a199586;
10575174553,317bytes,a1579a9a6f3dfaf604c1a8986a3b87068c281b1cb3b1cad9bb9363965db06221.
No verified or publication archive exists from either run. Derived failure
records are separate from raw requests and the explicitly scoped diagnostics.

## Mathematical interface and actual hypotheses

P is ANY finite original H-polyhedron {x:A_i(x)<=b_i}; Q is nonempty compact
convex. At every actual extreme u of P the active-row kernel is trivial by a
symmetric finite-slack perturbation. Summing all active original rows gives a
linear functional uniquely maximized at u, without a supplied rank, basis or
supporting objective. A compact maximizing face in Q has an extreme point q;
exposed-face extremality makes q extreme in Q. Any convex decomposition of u+q
must maximize the objective in its P components, forcing both to be u, then
reducing to an extreme-point decomposition of q. Thus u+q is a compatible
actual sum vertex. This argument handles tied maxima and nonpolytopal Q.

The intended final assembly lifts arbitrary requested u,v independently, applies
an ASSUMED actual all-pairs exposed-edge bound B in P+Q, then uses accepted #309's
unique decomposition and contraction to recover a route from precisely u to v
in P, of length at most B. The whole accepted343-line namespace prefix is copied
byte-for-byte; its old public root/prints are omitted. The accepted finite-margin
helper is reused from the moment chain. No accepted target is resubmitted.

P need not be bounded, full-dimensional, simple or irredundantly represented.
Q need not be polytopal. Compactness/nonemptiness of Q and the all-pairs sum-route
bound remain explicit; this does not construct a short completion or bound its
original-row complexity. Arbitrary q need not work, and an interior point of a
maximizing face may fail to lift. Empty/noncompact Q cannot simply be substituted.
This is not unrestricted Polynomial Hirsch, shortestness, a projection theorem
or a claim of historical novelty. Classical contraction is credited in the packet.

## Supporting tests and reproduction

The new script and unchanged #309 helper run in a clean two-script workspace.
Twenty-five finite H models include scaled/redundant rows,114 compatible lifts,
566 independent endpoint pairs and3033 support comparisons.1186 sum steps become
741 factor edges after445 stationary steps are removed. Five tied maximizing
faces are included. Four unbounded/lower-dimensional lifts and12 selected box
examples through dimension64 are separate checks, not full high-dimensional
graph enumeration. Nineteen saved records pass with construction disabled;
five forged records fail. These tests do not verify an arbitrary H parser.

Complete report12100bytes SHA256
f0deb1fb5d00e4acc5f2612ff8ffa15485843abfc4769b92a56f76b6bc35c810;
fixture22185bytes SHA256
d83747025439cedb4ae48843292747ab102c47716e53e490743a7459c56ad61f.
They reproduce byte-for-byte. Test source blobf0b4bf5c1e1305cbe12029cb94bd97fa7d09a7bc,
SHA2561f23b1f0a87edee8c29b2a17e00489bd34479ccc8ee4175d978749d5450ae371.
Full reports/fixtures and the original archives accompany the bundle; committed
summaries are labelled, not substituted for raw fixtures.

    python3 scripts/test_polyhedral_summand_lifts.py --out /tmp/summand-lifts

Existing main files, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5 guard, workflows, actor
allowlist, duplicate safeguards and trusted verify/publish credential isolation
are unchanged. Consult live PR metadata for the later evidence commit; it is
not the same as the frozen failed proof SHA.
