# PR #315: ordered original zonotope walk — compiler repair required

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live exact
PR heads/comments before continuing. Baseline main:
971d9d672dabe6e147b8828fff31fadbda521af6. This is the unowned walk-assembly
obligation following accepted #313, not a duplicate sweep or general decomposition.
Coordination comment5745535621 on #313 was posted/read back. Other owned work
and reserved #210 are untouched.

## Authoritative current status

Target: Hirsch.zonotope_regular_objective_original_routes.
Packet: research/publication_packets/zonotope_regular_routes.
PR #315 is OPEN/DRAFT. No complete passing packet audit, platform registration,
submission ID, ACCEPTED verdict or live Proved result exists from this attempt.

Actual NEW top-level command5745607790 was read back. Bot5745608540 resolved
proof5f4ed856d772ad3872bf2e7295f042ba7993b312 and run35472065688.
Gate105974700123 succeeded; verify105974722350 failed driver compilation with
exit1. Publish105974877023 and report-verify105974877076 were skipped. The run
completed. Only one gate was triggered; no second request or post-failure proof
edit occurred. Local Lean/Lake was absent and compiler-host DNS unavailable.

The crossing_vertices_distinct helper emitted only propext, Classical.choice
and Quot.sound. The other FOUR printed reports contain sorryAx from failed
elaboration. This is not a passed complete audit or independently published
helper. The scoped compiler excerpt and the original request ZIP are preserved;
the full runner log was inspected through cleanup but is not claimed committed.
There is no verified-packet or publication artifact to fabricate.

## Exact diagnosed sites and separate proposal

1. Line747: rw treated the local finite-set value S as a rewrite theorem.
   Replace the cardinal calculation with direct card_insert equalities.
2. Line826: the first rcases/rfl eliminated u/v before the second classification
   was invoked. Derive both classifications first and retain named equalities.
3. Lines973 and993: endpoint rewrites did not find evaluations inside unreduced
   lambda applications. Use explicit change at hepick before each rewrite.

The proposed repair changes only these four elaboration sites. It does not alter
any declaration signature, assumption, accepted prefix, public type or public
root proof. It is UNAPPLIED to the publication source and UNCOMPILED. The patch
applies/reverses byte-exact in a clean Git workspace. Further errors may surface
once these sites are repaired; do not claim that the proposal is Lean verified.
Proposed1072-line source blobdcfa6019d4c23b2d78fbfa96de0036357419ca71,
SHA2565a0a02ce8b00f58e121ab8372062d9765e7e405c6bab1b8a524abbd7b68627bf.

The exact tested1066-line/46746-byte source remains blob
9656a4308be4161ca9a61b6054136aae6cac30e7,
SHA2566179925b6505d5dd667a27177848508a0c59e72fd419f7e085a86d8a406b778f.
The complete699-line accepted #313 prefix is byte-identical; only its old root
and prints were omitted. All five dependency manifest hashes were rechecked
from its original verified archive. No accepted target was resubmitted.

## Mathematical argument and non-oracular construction

For Z=sum_i[0,w_i] and TWO supplied regular objectives f,g, accepted #313 derives
a same-sign target perturbation k and an exact finite event set T, |T|<=m.
Insert 0/1, enumerate increasingly, and prove no event lies between consecutive
entries. Midpoint chamber objectives are regular; their saturated points are
actual extreme points. Continuity and the intermediate value theorem fix signs
on every nonzero interval, identifying the first/last faces with f/g and placing
both adjoining chamber vertices in each event's WHOLE original edge face.

A crossed nonzero generator rules out equality of the two chamber points:
coefficient saturation for the first regular objective would force the second
representation to use the same pick on that generator, contradicting the affine
sign crossing. This lemma has the new standard-only report and requires no
injectivity of the redundant Boolean representation. Ambient extremality then
forces the distinct adjoining points to be the event segment's two endpoints.
One actual transition per event gives a Fin(|T|+1)-indexed original-edge walk.

No ordered schedule, adjacency, chamber vertex list or bounded path is assumed.
The written composition is complete, but the full Lean packet still requires
repair and successful verification. It includes zero/parallel/opposite/repeated
and rank-deficient generators, dimension zero and zero-event cases. Regular
endpoint objectives remain hypotheses. Constructing them for arbitrary requested
vertices and controlling generator count by ORIGINAL H facets remain separate.
No unrestricted Polynomial Hirsch result, shortestness, new best classical bound
or historical priority is claimed. Do not replace the generator budget by an
exponentially expanded list and call it an original-input polynomial bound.

## Evidence and reproduction

The original request artifact10593655183 is311bytes; SHA256
 d3b897757110bba56784f89833c0f91542a4d1c877ecbc0f9ef4fa60e12b35c4.
Its digest was recomputed and its raw resolved.json read back. The archive is
committed and exported. Raw evidence and derived status records are separate.

The unchanged new test script passed in a clean two-script workspace using the
accepted sweep constructor.84 small walks over42 systems give93 edges,177
visited vertices,30 parallel-tie events and18 zero generators.4324 Boolean
representations were examined for full small support faces, with5463 singleton
comparisons and299 event-face point checks. Four selected d8/16/32/64 routes
have lengths8/12/12/12, without complete large graph enumeration.22 saved records
pass with objective/route construction disabled; six forged inputs fail.

Full report1810bytes SHA256
101cc1cdeb7d4c41c31ef0c4656c2efc50f79cf6649019ce3c0e55f8c8785f77;
fixture77271bytes SHA256
65c11eda693b3a6af2bee2dac494f817a6e573afff1efd3e467ffc2ca027718f.
Both replay byte-for-byte. These are supporting finite checks, not Lean-extracted
code or verified arbitrary JSON. Full fixture and unchanged dependency accompany
the standalone bundle; the existing helper is not overwritten in this PR.

    python3 scripts/test_zonotope_regular_routes.py --out /tmp/zonotope-walk

All main proofs, root STATUS, Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.6 guard, workflows,
allowlist, duplicate controls and verify/publish credential separation are
unchanged. Consult live PR metadata for the later evidence head; it differs
from the frozen failed proof. Next step is full pinned verification of the saved
repair after a fresh duplicate/ownership check, not a new renamed theorem.
