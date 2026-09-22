# Accepted: quadratic original-edge routes with three exceptional target rows

## Exact result and publication identity

Target: Hirsch.three_exception_quadratic_original_routes.
Theorem ID: c31f1378-cca6-46b6-8bc5-c550b25df4f1.
Submission ID: 1dfac8b5-2a3d-42d5-9a66-f4380f08393d.
The unchanged raw publisher receipt records registration PUBLISHED, status
ACCEPTED and live_status Proved. Proved is the trusted publisher's authenticated
readback, not an independent platform or mission-root poll.

Frozen proof: ea943ccdbd57e076334521b0616277168da1f54b.
Trusted-main workflow: 0892d06f4944222ed327efb2d26f4c6796f4c171.
Coordination on #327: 5770302788. Actual new top-level publication request:
5770416937. Acknowledgement: 5770418190. Run: 35680108319.
Accepted verdict: 5770461916 at 2026-09-22T02:42:17Z. All were read back.

This is the FIRST complete hosted compiler attempt and FIRST platform submission
for this target. No post-gate proof or metadata repair was necessary or performed.
The complete source is 1430 lines / 62095 bytes, Git blob
1cebe264459e71e49b117d820d21af6e9885a0e1, SHA256
d6e5d4ff97961f82b6254bb2b3d490fad38caaf48097e2eb879cd34893754c34.
Its first1218 lines/51946 bytes are byte-identical to accepted #327's namespace
prefix; only that older target's public root and old print requests are omitted.
No accepted target was resubmitted. The public solution type exactly matches
problem.json and the separate target statement.

## Mathematical progress and retained structural hypotheses

P equals BOTH conv(C), for finite real C in ambient dimension d, and the original
m linear halfspaces. u,v are actual extreme points. B contains at most THREE
original labels. Target-tight rows outside B take their boundary value and at
most one other value on all actual vertices; exceptional/non-target rows remain
unrestricted. The theorem constructs original ordinary-edge routes with

    L <= (m-d)+m*m.

Every visited point is an actual original vertex. Every consecutive segment is
whole, nondegenerate and IsExtreme in original P. Every acquired target row stays
tight, including exceptional rows. Residual steps may acquire no new target label.

The accepted good-row prefix costs at most m-d and derives remaining direction
dimension<=3. For a nonzero original row restriction, its kernel inside that
space has dimension<=2. An explicit nested-subtype linear injection transports
the ambient equality-slice direction space into this kernel. Accepted planar
incidence geometry then bounds each such row slice by m+1 actual vertices,
without assuming the false two-vertices-per-slice cap in dimension three.

Each spatial residual vertex has at least three nonzero original active-row
incidences. Double-counting yields 3|V|<=m(m+1), and the low-dimensional cases
combine to |V|<=m*m+1. A genuine locked strict-ascent route has length+1<=|V|.
Append it to the actual entry prefix. No graph, selected basis, residual rank,
small catalogue, incidence count or cheap residual route is a public premise.

Exact H/hull equality and the outside-B two-level condition remain structural
assumptions. Redundant rows/generators, nonsimple/lower-dimensional hulls, empty
or non-target exceptions, dimension zero and equal endpoints remain covered.
m counts displayed original inequalities. No separate facet-lattice theorem,
shortestness, all-facet nonrevisiting, global monotonicity, ambient exposure or
efficient H-to-V computation is asserted. #327/#324 remain sharper for <=2/<=1
exceptions. This improves #325's cubic specialization but is neither a best
classical 3D diameter claim nor unrestricted Polynomial Hirsch. Repeated slicing
in larger dimensions still raises the exponent; that is not a uniform solution.

## Complete compiler and axiom evidence

Gate106595045294, verifier106595079597 and publisher106595322519 succeeded;
report-verify106595323238 was skipped. Complete driver.lean, standalone
solution.lean and separate statement.lean each compiled with exit zero. All
SEVEN named proof reports in EACH full proof log contain only propext,
Classical.choice and Quot.sound. No sorryAx appears in the proof reports.
The separate statement-only placeholder warning is not proof evidence.

Lean4.30.0 was observed in the hosted pinned environment; Mathlib remains
c5ea00351c28e24afc9f0f84379aa41082b1188f. Local lean/lake/elan and checked caches
were unavailable, with failed release/raw-host DNS lookup. Local source and exact
computations were not represented as Lean compilation. Strict0.10.7 publication,
all duplicate safeguards and verifier/publisher credential isolation are unchanged.

## Durable artifacts and executed exact tests

All three original ZIP digests and all five frozen input hashes were recomputed:
request10674477095,315 bytes,SHA2569de62208042933643d9d2dd77ba2a5ed3fa9303651a16d0ed9dea90369c38a4a;
verified10675186346,38507 bytes,SHA256103f507b38cd1f9106e6f22ff8b11e27e5a08eda3f8c4d647de65f1f7c1ae271;
receipts10674451653,920 bytes,SHA2568e584c8cdb20070f41d4b63b265315a85a806a42d21b0e22fda1aef8b9bc2de1.
All twelve unmodified verified files, both publisher files, exact request, source
checks, test/replay summaries and derived run/integrity records are preserved in
research/verification/three-exception-quadratic-routes/. Raw verified tree
72df22aedb4f9bbbee87f144920b77432ca452c2 and receipt tree
96e6ba20f5842b8d3ec8eedf449ba7cc5aa2b107 match independent local Git hashing.
Full decoded verifier/publisher logs were read through cleanup; only a scoped
exact excerpt is committed. Complete compiler logs are preserved unchanged.
Individual API response bodies were not returned and are not invented.

The23-hull suite passed271 certificates and2411 routes with3810 original-edge
occurrences, against3736 total shortest edges. All42 nonshortest routes and124
nonacquiring steps remain. There are150 qualifying targets, including16 targets
intrinsically requiring three exceptions,13 rejected targets and542 nonzero
row slices with more than two residual vertices. Eleven malformed controls fail.
Serialized records replay with certificate/route/edge construction disabled.

A clean FOUR-script workspace reproduces the complete report12349 bytes,
fixture6256810 bytes and control output794 bytes, byte-for-byte. The new script
is committed; all three full outputs and raw ZIPs accompany the downloadable
bundle and regenerate. The committed test summaries are explicitly derived,
not mislabeled as the entire fixture. These tests do not verify Python/JSON,
enumerate large graphs or establish the all-real result by sampling.

The export-only inspector passes28 frozen-evidence consistency checks and rejects
six corruptions. It does not run Lean, authenticate arbitrary JSON or contact the
platform. Its output is stored separately; its script is in review/check_packet.py
in the bundle, not claimed as an uploaded repository executable.

Handoff: research/THREE_EXCEPTION_QUADRATIC_HANDOFF.md. Complete normal eligible
integration of this existing PR; do not resubmit its accepted target. #326,#282,
reserved #210 and other owned work remain untouched.
