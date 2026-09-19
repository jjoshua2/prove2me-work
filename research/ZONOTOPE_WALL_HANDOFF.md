# PR #312: original zonotope-edge criterion — two proof sites remain

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live exact
heads/comments/receipts before continuing. This turn began at main
7ed199c915cd97afd65008f7ba60e171e28a39cb. #311 is ACCEPTED/Proved and was not
resubmitted. The distinct whole-edge criterion was coordinated in #311 comment
5742480623, posted/read back. Other owned work and reserved #210 stayed untouched.

## Actual status: OPEN/DRAFT, not accepted

Target: Hirsch.zonotope_exposed_edge_iff_tied_collinear.
Packet: research/publication_packets/zonotope_exposed_edge_criterion.
Branch: proof/zonotope-exposed-edge-criterion.
Frozen proof:6599be3895c7ab7fbe9e448625fb558e24139a31.
NEW top-level command5742568565 was posted/read back; bot5742569989 resolved
that exact proof and run35448186683. Gate105910664069 succeeded;
verify105910693688 failed driver compilation with exit1; publish105910817042
and report-verify105910816872 were skipped. Last observed run:completed/failure.
No complete passing audit, verified packet, platform theorem/submission ID,
ACCEPTED verdict or live Proved was produced. Exactly ONE gate; no retry.

The requested reports for point_eq_cap_iff, segment_forces_line and
endpoints_extreme contain only propext, Classical.choice and Quot.sound.
line_face and public solution contain sorryAx from failed elaboration. Three
standard-only reports are not a complete packet audit or separate acceptance.

The tested447-line/18046-byte source remains unchanged:
blobdff8ec1cf4d2b9230d321bccf53cf42bd9f3dbba,
SHA256a849a1874713ac0396c7ac99f381f00794792e6fe3d01548cfa27b30f91e0618.
Both metadata files are unchanged after the gate. Local Lean/Lake was absent
and compiler-host DNS failed. Text equality and exact Python tests are not
Lean verification. No second trigger or post-gate publication-source edit.

## Two actual diagnostics and a separate proposal

At line198, scalar_bounds contains a layout-sensitive multiline `by simpa ...
using` inside a pair term; the parser expects the closing bracket and leaves
an underdetermined multiplication instance. The proposal splits the two
conjuncts and uses an explicit typed inequality followed by one_mul.

At line248, line_face's mass nonnegativity subproof calls split_ifs while its
goal still contains the lambda application
0 <= (fun i => if f(w_i)=0 then |c_i| else0) i.
The proposal explicitly changes that expression to the displayed if-expression
before splitting, then proves each branch directly.

The proposed-local-repair.patch is UNAPPLIED to the publication file and
UNCOMPILED. It changes only those proof bodies, preserving all definitions,
statements, assumptions, public root statement AND proof and metadata. It
applies/reverses byte-exact in an isolated Git workspace. Proposed454-line file:
blobfdae9555c66329742f641c259e551f03edad132d,
SHA256cdf116eed7169dd2e8ea0cd53c58154393689e8c052c4fa6301c1682ddd9aad5.
Further errors may emerge after the repair. Do not label it verified or run
another speculative edit/compile cycle. Full pinned compilation and a fresh
live duplicate check are prerequisites before another normal comment submission.

## Mathematical interface and scope

The intended root is an IFF for arbitrary generator families and linear f.
The whole maximizing face of Z=sum_i[0,w_i] is a nondegenerate original exposed
segment with actual extreme endpoints exactly when all tied generators are
collinear and at least one is nonzero. The proof derives support saturation for
EVERY representation. It constructs endpoint coefficients and positive total
width for sufficiency, and toggles each tied generator inside the actual face
for necessity. Repeated/opposite/zero directions, f0, m0, d0 and rank deficiency
are included. The collinearity condition is characterized, not assumed to hold
for every objective or mistaken for projected coefficient-cube adjacency.

Three supporting results have standard-only reports; the sufficiency direction
and complete iff still need repair. The whole geometry and exact endpoint proof
are not to be replaced by an edge-list assumption or weaker conditional target.
Two elementary segment-parameter/line-injectivity proof bodies follow accepted
#309. Classical support-face geometry is credited; no historical-priority claim.

No generic objective sweep, endpoint-objective construction, all-pairs route,
length bound, translated #311 composition, or original-H-row complexity bound
is supplied by this packet. Those remain separate genuine obligations. In
particular cube edges can project into the interior of Z. The accepted completion
and summand-transfer results are not resubmitted. No general Polynomial Hirsch
conclusion follows from this local criterion alone.

## Evidence and reproduction

The sole request archive10585546576,315bytes was downloaded and hash-checked:
b310dc760d33d14321635697d303e68186b267dcd9321a8aa23d64c8025c7f72.
Its raw resolved.json is preserved. The runner log was read through compiler
failure and cleanup; committed diagnostics are explicitly the selected exact
error/context/axiom block, not a fabricated full runner log. No unavailable
verified or publication artifact is invented. Tested source, raw request,
proposed patch and derived readbacks are separately labelled.

The197-line standalone Fraction script has Git blob
ba48c1514aa9cabc79c7dd8726c410db8cce6d0b, SHA256
5601084204fe011e5491ba309f341b5b6a6ffaf2f4fd8040a868ced0b0562d2f.
It checks66 small systems,987 objectives,37894 saturation statements,2961
fractional representations,236 edge faces and751 nonedges. Complete independent
planar hulls account for75 original edges. Five selected models through d64
are not full graph enumerations. Twenty-seven saved certificates pass with
construction/rank/hull discovery disabled; five forged records fail.

The complete report27430bytes and fixture36496bytes reproduce in a clean
script-only workspace with hashes
42ad193e6b3436487beed34b380ac5e5257af2c68dc8a044e9856bf8615c1386 and
8ddda93ad1deeb89da2d00ca7c773c2c1977f03090d26ec6283efb5e5693118b.
They are supporting tests, not Lean-extracted Python/JSON verification. Full
outputs, original ZIP and proposed source accompany the download and regenerate:

    python3 scripts/test_zonotope_wall.py --out /tmp/zonotope-wall

No pre-existing main file, root STATUS, other owned branch, #210, Lean4.30.0 /
Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.5 guard, workflow,
allowlist, duplicate safeguards or trusted credential split changed. Consult
live PR metadata for the later evidence head, distinct from the frozen proof.
