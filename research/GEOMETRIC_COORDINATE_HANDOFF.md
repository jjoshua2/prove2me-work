# PR #322: geometric coordinate original-edge routes

## Current state: first full compiler attempt failed; keep OPEN/DRAFT

Repository: jjoshua2/prove2me-work.
Branch: proof/geometric-coordinate-original-routes.
Target: Hirsch.finite_hull_original_coordinate_routes.
Packet: research/publication_packets/geometric_coordinate_routes.
Tested proof: fe90bf7fae251e8ea8670bff0ad4c362d645ec92.
Base / trusted publisher main: 3ee00edc5a9d5e2a22e5c0971f7f0c5b5f2eeeff.

Actual NEW top-level publication comment 5767819039 was posted and read back.
Bot acknowledgement 5767821145 resolved the exact tested proof to run 35657778026.
Gate 106525550822 succeeded; verifier 106525605176 failed driver compilation
with exit 1. Separate solution and statement compilation were not reached.
Publish 106526033174 and report-verify 106526032699 were skipped.
No complete packet audit, verified archive, platform registration, submission,
theorem/submission ID, ACCEPTED verdict or Proved readback was produced.
No independent platform/root poll occurred and no further trigger was posted.

Lean 4.30.0 was reported by the restored pinned environment. Mathlib remains
c5ea00351c28e24afc9f0f84379aa41082b1188f. Local Lean/Lake and toolchain DNS were
unavailable; source/Python checks are not compilation. Do not treat a helper
inside this failed driver as verification of the complete public theorem.

## What the new mathematics does

For any finite real hull P=conv(C) and actual extreme endpoints u,v, the complete
written argument and Lean candidate construct original ordinary-edge routes of
length at most sum_j(K_j-1), where K_j counts ACTUAL vertex coordinate levels.
No neighbor relation, face catalogue, improving-edge witness, rank, connectivity,
simplicity or bounded path is assumed. C may contain redundant/interior points;
nonsimple/lower-dimensional hulls, dimension zero and equal endpoints remain.

The substantive geometric construction strictly exposes u, regularizes the
finite normalized displacement contrasts while preserving objective signs,
then takes a farthest maximum-ratio generator. The resulting whole exposed
support segment strictly improves the ORIGINAL objective. Filtering coordinate
extrema gives full retained faces; the actual vertex hull is derived by finite
Krein--Milman. These discharge accepted #283's local graph/face assumptions.
Public edges are nondegenerate whole IsExtreme original segments. Local edges
are IsExposed in their retained face; a separate ambient IsExposed statement
is not asserted. The internal 0/1-hull corollary targets at most d edges for
arbitrary finite 0/1 point families, not only cubes.

The coordinate inventory can be exponential in original facets. This is not
Polynomial Hirsch, shortestness, a polynomial-time H-to-V algorithm, a globally
monotone route, or a nonrevisiting theorem. Classical coordinate bounds are
credited in GEOMETRIC_COORDINATE_ROUTES.md. No historical-priority claim.

## Four reported elaboration issues and saved proposal

Original source: 1000 lines / 43482 bytes.
Git blob: 9ada1c7febd018f80531df1c5755bae1626972e8.
SHA256: 236c70b717aeb0860250dcd2600b7e34f4d08e4384a8d1c039691f34b5e429f2.
All three packet blobs were read back and match local prepared bytes.

The actual compiler reports:
1. Line 709: convex_segment is passed the scalar as an explicit endpoint,
   causing AddCommMonoid Type synthesis failure. Proposed call: convex_segment u v.
2. Line 916: exact IsExtreme.rfl runs after rw already closed the goal. Remove it.
3. Line 929: rewriting V changes the dependent Fin(card V) type of c. Transport
   the image equality with a nondependent congrArg, then simplify image_image.
4. Line 959: the 0/1 calc parses subtraction after the sum. Parenthesize each
   card-minus-one term and use the existing vertices definition in that body.

The scoped transcript preserves the complete compiler warning/error/axiom block
with runner timestamps removed; it is not a byte-for-byte raw runner archive.
All five inherited finite-proof reports are standard-only. The NEW
hull_filter_exposed and vertex_hull reports also contain only propext,
Classical.choice and Quot.sound. improving_edge, original_routes, zero_one_routes
and solution contain sorryAx caused by the failed elaborations. No admission
was written in the source; these are NOT passing transitive proof audits.

The proposed-local-repair.patch is UNAPPLIED to the publication source and
UNCOMPILED. It produces 995 lines / 43268 bytes, blob
b0da419948aeced1815471e66dbe1f7ec7db8404, SHA256
250ab15136fee24d87a2b77312ecd51bd5cefb2f082b9a57f9771d266da4cfa2.
Forward and reverse patch application reproduce both entire files exactly.
All declaration signatures, hypotheses, complete public root AND its proof,
accepted finite dependency and metadata remain unchanged. Further errors may
appear after these repairs; the proposal is not a promise of successful compile.

## Evidence and executed supporting checks

Evidence directory: research/verification/geometric-coordinate-routes/.
It preserves the original tested source, scoped diagnostics, frozen resolved
request, derived failure/source/dependency/test/replay records and saved repair.
The only run artifact is request 10665062775: 313 bytes, SHA256
1ee3ea6e81fc354edf4491ed3b74d4b3ed5b1e1d01c5d4c16ab64af7701a3ae4.
It was downloaded and independently rehashed. No missing verified/publication
artifact or individual API response is invented.

The accepted #283 source is reused after ONLY renaming its old root/print.
All five dependency manifest-file hashes match the downloaded accepted archive.
Finite regularization and segment-endpoint bodies are unchanged accepted reuse.
No earlier public target was resubmitted.

Fourteen exact models give 79 generators,74 vertices,91 facets,146 reference
edges,424 faces,417 active-system candidates,37 nonsimple vertices and5 redundant
generators. All 2811 local improvement obligations pass. The 480 ordered endpoint
routes contain 690 edge occurrences versus 534 shortest-distance total;134
nonshortest outputs are retained. All 690 saved certificates replay with the
producer disabled;11 malformed controls fail. The constructor does not read the
reference edge table, but does use exhaustively derived supporting rows.

Both scripts and the full report are preserved; the full 331977-byte fixture
accompanies the export and regenerates. A clean two-script replay reproduces
both complete report and fixture byte for byte. These are supporting exact tests,
not Lean-extracted software or a verified JSON parser. No large graph run is claimed.

## Next action and ownership

Resume THIS PR and saved repair, not a renamed or overlapping theorem. First
read all project instructions and live heads/comments/ownership. Apply/review
these four proof-body repairs, compile locally if available, then run a complete
pinned gate with transitive audit before any publication. Keep the target,
metadata, accepted dependency code, pins and trusted security split unchanged.
Do not repeat speculative hosted compiler edits or bypass a blocked action.

Coordination on accepted #283 was comment 5767607284, posted and read back.
#320 is already ACCEPTED/merged and must not be resubmitted. #282's positive
triangular routes, reserved #210 and all other owned work remain untouched.
Strict 0.10.7 compatibility, workflows, allowlist and secret-free verifier /
trusted publisher isolation are unchanged. The next mission-level mathematical
gap is adaptive original-row/level control; the finite level-dependent bound
must not be relabelled a universal original-facet polynomial result.
