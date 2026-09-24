# First gate: complete actual-vertex hull verified; four local repairs remain

PR #340 is OPEN/DRAFT and unmerged. Target:
Hirsch.planar_original_halfspace_half_bound.
Tested proof f06b42d02ba51e1d3b712d8f245acae455494e73.
Source 1392 lines / 58551 bytes, blob a73661cea8141a2f934138e061fa432afbbedb3f,
SHA256 a2d412a073e87addb663d52d78897e8de9d2f3310bddc15216757be19b67a383.
No post-gate publication-source or metadata edits were made.

## Actual verification and publication boundary

New top-level request 5804972626 and acknowledgement 5804974991 resolve
run 35936462095 to that exact proof. Gate 107434487042 succeeded; verifier
107434542974 failed driver compilation with exit1. Standalone solution and
exact target statement were not reached. Publisher 107434853477 and
report-verify 107434853488 were skipped. One hosted attempt, zero registration
requests and zero actual proof submissions. No theorem/submission ID, verified
packet, publisher receipt, ACCEPTED verdict or authenticated Proved exists.

The new complete_vertices lemma and inherited RadialPolygon.original_routes
have standard-only transitive reports: propext, Classical.choice, Quot.sound.
The complete-vertex lemma derives ALL actual vertices from a possibly redundant
finite generator set and proves that their hull is the whole original body.
It is not a supplied vertex-catalogue premise.

vertex_bound, independent_coordinate, normalized_injective, sorted_enumeration,
half_bound and public solution retain failed-elaboration sorryAx. No admission
was written. The clean vertex-hull lemma does not verify the complete route bound.

## Six diagnostics, four local proof sites

1134: the row-slice call needs the explicit hdim.le proof rather than an omega
block that did not recover the ambient dimension equality.
1196: generic ext introduced z as a Fin2 coordinate index, not a Point. Apply
LinearMap.ext explicitly, then introduce the point z. Two displayed errors arise.
1251: hne has function type x=y -> False, so field lookup hne.symm fails twice.
Use explicit Ne.symm hne at both occurrences.
1294: expose f(p i)<f(p j) with change before rewriting the coordinate values;
the original target still contained unreduced lambda applications.

The saved FOUR-SITE patch is UNAPPLIED to publication inputs and UNCOMPILED.
It adds five lines and removes three, yielding 1394 lines / 58613 bytes:
computed blob 7476b40e159e3cae9f346c6b116c40471f160e4c,
SHA256 47324761cc298df950d242cf4b884836e05a021cdecc7dc73f60fe1c7f8777a3.
Patch apply/check/reverse passes. All declaration statements, the complete public
root statement AND proof, accepted dependency prefix, metadata and explanation
remain unchanged. Further errors may appear. No second gate was triggered.

Patch: research/verification/planar-original-half-bound/first-attempt/
proposed-local-repair.patch. Resume this SAME target after live checks, using
local compilation where available and one prepared complete pinned gate.

## Written mathematical advance and precise limits

The complete argument derives an original exposed-edge route with 2L<=m from
exact conv(C)=the ORIGINAL m planar halfspaces and actual extreme endpoints.
Ambient-plane incidence counting gives |V|<=m: each actual vertex has at least
two nonzero active original rows; each nonzero row contains at most two vertices.
The complete actual-vertex hull, strict exposure, independent coordinate and
normalized sorting are derived before applying accepted #339's original walk.
Neither a favourable chart nor a short-route/rank/adjacency oracle is supplied.

Finite-hull/H equality, actual endpoints and AMBIENT DIMENSION TWO remain
explicit. C may contain redundant generators; rows may repeat, rescale or be
zero. Equal endpoints, segments and points are included. This is not a formal
arbitrary-dimensional Polynomial Hirsch, efficient H-to-V, irredundant-facet,
arbitrary-walk shortestness, path-injectivity or target-facet-locking theorem.
The displayed-row count is original input, not an expanded generator inventory.

## Executed checks and preserved evidence

The committed standalone Fraction script covers 15 planar models, 430 routes
and 1434 original-edge occurrences, including 64 equal-endpoint routes, segment
and point bodies, 103 redundant generators and 28 zero rows. Eleven malformed
or invalid-premise controls fail. A clean single-script replay reproduces all
FOUR complete report/fixture files byte-for-byte. Python and JSON are not
kernel-verified; the larger case is 32 planar vertices/four targets, not 32D.

Only request artifact 10782913821 was produced: 313 bytes, SHA256
fd49dabb0ccac7317d8cf77bdeee39ca8a990492fc26d96e596aef754ad4c499.
Its original ZIP was downloaded and rehashed; exact resolved.json is preserved.
The complete decoded verifier log was read through cleanup. The stored error
transcript includes all six displayed errors and eight reports, but omits
linter warnings, timestamps and setup/cleanup; it is not a full raw runner archive.
Unavailable verified/publication artifacts and API responses are not invented.

The first detached source upload had a five-byte transcription omission. Hash
checking caught it before any commit, PR or gate, and excluded that blob. The
committed tested source matches the original prepared source and accepted prefix.
Local Lean/Lake/Elan and checked caches were absent; toolchain DNS failed. Source
checks and rational execution are not Lean compilation. Keep Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8 and all safeguards.
Handoff: research/PLANAR_ORIGINAL_HALF_BOUND_HANDOFF.md.
