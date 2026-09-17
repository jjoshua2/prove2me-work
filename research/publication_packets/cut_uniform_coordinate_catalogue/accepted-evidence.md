# ACCEPTED: one uniform cut-vertex coordinate catalogue

The trusted publisher reports ACCEPTED and authenticated live Proved for
`Hirsch.cut_vertex_uniform_coordinate_catalogue`. Do not resubmit this theorem.

- Theorem: `f7bdc6f6-ecfb-4525-816e-7e66d0ae6ad3`.
- Submission: `9009a1fe-2e0b-4a91-956b-8a4ee322ba25`.
- Registration: PUBLISHED.
- Frozen proof: `91c5c7386a106c5cd73bea203cbb23f324036d8f`.
- Run: `35268179894`.
- Actual command: https://github.com/jjoshua2/prove2me-work/pull/297#issuecomment-5720437545
- Resolved-head reply: https://github.com/jjoshua2/prove2me-work/pull/297#issuecomment-5720439766
- Authenticated verdict: https://github.com/jjoshua2/prove2me-work/pull/297#issuecomment-5720480187
- Verdict time: September 17, 2026, 20:03:13 UTC (16:03:13 America/New_York).

## New formal result

For a generating set S in R^d, a finite joint cut-image cover Omega and a finite
scalar coordinate cover Lambda of all its generating points, the theorem
constructs ONE finite real set K containing every coordinate of EVERY extreme
point of convexHull(S) cut by m specified linear halfspaces. K is selected before
choosing the vertex or coordinate. The explicit bound is

    |K| <= 2^m * sum_(n=0..min(d+1,m+1)) |Omega|^n * |Lambda|^n.

No cut-vertex catalogue, support list, weights, active mask, rank, or output
membership assertion is a premise. The accepted positive-support theorem
selects a genuine support and uniquely recovers its real weights from all
active equations. The new finite code enumerates all masks, image tuples and
scalar tuples, decodes one scalar from each, and proves that every actual
coordinate is decoded. The proof does NOT require unrelated codes to be
consistent or uniquely soluble: they may produce extraneous values. Thus K is
a complete overcover, not a claimed exact list of attained levels.

The logical decoder uses classical choice. It is not a certified runtime solver,
a canonical catalogue or a proof of the Python implementation. The n=0 term
is harmless padding, and empty sets/zero dimension/no cuts are included.
For fixed m the bound is polynomial in the supplied catalogue sizes; it is
not uniformly polynomial in unrestricted m. Small input catalogues for arbitrary
carriers are not constructed or assumed to exist. No new edge path or universal
Polynomial Hirsch bound is asserted by this theorem.

## Actual first-attempt verification and dependency reuse

The unchanged 419-line source passed its FIRST pinned compilation/axiom gate
and FIRST platform submission. Driver, solution and target exits are all zero.
All SIX printed transitive declarations depend only on propext, Classical.choice
and Quot.sound. No repair commit, theorem weakening, target self-import or new
axiom was used. The separately compiled target stub intentionally ends in
by sorry; the submitted solution and audited root do not contain that admission.

The complete accepted #291 source was copied with only the public root and print
name changed to accepted_positive_support. Its live accepted receipt and five
original frozen hashes were checked; it was not submitted again. Current source
blob166eecc5909561c0db132e2741780b5c1099fb93, SHA256
5e2a8efb6f5f8d4767d4aa6a248f30d1bfc07576f0688c7a6d84138bbd640bd0.
The public target signature is exact. Local Lean/Lake was absent; the actual
compiler was the pinned hosted gate, not rational tests relabeled as Lean.

All THREE original archives were downloaded and independently hash-checked:

- request10518265078: 6e7cadcb7ed63bf442f1dafa073a1aaf4bc9119ed84698706d9a670c13f2d4a4;
- verification10517830775: 35ea46be0cdf6bf0408354c347608c7398b1dbd569ce5463e08a1483874ff2de;
- publication10517945908: dd9086f3873c32508a51c1bb12e29bb50972dd9ffb298771b1afc2f59e59a3ac.

All five frozen file hashes were recomputed. Source, problem.json and explanation
match the originally prepared bytes. Raw request, packet audit, manifests, compile
log and publication receipt are stored separately from derived readback and this
summary. No absent individual API response is invented. Post-gate integration
adds tests and evidence only; the accepted proof and target are unchanged.

## Distinct coordination and next mathematical obligation

The live #294 agent resumed the selected-square-row proof during the initial
queue inspection. That work and its publication command5720225598 were left
untouched. This separate direction was announced on #294 in comment5720255040.
Our proof does not assume the square-row result: it deliberately counts all
active masks using the earlier accepted #291 theorem.

The next useful composition can use the separately selected n-1 original active
rows to replace the all-mask count by a count of appropriate small row subsets,
and use cut-image covers projected to those rows rather than the entire joint
image. That would connect more directly to the written cut-level closure and
its few-column-type class bounds. It has not been formalized here. Even such
sharper counting must retain its true parameter dependence; neither large
support inventories nor global-coordinate obstructions disappear by notation.
Do not duplicate this accepted uniform-catalogue theorem or claim a general
polynomial bound from its finite but potentially exponential count.

## Separate supporting computation

The Fraction-only regression exhausts26397 scalar recipes and3636 linear systems
across seven inputs, including2766 consistent rank-deficient systems. Independent
original H-basis enumeration yields39 cut vertices from188 square systems; all98
coordinates and39 selected positive-support recoveries are checked against the
one catalogue for each input. Incomplete image covers and nonextreme points
provide adverse controls; empty recipes and zero dimension are also tested.

A fresh standalone workspace reproduced the entire3678-byte report and8210-byte
fixture byte-for-byte. These tests are not Lean-extracted and do not establish
parser correctness. Their identities and the prepared-source history are
preserved. No existing source, other owned branch, pin, protocol, workflow,
permission, duplicate safeguard or trusted credential separation was changed.

    python3 scripts/test_uniform_cut_catalogue.py
