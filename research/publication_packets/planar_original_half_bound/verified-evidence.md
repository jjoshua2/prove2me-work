# Complete verification of the planar original-row half bound

This records the successful Lean stage. Consult publication-receipt.json and the
current handoff for the separately established platform verdict and PR lifecycle.

## Frozen identity and exact repair

Target: Hirsch.planar_original_halfspace_half_bound.
Packet: research/publication_packets/planar_original_half_bound.
Verified proof: 6c08becac3a895c2245b567670c4345af00f60af.
Source: 1394 lines / 58613 bytes.
Git blob: 7476b40e159e3cae9f346c6b116c40471f160e4c.
SHA256: 47324761cc298df950d242cf4b884836e05a021cdecc7dc73f60fe1c7f8777a3.
Main at gate: cc0d237ea750f6e3cbb63decc99d776a00f41f2b.

The exact saved four-site repair adds five lines and removes three: explicit
hdim.le, LinearMap.ext, Ne.symm, and the beta-reduced comparison before rewriting.
All declaration statements, the accepted dependency prefix, the entire public
root statement AND proof, problem.json and explanation.md are unchanged. The
first failed source/run35936462095 remains preserved in first-attempt/. No proof
or metadata change followed this successful verification.

## Actual complete compiler result

Request5805457316 and acknowledgement5805461985 bind run35940253176 to the exact
proof above. Gate107446368967 and verify107446479011 succeeded. Driver, standalone
solution and separate exact target statement each exited zero. All EIGHT reports
in BOTH complete proof logs contain only propext, Classical.choice and Quot.sound:
original_routes, vertex_bound, complete_vertices, independent_coordinate,
normalized_injective, sorted_enumeration, half_bound and public solution.
No sorryAx remains. The separate target-statement placeholder is not proof evidence.
Linter warnings are preserved unchanged, not hidden by source edits.

This is the second hosted compiler attempt. Local Lean/Lake/Elan and checked
installation/cache paths were absent; release/raw toolchain hosts failed DNS.
The actual compilation is the hosted Lean4.30.0/Mathlib
c5ea00351c28e24afc9f0f84379aa41082b1188f run. Strict protocol0.10.8 and the
secret-free verifier/trusted-publisher separation are unchanged. Patch checks,
Python execution and offline evidence inspection are not Lean compilation.

## What the theorem proves

Given finite real planar C, m original linear inequalities, exact whole-set
conv(C)={x : all original inequalities hold}, and actual extreme endpoints u,v,
the theorem constructs a finite original-vertex route with 2L<=m. Each step is a
whole nondegenerate IsExposed segment of the ORIGINAL feasible body.

It derives the entire actual vertex hull, strict target exposure, independent
second coordinate and sorted normalized chart. None is a public hypothesis.
Ambient-plane incidence counting gives |V|<=m: each actual vertex has at least
two nonzero active original rows and each nonzero row contains at most two actual
vertices. Accepted original-edge geometry then constructs a route with
2L<=|V|<=m. Equal endpoints are handled by the length-zero sequence.

Redundant boundary/interior generators, repeated/rescaled/redundant/zero rows,
point and segment bodies remain included. The count is the ORIGINAL displayed
row count, not an expanded vertex inventory. Exact finite-hull/H equality,
actual endpoint extremality and ambient dimension TWO remain explicit. This is
not an arbitrary-dimensional Polynomial Hirsch result, efficient H-to-V theorem,
formal irredundant-facet count, shortestness, global path injectivity or a
separate target-facet-locking assertion.

## Reproduction and raw evidence

Both unchanged standalone rational suites reran in this continuation. All FOUR
complete report/fixture files reproduce their previous bytes. Across15 planar
models they retain430 routes/1434 original-edge occurrences,64 equal-endpoint
routes,103 redundant generators,28 zero rows and11 rejected controls. Segment
and point cases are included. Large means32 planar vertices/four targets/36 rows,
not32 dimensions. Python and JSON decoding are not kernel-verified.

The request archive10784354279 is313 bytes, SHA256
f3ff9d414692aafe1aa0f5b975e1d6adac320f5b3b24325fca5a8d4e2d03fdea.
The verified archive10784667103 is40547 bytes, SHA256
7f52f23f589d57e0ff7e3464e9e65f409580a4dec040a341631e6a844edd7a8e.
Both were downloaded/rehashed. All five frozen input hashes and all12 verified
members match. Full raw verified Git tree50075f5161e4c949c4816672f9d0738d7392f06f
and packet tree63b5500b9ae0353e4eb424a7c953306688c4f62e match independent local
Git hashing. Complete compiler logs are preserved byte-for-byte. The full decoded
verifier runner log was read through cleanup; a selected runner excerpt is not
misrepresented as a complete raw job archive.
