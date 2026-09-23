# PR #339: radial polygon original routes — first gate failed

Read the five project instructions and LIVE heads/comments before resuming.
Continue this same PR/target; do not republish accepted #338 or take the separate
changing-numerator claim5786607495, #326, #282 or reserved #210.

Branch: proof/radial-polygon-original-routes.
Packet: research/publication_packets/radial_polygon_routes.
Target: Hirsch.actual_planar_vertices_rank_attaining_original_routes.
Tested proof:14f50c6a2ffb47fdce165753a889feb083800004.
Main at gate:e4cb622be8e1cd4f5fd10253669465460c57b735.
Source:940 lines/39495 bytes, blob3ed33059e0c0611b61d2f809e796bc8094184503,
SHA25696b4c2fb43fc03b3143c8155e4bb1771e11675167e09557ba4602443e9576226.

## Outcome and precise next action

Request5802759818, acknowledgement5802762849, run35918994272.
Gate107377791629 success; verifier107377867035 failed driver compilation.
Separate solution/statement not reached. Publish107378455630 and
report-verify107378454193 skipped. One attempt; no registration, proof submission,
IDs, acceptance or authenticated Proved. The exact inherited rank, new radial mass
and new secant-edge reports are standard-only; the full public root is not.

Apply the saved FOUR-SITE proposal at first-attempt/proposed-local-repair.patch:
1. Add one_mul to normalized_interpolation's final simplification (line405).
2. Replace strict_chord's failed mul_lt_mul_left step and auxiliary product
   identity with apply (div_lt_iff₀ hx).2, leaving the final nlinarith (line430).
3. Add local f,w to the ray_edge identity simplification (line687).
4. Explicitly change Fin zero's lower-bound goal to (0:Nat)<=i.val and use
   Nat.zero_le (line834).

The line431 no-goals error is the second site's cascade. The proposal is NOT
applied to repository publication inputs and has NOT been compiled. It yields
937 lines/39437 bytes, computed blob303dc7e6d2239690dcebde0600acf537124a0363,
SHA2561a850ee30cfc49facfb0d9b82acd5659a692c5bd272c3d28a66ed56e320c88f2.
Every declaration type, accepted prefix, public hypothesis, metadata file and
explanation is unchanged. Patch apply/reverse passed, not compilation. Further
errors may appear. Recheck live ownership/pending state, apply exactly, compile
locally where available, and request one complete prepared gate on this same PR.
No second trigger was posted in the initial continuation.

## What this adds and what remains

The proposed proof derives strict chart convexity from ACTUAL original vertex
extremality, transports lower secants/extreme rays to whole original exposed
segments and constructs finite original-edge walks attaining #338's exact rank.
It retains complete finite-hull vertex data, chosen strict target h, independent
e coordinate and increasing normalized order. It does not assume strict chart
convexity, supplied edges, a neighbor graph or a short route. L=min(k,n-k)+1
and2L<=n+2 count original vertices, not facets. The theorem is planar, not a
uniform arbitrary-dimensional Polynomial Hirsch result. Chart selection/H-to-V,
formal facet counts and arbitrary-walk shortestness are not conclusions.

## Durable records and reproduction

Current packet note:first-gate-evidence.md. Exact copied failed inputs, resolved
request, full displayed diagnostic/all seven reports, proposal and derived
readback are under research/verification/radial-polygon-routes/first-attempt/.
Source integrity, test summary and replay records are labelled as non-Lean.
The complete original request ZIP and four test output files are in the export.
No unavailable verified or publisher artifact was reconstructed.

New test:scripts/test_radial_polygon_geometry.py. Two existing dependencies:
scripts/test_inverse_rank_reduction.py and scripts/inverse_rank_planar.py.

    python3 scripts/test_radial_polygon_geometry.py --out /tmp/radial-small
    python3 scripts/test_radial_polygon_geometry.py --large --out /tmp/radial-large

Twelve planar models,118 charts,19012 triples,750 exposed segments,632 routes,
1896 edge occurrences and10 rejected controls. Large means32 vertices/four targets,
not32 dimensions. Clean three-script replay reproduces all four complete outputs.
The singleton-chart formal case is not in these executable fixtures. Python and
JSON are not kernel-verified. No old blocked supporting script is needed.

No local Lean/Lake/cache was found; toolchain DNS failed. Preserve the actual
Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f pin, strict0.10.8,
accepted source bytes and verifier/publisher isolation. No new proof repair or
publisher workaround may weaken these boundaries.
