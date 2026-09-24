# PR #340: chart-free planar original-row half bound — first gate failed

Read the five project instructions and LIVE heads/comments before resuming.
Continue this SAME PR/target. Do not redo accepted #339 or the obsolete #320
assignment. Respect #326, #282, reserved #210 and changing-numerator ownership.

Branch: proof/planar-original-half-bound.
Packet: research/publication_packets/planar_original_half_bound.
Target: Hirsch.planar_original_halfspace_half_bound.
Tested proof: f06b42d02ba51e1d3b712d8f245acae455494e73.
Main at gate: cc0d237ea750f6e3cbb63decc99d776a00f41f2b.
Source: 1392 lines / 58551 bytes, blob a73661cea8141a2f934138e061fa432afbbedb3f,
SHA256 a2d412a073e87addb663d52d78897e8de9d2f3310bddc15216757be19b67a383.
Evidence-only commits do not replace this tested proof identity.

## Outcome

Request 5804972626; acknowledgement 5804974991; run 35936462095.
Gate107434487042 succeeded. Verify107434542974 failed driver compilation, exit1.
Standalone solution/statement not reached; publish107434853477 and
report-verify107434853488 skipped. One hosted attempt; zero registration requests
or proof submissions, no IDs/receipt/ACCEPTED/Proved. No second gate was posted.

Inherited original_routes and new complete_vertices have standard-only reports.
All six other reports, including public solution, retain failed-elaboration
sorryAx. No admission was written. Complete vertex-hull recovery is verified;
the entire original-row route theorem is not.

## Exact next repair

Saved patch: research/verification/planar-original-half-bound/first-attempt/
proposed-local-repair.patch. Four sites, five additions/three deletions:

1. At1134 pass hdim.le explicitly to PlanarResidual.row_slice_card.
2. At1194 replace ext z with apply LinearMap.ext; intro z, retaining z as a point.
   The two displayed errors refer to its applications at1196.
3. At1251 replace both hne.symm occurrences with (Ne.symm hne).
4. At1294 insert change f (p i) < f (p j) before rewriting hfval.

Proposal is UNAPPLIED to the publication source and UNCOMPILED. It yields
1394 lines / 58613 bytes, computed blob7476b40e159e3cae9f346c6b116c40471f160e4c,
SHA25647324761cc298df950d242cf4b884836e05a021cdecc7dc73f60fe1c7f8777a3.
Apply/check/reverse passes. All declaration statements, accepted1095-line prefix,
complete public root (statement and proof), metadata and explanation are unchanged.
Further errors may appear. Recheck live ownership/pending requests, apply exactly,
compile locally where possible, and use one prepared complete gate on this PR.
Never rename the theorem or weaken assumptions to get a passing compilation.

## What this closes and what it does not

The proposed theorem uses only exact conv(C)=the original m planar inequalities
and actual extreme endpoints. It derives actual vertex completeness, exposure,
independent coordinate, normalized injectivity and sorted chart. Ambient-plane
incidence counting gives |V|<=m, and accepted #339 yields an original exposed-edge
route with 2L<=m. Original rows, not a supplied expanded vertex inventory, govern
this bound. Redundant generators/rows, zero rows, points, segments and equal
endpoints remain included. The result is planar, not the arbitrary-dimensional
mission. Exact finite-hull/H equality and endpoint extremality remain explicit.
No formal shortestness, efficient H-to-V, facet-lattice or locking claim is made.

## Reproduction and evidence

    python3 scripts/test_planar_original_input.py --out /tmp/planar-small
    python3 scripts/test_planar_original_input.py --large --out /tmp/planar-large

One standard-library script; 15 planar models,430 routes/1434 edge occurrences,
64 equal endpoints,103 redundant generators,28 zero rows and11 rejected controls.
Both complete report/fixture pairs repeated byte-for-byte in a clean workspace.
Python/JSON are not kernel-verified. Large means32 planar vertices/four targets.

Packet first-gate-evidence.md and first-attempt/ preserve exact failed inputs,
all displayed errors/eight reports, exact resolved request and derived readback.
Only request artifact10782913821 exists:313 bytes,SHA256
fd49dabb0ccac7317d8cf77bdeee39ca8a990492fc26d96e596aef754ad4c499.
The export contains that original ZIP, full test outputs and full uncompiled
proposal. Extracted diagnostics omit linter/setup/timestamp material; they are
not the whole raw runner log, which was read through cleanup.

Keep Lean4.30.0/Mathlibc5ea00351c28e24afc9f0f84379aa41082b1188f, strict0.10.8,
accepted proof bytes, duplicate guards and secret-free verifier/trusted-publisher
separation. Local compiler/cache was absent and toolchain-host DNS failed; those
facts do not authorize changing the environment or bypassing a blocked action.
