# Original-route exclusion continuation

## Contribution and exact scope

PR #271, branch `research/original-route-exclusions`, starts from
`dbfd755ef4b6b2eb272c0cb70f888bf78741b5ec`. Read current STATUS and live PRs again
before changing anything. Coordination comment5690683673 on #268 was posted
and read back. This work does not change #268's encoding or claim its UNSAT
trace is certified. It independently establishes the route exclusion.

The four source files provide complete local tangent-star witnesses, finite
closure/depth exclusion, explicit original-row reentry memory, and transport
over an ENTIRE positive real affine parameter ray. A consumer never invokes
SMT, BFS, inversion, elimination or the producer's star search. Every active
(d-1)-subset is checked, so neighbor completeness is a conclusion. Geometry
retains nonsimple vertices, redundant rows, lower-dimensional H descriptions
and unbounded edge rays. A ray is not an edge to a fictitious vertex at infinity.

A certificate excluding paths of length<=L is separate from a zero-reentry
certificate of UNLIMITED length. Row reentries are genuine facet reentries
only on genuine-facet descriptions. Exponentially large stars and state spaces
remain possible; the negative-certificate scheme is not a universal polynomial
length or running-time proof.

## Parameter-wide mathematical result

On the classical Klee--Walkup U_4 with source0 and target(1,1,8,8), a checked
finite closure excludes ANY nonrevisiting path. A separate5-edge path with one
reentry proves the minimum is one. This is classical geometry with a new
independent certificate, not a historical novelty claim.

For EVERY real C>18, intersecting U_4 with sum(x)<=C preserves every old finite
vertex and finite edge, yet permits a NONREVISITING5-edge path. No4-edge path
exists. The exact points/active sets and the proof are in
`ORIGINAL_ROUTE_EXCLUSION.md`. The uniform consumer checks coefficients and
signs, not interpolation at a few sampled parameters. All nine original facets
have uniform strict relative-interior anchors. The result is a control against
transferring forced reentry by a distant cap, not a bounded Hirsch counterexample
or an assertion about all caps. The product amplification is a written elementary
corollary; no large product-graph experiment was executed here.

## Executed evidence

The primary report contains43 positive and42 negative certificates, all85
replayed with all geometric/search producers disabled. Eight reference models
and32 endpoint pairs check length L and L-1;13 complete local stars match an
independent SymPy rank graph. The genuine Birkhoff4 diagonal control requires
495 active subsets in its single expanded star, with20 neighbors. Reuse of
that example is credited to #268.

Klee--Walkup is tested separately unbounded and at caps18.001,19,100,10^6.
The unbounded no-reentry certificate has17 states,14 stars,56 subset witnesses,
16 allowed and42 excluded-memory transitions,10 unbounded rays. The uniform
no-four-edge certificate has26 vertices,22 stars,88 subsets/transitions and1035
affine checks. The uniform five-edge positive has54 affine checks. Old finite
vertices are independently accounted for by all70 active bases:4 singular,
51 infeasible,15 finite vertices, maximum coordinate sum18.

Seventeen finite and six affine certificate mutations fail. Three explicit
resource caps give UNKNOWN, not an exclusion. Both uniform saved certificates
replay with coefficient proposal and all base producers disabled.

The FINAL four source blobs were read back. A missing CLI help description
in the initial engine transcription was reconciled in the local file; logical
certificate checks were unchanged, and the FINAL source reran completely. Both
full reports and all four fixtures are byte-identical in a separate clean
four-source workspace. No elapsed-time fields are ignored. Reference graph
tests use installed SymPy; the consumers use standard-library arithmetic only.

## Preserved files and reproduction

Committed research records:
- `ORIGINAL_ROUTE_EXCLUSION.md`: complete certificate soundness and cap argument.
- `ROUTE_EXCLUSION_CHECK.json`: explicitly DERIVED compact summary with raw hashes.
- `ROUTE_EXCLUSION_SOURCES.json`: exact source identities.
- `ROUTE_EXCLUSION_REPLAY.json`: clean reproduction and fixture hashes.

The full raw reports and all four serialized fixtures accompany the conversation
ZIP and regenerate from the scripts. The large85-certificate fixture is not
silently replaced by its compact summary. There is no Lean source, compiler
run, axiom audit, Actions verification, Prove2Me theorem/submission ID or live
root/leaf poll for this research-only contribution. Do not trigger a publication
workflow merely because the note is complete.

    python3 scripts/test_original_route_exclusion.py --out /tmp/tests.json --fixtures /tmp/exclusions
    python3 scripts/test_affine_route_exclusion.py --out /tmp/affine.json --fixtures /tmp/exclusions/affine
    python3 scripts/affine_route_exclusion.py /tmp/exclusions/affine/family.json /tmp/exclusions/affine/exclude_four.json --output /tmp/uniform-negative.json

## Next useful target

The direct-path line can now distinguish a failed solver search from an
independently checked exclusion, and compare restricted and unrestricted
families across a whole parameter range. A useful next theorem must control
actual ORIGINAL paths in bounded carriers or rule out a precise bounded
path-local hypothesis, not assume a polynomial budget is already sufficient.
There is still no universal polynomial upper bound proved by these tests.
#267's complete forward-stellar-size obstruction remains intact.

#270's previously blocked companion has NOT been retried, copied or integrated
through this branch. #264/#255/#250/#244/#238/#208 and reserved #210 remain
unchanged. No toolchain, workflow, credential, permission or publisher-isolation
change. Root STATUS was not replaced underneath another agent; this durable
handoff and PR description identify the new independent certificate interface.
