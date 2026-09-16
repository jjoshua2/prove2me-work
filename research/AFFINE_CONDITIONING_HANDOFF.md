# PR #275: compiled metric obstruction; publication requires supported skill refresh

Read current STATUS, AGENTS, CLOUD_AGENT, SKILL, CONTINUE_HIRSCH and live PR
ownership before taking work. Baseline main338d1f9e1cc20df86998efa5f0dc6e92916329e8.
The exact new source/receipts are on `proof/affine-conditioning-barrier`.
Do not modify #210 or move #270's blocked companion through this branch.

## Exact successful compile and failed publication boundary

Packet: research/publication_packets/affine_pair_conditioning.
Public target: Hirsch.affine_pair_conditioning_optimum.
Proof SHA: ff9b0743f31b0db6adbcd078a2447180f0a8f7d4.
Actual new top-level trigger: #275 comment5691648630.
Resolved run:35052375246. Workflow-main338d1f9e1cc20df86998efa5f0dc6e92916329e8.

The unchanged81-line proof passed driver, solution and statement compilation
with exit0 on the FIRST gate. Three transitive axiom printouts contain only
propext, Classical.choice and Quot.sound. Artifact10429507451 was downloaded;
archive digest ae81fe723057ae61b2d140c3fbaced0e624db60b955e5fdf844cfb1f085248ae
and all five frozen file hashes were recomputed. Original audit, manifest,
driver, target statement and full compile logs are preserved in the packet.
The deliberate placeholder in statement.lean is not an admission in the proof.

Publication job104655680728 FAILED at the trusted platform skill-version check:
`Platform skill version changed; refresh the skill before publishing.`
The run produced no publication receipt or authenticated ACCEPTED/Proved
verdict. Do not invent a theorem/submission ID. No second trigger was posted,
no proof edit was needed and no verifier, guard, pin, workflow, actor allowlist
or secret split was changed. Keep this PR DRAFT with that blocker. The next
publication action requires the supported current skill/protocol refresh,
then checking for any existing registration before an authorized safe resume.
Do not merely overwrite the expected version or bypass the guard. This turn
has not performed a fresh authenticated root/leaf status poll.

## New mathematical conclusion and precise limits

For0<e<1, the two normal pairs(a,a+e*b) and(b,b+e*a) have minimum squared sine
at most e^2 for EVERY positive definite Gram matrix. The metricX=Y=1,Z=-e
attains it. The scalar target proves exactly that universal bound and attainment.

For0<e<=1/2, four such directions occur as genuinely adjacent facet normals
of the explicit simple bounded octagon in AFFINE_CONDITIONING_BARRIER.md.
Its diameter is4 despite best affine local/global delta EXACTLY e. Product
with a(d-2)-cube has2d+4 genuine facets,diameter d+2 and the same exact optimum.
All invertible affine maps, including dense mixing, are covered; this is not
failure of a finite chart search. Positive row scaling changes nothing.

A single shallow vertex truncation gives a non-Cartesian-product simple
polytope with2d+5 genuine facets,diameter at most d+3 and every affine local
delta still at most e. The new simplex facet and facet count certify nonproduct
for d>=3. This says nothing about Minkowski/projective indecomposability.
At d32,e=2^-160 the actual selected route has34 edges,SHORTEST by original
product projection,with69 genuine facets and no common endpoint facet. The
all-pairs upper bound35 is not a measured diameter.

The geometric realization/product/truncation theorems are written mathematics
with exact tests, NOT extra conclusions of the Lean scalar target. Small delta
is NOT a diameter lower bound. Other normal-cone width notions, projective
changes, different combinatorial realizations and route-local arguments remain
outside this obstruction. Dadush--Haehnle's sufficient angle-based results are
credited, not disproved or reimplemented. No historical-priority claim.

## Positive recognition and independent certificates

For rows with one or two nonzeros, positive diagonal balancing to signed roots
exists iff every magnitude gain cycle has product1. Exact propagation produces
scales and row weights, or an original-row closed walk of nonunit gain. The
consumer checks all products directly, without graph search or logs. Negative
cycles exclude ONLY positive diagonal scaling with those coordinate supports,
not dense affine possibilities. Positive certificates transport inequalities
and actual original edges and give access to #274's classical signed-root
coverage. The old unit-box executable is not asserted to accept all such charts.

## Executed evidence and source integrity

600 rational metrics/1200 independent vector-projection checks;5 exact attaining
metrics. Five complete product H graphs use699 active systems,72 vertices,112
edges; all700 pairs match independent shortest distances,2048 edge occurrences.
A separate coupled3D graph has18 vertices and checks its selected shortest path.
Large product/coupled routes in d16/32 and all their genuine-facet anchors pass.
Three dense affine re-encodings retain exact original-row path certificates.
256 gain cases match independent nullspaces:161 positive,95 negative. Recognized
32D simplex rows have diagonal scale ratio2^620 and a checked one-edge path.
18 malformed controls fail. Saved replay disables discovery/inversion/producers
and audits23 records,including150 original-edge occurrences.

A fresh THREE-source workspace reproduces all FIVE full reports and SIX
serialized fixture files BYTE-FOR-BYTE. No timing field is ignored. SymPy is
used only for the independent test reference. The consumer uses the unchanged
#271 original_route_exclusion.py and exact standard-library arithmetic. Its
full finite checks are not claimed as Lean-extracted JSON verification.

Two new tested source blobs: cb1dd140e8a220afa9d351c96ccec125df8829b7 and
9da333041f9414e1cd03de111fdf8d9551247c80, read back at
aa51344110767183405d8a38da9f7338cdcbbc1f. The frozen Lean solution blob remains
ea86f01d8eb6ca445d50c0e5725eda40c00b44ca. See source/replay manifests for SHA256.

    for s in metric geometry gain negative audit; do
      python3 scripts/test_affine_conditioning_certificates.py --stage "$s" \
        --out "/tmp/affine-$s.json" --fixtures /tmp/affine-conditioning-fixtures
    done

The downloadable bundle includes the original verified archive, five full
research reports and six complete fixtures. Larger fixtures are regenerated,
not silently replaced by metadata. Prior dependencies are bundled unchanged
but excluded from the new-file patch. Keep compilation, axiom audit, geometric
research, server acceptance and live Proved as distinct states.
